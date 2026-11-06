"""Pure archive/digest/command-planning DATA; never install or start Lean."""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import ast
import re
import tarfile
import unittest
from unittest import mock
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SUPPORT = ROOT / ("ci" if (ROOT / "ci/portable_ci_data_v1.py").is_file() else "proposal")
SPEC = importlib.util.spec_from_file_location("portable_ci_data_v1", SUPPORT / "portable_ci_data_v1.py")
m = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(m)


def tar_data(name="elan-init", link=False, duplicate=False):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w:gz") as archive:
        for _ in range(2 if duplicate else 1):
            info = tarfile.TarInfo(name)
            body = b"INERT DATA: NEVER EXECUTE\n"
            if link:
                info.type = tarfile.SYMTYPE
                info.linkname = "elsewhere"
                archive.addfile(info)
            else:
                info.size = len(body)
                archive.addfile(info, io.BytesIO(body))
    return output.getvalue()


def zip_data(files, symlink=False):
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w") as archive:
        for name, body in files:
            info = zipfile.ZipInfo(name)
            if symlink:
                info.create_system = 3
                info.external_attr = (stat.S_IFLNK | 0o777) << 16
            archive.writestr(info, body)
    return output.getvalue()


def asset(data, windows=False):
    return {"name": "elan-x86_64-pc-windows-msvc.zip" if windows else "elan-x86_64-unknown-linux-gnu.tar.gz",
            "size": len(data), "digest": "sha256:" + hashlib.sha256(data).hexdigest()}


def source_archive(extra=None, changed=False):
    body = b"-- inert source fixture\n"
    inventory = {"schema": "conditional-separation-source-files-v1", "files": [
        {"path": "Example.lean", "bytes": len(body), "sha256": hashlib.sha256(body).hexdigest()}]}
    files = [("Example.lean", b"changed" if changed else body), ("PACKAGE_FILES.json", json.dumps(inventory).encode())]
    if extra:
        files += extra
    return zip_data(files)


class PortableDataTests(unittest.TestCase):
    def setUp(self):
        root = os.environ.get("CI_DATA_ROOT")
        if not root:
            self.fail("CI_DATA_ROOT must name private disposable DATA under the runner/author root")
        self.destination = Path(root) / self.id().split(".")[-1]

    def test_all_five_platform_assets(self):
        rows = m.load_assets(SUPPORT / "elan-v4.2.4.json")
        for system, machine, suffix in (("Linux", "x86_64", "x86_64-unknown-linux-gnu.tar.gz"),
                                        ("Linux", "aarch64", "aarch64-unknown-linux-gnu.tar.gz"),
                                        ("Darwin", "arm64", "aarch64-apple-darwin.tar.gz"),
                                        ("Darwin", "x86_64", "x86_64-apple-darwin.tar.gz"),
                                        ("Windows", "AMD64", "x86_64-pc-windows-msvc.zip")):
            self.assertEqual(m.asset_for(rows, system, machine)["name"], "elan-" + suffix)

    def test_unsupported_platforms_fail(self):
        for system, machine in (("Windows", "ARM64"), ("Linux", "riscv64"), ("FreeBSD", "amd64")):
            with self.assertRaises(ValueError):
                m.asset_for([], system, machine)

    def test_native_runner_labels(self):
        self.assertEqual(m.validate_runner("macos-15", "Darwin", "arm64", "arm64"), "aarch64")
        self.assertEqual(m.validate_runner("macos-15-intel", "Darwin", "x86_64", "x64"), "x86_64")

    def test_runner_arch_mismatch(self):
        for runner, system, machine, python_arch in (("macos-15", "Darwin", "x86_64", "x64"),
                                                     ("ubuntu-24.04", "Linux", "x86_64", "arm64"),
                                                     ("windows-2022", "Linux", "x86_64", "x64")):
            with self.assertRaises(ValueError):
                m.validate_runner(runner, system, machine, python_arch)

    def test_tar_installer_is_inert_data(self):
        data = tar_data()
        path = m.unpack_installer(data, asset(data), self.destination)
        self.assertEqual(path.read_bytes(), b"INERT DATA: NEVER EXECUTE\n")

    def test_zip_installer_is_inert_data(self):
        data = zip_data([("elan-init.exe", b"NOT A WINDOWS EXECUTABLE")])
        self.assertEqual(m.unpack_installer(data, asset(data, True), self.destination).name, "elan-init.exe")

    def test_digest_failure_writes_nothing(self):
        data = tar_data()
        with self.assertRaisesRegex(ValueError, "byte size"):
            m.unpack_installer(data + b"tamper", asset(data), self.destination)
        same_size_corruption = bytes([data[0] ^ 1]) + data[1:]
        with self.assertRaisesRegex(ValueError, "SHA256"):
            m.unpack_installer(same_size_corruption, asset(data), self.destination)
        self.assertFalse(self.destination.exists())

    def test_boolean_size_rejected(self):
        data = tar_data()
        with self.assertRaises(ValueError):
            m.unpack_installer(data, {**asset(data), "size": True}, self.destination)

    def test_tar_traversal_rejected(self):
        data = tar_data("../elan-init")
        with self.assertRaises(ValueError):
            m.unpack_installer(data, asset(data), self.destination)

    def test_tar_symlink_rejected(self):
        data = tar_data(link=True)
        with self.assertRaises(ValueError):
            m.unpack_installer(data, asset(data), self.destination)

    def test_tar_duplicates_rejected(self):
        data = tar_data(duplicate=True)
        with self.assertRaises(ValueError):
            m.unpack_installer(data, asset(data), self.destination)

    def test_unexpected_archive_member_rejected(self):
        data = tar_data("other-program")
        with self.assertRaises(ValueError):
            m.unpack_installer(data, asset(data), self.destination)

    def test_zip_symlink_rejected(self):
        data = zip_data([("elan-init.exe", b"target")], symlink=True)
        with self.assertRaises(ValueError):
            m.unpack_installer(data, asset(data, True), self.destination)

    def test_archive_malformed_rejected(self):
        data = b"not an archive"
        with self.assertRaises(ValueError):
            m.unpack_installer(data, asset(data), self.destination)

    def test_source_archive_exact_set(self):
        root = m.unpack_source(source_archive(), self.destination)
        self.assertEqual((root / "Example.lean").read_bytes(), b"-- inert source fixture\n")

    def test_source_missing_inventory(self):
        with self.assertRaises(ValueError):
            m.unpack_source(zip_data([("Example.lean", b"x")]), self.destination)

    def test_source_duplicate_or_traversal(self):
        for path in ("../outside", "C:/outside", "a\\outside", "Example.lean"):
            with self.assertRaises(ValueError):
                m.unpack_source(source_archive([(path, b"x")]), self.destination)

    def test_source_digest_mismatch(self):
        with self.assertRaises(ValueError):
            m.unpack_source(source_archive(changed=True), self.destination)

    def test_source_object_or_git_extra_rejected(self):
        for path in (".lake/build/Fake.olean", ".git/config", "reports/log.txt", "__pycache__/cache.pyc"):
            with self.assertRaises(ValueError):
                m.unpack_source(source_archive([(path, b"x")]), self.destination)

    def test_source_count_budget_exact_and_over_before_reads(self):
        data = source_archive()
        with mock.patch.object(m, 'SOURCE_MAX_MEMBERS', 2):
            self.assertEqual(len(m.source_payloads(data)), 2)
        with mock.patch.object(m, 'SOURCE_MAX_MEMBERS', 1), \
             mock.patch.object(m.zipfile.ZipFile, 'read', side_effect=AssertionError('unexpected decompression')) as read:
            with self.assertRaisesRegex(ValueError, 'member-count budget'):
                m.unpack_source(data, self.destination)
            read.assert_not_called()
        self.assertFalse(self.destination.exists())

    def test_many_individually_small_members_rejected_before_reads(self):
        files = [('Data'+str(i)+'.lean', b'-- FAKE DATA\n') for i in range(12)]
        inv = dict(schema='conditional-separation-source-files-v1', files=[
            dict(path=n, bytes=len(b), sha256=hashlib.sha256(b).hexdigest()) for n,b in files])
        data = zip_data(files + [('PACKAGE_FILES.json', json.dumps(inv).encode())])
        # Lowered constant tests the actual production guard; no large allocation.
        with mock.patch.object(m, 'SOURCE_MAX_MEMBERS', 12), \
             mock.patch.object(m.zipfile.ZipFile, 'read', side_effect=AssertionError('unexpected decompression')) as read:
            with self.assertRaisesRegex(ValueError, 'member-count budget'):
                m.unpack_source(data, self.destination)
            read.assert_not_called()
        self.assertFalse(self.destination.exists())

    def test_source_total_budget_exact_and_over_before_reads(self):
        data = source_archive()
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            total = sum(i.file_size for i in z.infolist())
        with mock.patch.object(m, 'SOURCE_MAX_TOTAL_BYTES', total):
            self.assertEqual(len(m.source_payloads(data)), 2)
        with mock.patch.object(m, 'SOURCE_MAX_TOTAL_BYTES', total-1), \
             mock.patch.object(m.zipfile.ZipFile, 'read', side_effect=AssertionError('unexpected decompression')) as read:
            with self.assertRaisesRegex(ValueError, 'declared aggregate budget'):
                m.unpack_source(data, self.destination)
            read.assert_not_called()
        self.assertFalse(self.destination.exists())

    def test_all_declared_metadata_checked_before_first_read(self):
        original = m.zipfile.ZipFile.infolist
        for bad in [False, -1, 'wrong type', m.SOURCE_MAX_MEMBER_BYTES+1, 'symlink']:
            def members(z):
                rows = original(z)
                if bad == 'symlink': rows[-1].external_attr = (stat.S_IFLNK | 0o777) << 16
                else: rows[-1].file_size = bad
                return rows
            with self.subTest(metadata=bad), mock.patch.object(m.zipfile.ZipFile, 'infolist', members), \
                 mock.patch.object(m.zipfile.ZipFile, 'read', side_effect=AssertionError('unexpected decompression')) as read:
                with self.assertRaises(ValueError): m.unpack_source(source_archive(), self.destination)
                read.assert_not_called()
            self.assertFalse(self.destination.exists())

    def test_actual_cumulative_bytes_checked_even_with_false_metadata(self):
        data = source_archive()
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            total = sum(i.file_size for i in z.infolist())
        with mock.patch.object(m, 'SOURCE_MAX_TOTAL_BYTES', total), \
             mock.patch.object(m.zipfile.ZipFile, 'read', return_value=b'X'*(total+1)):
            with self.assertRaisesRegex(ValueError, 'actual aggregate budget'):
                m.unpack_source(data, self.destination)
        self.assertFalse(self.destination.exists())

    def test_actual_member_size_and_payload_type_must_match(self):
        for payload in [b'', b'wrong size', None]:
            with self.subTest(payload=payload), mock.patch.object(m.zipfile.ZipFile, 'read', return_value=payload):
                with self.assertRaisesRegex(ValueError, 'actual size mismatch|payload type'):
                    m.unpack_source(source_archive(), self.destination)
            self.assertFalse(self.destination.exists())

    def test_complete_current_package_fits_and_extracts_exactly(self):
        inventory = json.loads((ROOT/'PACKAGE_FILES.json').read_bytes())['files']
        files = [(r['path'], (ROOT/r['path']).read_bytes()) for r in inventory]
        files.append(('PACKAGE_FILES.json', (ROOT/'PACKAGE_FILES.json').read_bytes()))
        self.assertEqual(len(files), 1180)
        self.assertLessEqual(len(files), m.SOURCE_MAX_MEMBERS)
        self.assertLessEqual(sum(len(b) for _,b in files), m.SOURCE_MAX_TOTAL_BYTES)
        self.assertLessEqual(max(len(b) for _,b in files), m.SOURCE_MAX_MEMBER_BYTES)
        data = zip_data(files)
        self.destination.with_suffix('.zip').write_bytes(data) # Retained SOURCE/DATA, not compiler evidence.
        root = m.unpack_source(data, self.destination)
        actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
        self.assertEqual(actual, {n for n,_ in files})
        for name,body in files:
            self.assertEqual(hashlib.sha256((root/name).read_bytes()).digest(), hashlib.sha256(body).digest())

    def test_frozen_dependency_lock(self):
        fixture = ROOT / "dependency-lock.fixture.json"
        if not fixture.exists():
            fixture = ROOT / "lake-manifest.json"
        data = fixture.read_bytes()
        self.assertEqual(len(m.validate_lock(data)), 9)
        with self.assertRaises(ValueError):
            m.validate_lock(data + b" ")

    def test_installer_commands_are_only_plans(self):
        plan = m.install_commands(Path("INERT-elan-init"), Path("PRIVATE-elan"), "Linux")
        self.assertIn("--no-modify-path", plan[1])
        self.assertIn("none", plan[1])
        self.assertIn("leanprover/lean4:v4.22.0-rc2", plan[2])

    def test_conditional_consumer_does_not_claim_R(self):
        source = m.consumer_source()
        self.assertIn("ConditionalSeparation.OpenProblem.R", source)
        self.assertIn("theorem conditional_surface", source)
        self.assertIn("theorem check_conditional_surface", source)
        self.assertNotIn("theorem research_lower_bound", source)
        self.assertEqual(source.count("ContentPrefixExtensionLanguage"), 6)

    def test_workflow_literal_standard_matrix(self):
        path = SUPPORT / "conditional-separation-native-v2.yml"
        # The workflow is installed outside the package, so distributed package
        # unit tests omit only this source-location check when it is absent.
        if not path.exists():
            self.skipTest("workflow lives at repository .github/workflows after integration")
        text = path.read_text(encoding="utf-8")
        actual = dict(re.findall(r"- runner: ([\w.-]+)\n\s+python-arch: (\w+)", text))
        self.assertEqual(actual, {k: m.RUNNERS[k][2] for k in ("ubuntu-24.04", "macos-15")})
        self.assertNotIn("windows-", text)
        self.assertIn("CI_EXPECTED_HEAD: ${{ inputs.source_sha || github.sha }}", text)
        self.assertIn("CI_CONTROLLER_SHA: ${{ inputs.controller_sha || github.sha }}", text)
        self.assertIn("branches: ['infrastructure/conditional-separation-package-docfix-20261031']", text)
        self.assertNotIn("pull_request:", text)
        self.assertNotIn("github.event.pull_request.head.sha", text)
        self.assertIn("github.repository == 'khanukov/p-np2'", text)
        self.assertIn("github.ref_name != 'main' && github.ref_name != 'master'", text)
        self.assertIn("max-parallel: 2", text)
        self.assertIn("controller != os.environ['GITHUB_WORKFLOW_SHA']", text)
        self.assertIn("FETCH_HEAD^{commit}", text)
        self.assertNotIn("uses: actions/checkout@", text)
        self.assertNotIn("core.protectNTFS=false", text)
        self.assertIn("contents: read", text)
        self.assertNotIn("pull_request_target:", text)
        self.assertEqual(re.findall(r"uses: ([^\n]+)", text), [
            "actions/setup-python@6d4fd22b20465ccc0f7354476588e8df7c9ca0e0",
            "actions/upload-artifact@cf430e030ddbb5b0abf93d22962f4752f3646cd9"])

    def assert_workflow_dispatch(self,block,entry,phase=None):
        """Parse the literal argv; never execute the stub, dispatcher or a child."""
        tree=ast.parse('\n'.join(line[10:] for line in block.splitlines()))
        self.assertEqual([type(n) for n in tree.body],
                         [ast.Import,ast.ImportFrom,ast.Assign,ast.Assign,ast.Assign,ast.Expr])
        self.assertEqual(ast.unparse(tree.body[0]),'import os, subprocess, sys')
        self.assertEqual(ast.unparse(tree.body[1]),'from pathlib import Path')
        self.assertEqual([ast.unparse(n.targets[0]) for n in tree.body[2:5]],['helper','anchor','stub'])
        self.assertEqual(ast.unparse(tree.body[2].value),"Path(os.environ['RUNNER_TEMP']) / 'trusted-native-controls-v1.py'")
        anchor=hashlib.sha256((SUPPORT/'trusted_controls_v1.py').read_bytes()).hexdigest()
        self.assertEqual(ast.literal_eval(tree.body[3].value),anchor)
        stub=("import hashlib,pathlib,sys; p=pathlib.Path(sys.argv[1]); b=p.read_bytes(); "
              "assert hashlib.sha256(b).hexdigest()==sys.argv[2], 'dispatcher hash'; "
              "sys.argv=[str(p),*sys.argv[3:]]; "
              "exec(compile(b,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})")
        self.assertEqual(ast.literal_eval(tree.body[4].value),stub)
        call=tree.body[-1].value
        self.assertIsInstance(call,ast.Call)
        self.assertEqual(ast.unparse(call.func),'subprocess.run')
        self.assertEqual(len(call.args),1)
        expected="[sys.executable, '-I', '-S', '-B', '-c', stub, str(helper), anchor, '--run', anchor, str(Path.cwd()), "+repr(entry)
        if phase is not None:expected+=', '+repr(phase)
        expected+=']'
        self.assertEqual(ast.dump(call.args[0]),ast.dump(ast.parse(expected,mode='eval').body))
        self.assertEqual([(k.arg,ast.literal_eval(k.value)) for k in call.keywords],[('check',True)])

    def test_workflow_python_phase_binding_is_data(self):
        text=(SUPPORT/'conditional-separation-native-v2.yml').read_text(encoding='utf-8')
        blocks=re.findall(r'        run: \|\n((?:          [^\n]*\n)+)',text)
        self.assertEqual(len(blocks),6)
        for block,phase in zip(blocks[1:5],['bootstrap','foundations','build','consumers']):
            with self.subTest(phase=phase):self.assert_workflow_dispatch(block,'ci/native_ci_v1.py',phase)
        self.assert_workflow_dispatch(blocks[5],'ci/export_ci_evidence_v2.py')
        self.assertIn('if: ${{ always() }}',text.split('- name: Stage bounded owned evidence even on failure',1)[1])

    def test_workflow_dispatch_mutations_are_rejected(self):
        text=(SUPPORT/'conditional-separation-native-v2.yml').read_text(encoding='utf-8')
        blocks=re.findall(r'        run: \|\n((?:          [^\n]*\n)+)',text)
        self.assertEqual(len(blocks),6)
        block=blocks[1]
        mutations=[("'-I', ",''),("'-S', ",''),("'-B', ",''),('check=True','check=False'),
                   ("'--run'","'--check'"),("'bootstrap'","'consumers'"),
                   ("'ci/native_ci_v1.py'","'ci/UNTRUSTED.py'"),
                   ("'trusted-native-controls-v1.py'","'untrusted.py'"),
                   ("assert hashlib.sha256(b).hexdigest()==sys.argv[2]","assert True"),
                   ('anchor, str(Path.cwd())',"'0'*64, str(Path.cwd())")]
        for old,new in mutations:
            self.assertIn(old,block)
            with self.subTest(old=old),self.assertRaises(AssertionError):
                self.assert_workflow_dispatch(block.replace(old,new,1),'ci/native_ci_v1.py','bootstrap')
        with self.subTest(export='wrong entry'),self.assertRaises(AssertionError):
            self.assert_workflow_dispatch(blocks[5].replace('ci/export_ci_evidence_v2.py','ci/native_ci_v1.py'),
                                          'ci/export_ci_evidence_v2.py')


    def test_future_driver_is_syntax_checked_only(self):
        text = (SUPPORT / "native_ci_v1.py").read_text(encoding="utf-8")
        tree = ast.parse(text)
        self.assertIsInstance(tree, ast.Module)
        self.assertIn('["lake", "build", "ProofCore", "ConditionalSeparation"]', text)
        self.assertIn('cwd', text)
        self.assertNotIn("/root/", text)
        # No import or execution of this operational source occurs in DATA.


if __name__ == "__main__":
    unittest.main()
