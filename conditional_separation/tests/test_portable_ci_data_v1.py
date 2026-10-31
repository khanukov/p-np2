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
        self.assertEqual(actual, {k: m.RUNNERS[k][2] for k in ("ubuntu-24.04", "macos-15", "windows-2022")})
        self.assertIn("CI_EXPECTED_HEAD: ${{ github.event.pull_request.head.sha || github.sha }}", text)
        self.assertIn("FETCH_HEAD^{commit}", text)
        self.assertNotIn("uses: actions/checkout@", text)
        self.assertNotIn("core.protectNTFS=false", text)
        self.assertIn("contents: read", text)
        self.assertNotIn("pull_request_target:", text)
        self.assertEqual(re.findall(r"uses: ([^\n]+)", text), [
            "actions/setup-python@6d4fd22b20465ccc0f7354476588e8df7c9ca0e0",
            "actions/upload-artifact@cf430e030ddbb5b0abf93d22962f4752f3646cd9"])

    def test_workflow_python_phase_binding_is_data(self):
        path = SUPPORT / "conditional-separation-native-v2.yml"
        if not path.exists():
            self.skipTest("workflow source-location check applies in prospective author bundle")
        text = path.read_text(encoding="utf-8")
        blocks = re.findall(r"        run: \|\n((?:          [^\n]*\n)+)", text)
        self.assertEqual(len(blocks), 6)
        phases = []
        for block in blocks[1:5]:
            tree = ast.parse("\n".join(line[10:] for line in block.splitlines()))
            call = tree.body[-1].value
            self.assertEqual(ast.unparse(call.func), "subprocess.run")
            self.assertEqual(ast.unparse(call.args[0].elts[0]), "sys.executable")
            self.assertEqual(ast.literal_eval(call.args[0].elts[1]), "-B")
            self.assertEqual(ast.literal_eval(call.args[0].elts[2]), "ci/native_ci_v1.py")
            phases.append(ast.literal_eval(call.args[0].elts[3]))
            self.assertTrue(any(k.arg == "check" and ast.literal_eval(k.value) for k in call.keywords))
        self.assertEqual(phases, ["bootstrap", "foundations", "build", "consumers"])
        export = ast.parse("\n".join(line[10:] for line in blocks[5].splitlines())).body[-1].value
        self.assertEqual(ast.literal_eval(export.args[0].elts[2]), "ci/export_ci_evidence_v2.py")
        self.assertEqual(len(export.args[0].elts), 3)

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
