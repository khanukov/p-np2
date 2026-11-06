"""Finite FAKE DATA only; never SDK, native workflow, compiler or network."""
import contextlib
import errno
import hashlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def guard_data():
    path = ROOT / 'ci/trusted_controls_v1.py'
    name = 'OWN_TRUST_GUARD_DATA_' + str(len(sys.modules))
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


class TrustedControlsDATA(unittest.TestCase):
    def fixture(self):
        m = guard_data()
        package = Path(tempfile.mkdtemp(prefix='FAKE_DATA_NOT_LEAN-', dir=os.environ['CI_DATA_ROOT']))
        bodies = {
            'ci/native_ci_v1.py': b"from pathlib import Path\nimport portable_ci_data_v1\nimport trusted_controls_v1\ntrusted_controls_v1.require_control_context(Path(__file__).resolve().parents[1])\nassert portable_ci_data_v1.VALUE == 'FAKE_DATA_ORIGINAL'\nprint('FAKE_DATA_SELECTED:'+str(Path(__file__).resolve().parents[1]))\n",
            'ci/portable_ci_data_v1.py': b"VALUE='FAKE_DATA_ORIGINAL'\n",
            'ci/ci_evidence_data_v2.py': b"VALUE='FAKE_DATA_EXPORT_HELPER'\n",
            'ci/export_ci_evidence_v2.py': b"import ci_evidence_data_v2\nassert ci_evidence_data_v2.VALUE=='FAKE_DATA_EXPORT_HELPER'\nprint('FAKE_DATA_EXPORT')\n",
            'ci/package_source_v1.py': b"VALUE='FAKE_DATA_MATERIALIZER'\n",
            'ci/run_data_tests_v2.py': b"print('FAKE_DATA_UNIT_ENTRY')\n",
            'tools/workbench.py': b"VALUE='FAKE_DATA_WORKBENCH'\n",
            'tools/SourceImports.lean': b'-- FAKE DATA bytes, never compiled\n',
            'tests/lean_rejections.py': b"print('FAKE_DATA_NEGATIVE_ENTRY')\n",
            'tests/test_unit_DATA.py': b"VALUE='FAKE_DATA_UNIT'\n",
            'lean-toolchain': b'FAKE_DATA_NO_SDK\n',
        }
        for name, raw in bodies.items():
            p = package / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(raw)
        (package / m.SELF).write_bytes(Path(m.__file__).read_bytes())
        (package / m.WORKFLOW_DATA).write_bytes(b'FAKE_DATA_NOT_AN_EXECUTED_WORKFLOW\n')
        manifest = {'schema': 'trusted-native-controls-v1',
                    'seed_revision': '9c8e998457514fbf3f2dba5cc3a0edf362010571',
                    'files': [dict(path=n, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
                              for n, raw in sorted(bodies.items())]}
        data = (json.dumps(manifest, sort_keys=True) + '\n').encode()
        (package / m.MANIFEST).write_bytes(data)
        # An explicitly FAKE independent trust root, only in this inert module.
        # Production has no flag/argument permitting manifest-anchor replacement.
        m.MANIFEST_SHA256 = hashlib.sha256(data).hexdigest()
        anchor = hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
        return m, package, anchor, manifest

    def run_fake(self, m, package, anchor, entry='ci/native_ci_v1.py'):
        out = io.StringIO()
        with patch('subprocess.Popen', side_effect=AssertionError('NO process DATA effect')), \
             patch('subprocess.run', side_effect=AssertionError('NO process DATA effect')), \
             patch('urllib.request.urlopen', side_effect=AssertionError('NO network DATA effect')), \
             contextlib.redirect_stdout(out):
            m.run_control(package, anchor, entry, [])
        return out.getvalue()

    def test_actual_complete_proposed_control_tuple(self):
        m = guard_data()
        anchor = hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
        data = m.verify_controls(ROOT, anchor)
        self.assertIn('ci/native_ci_v1.py', data)
        self.assertIn('ci/export_ci_evidence_v2.py', data)
        self.assertIn('tools/workbench.py', data)
        self.assertIn('tests/lean_rejections.py', data)

    def test_authenticated_snapshots_keep_tested_package_filename(self):
        m, package, anchor, _ = self.fixture()
        self.assertEqual(self.run_fake(m, package, anchor), 'FAKE_DATA_SELECTED:'+str(package)+'\n')
        self.assertEqual(self.run_fake(m, package, anchor, 'ci/export_ci_evidence_v2.py'), 'FAKE_DATA_EXPORT\n')

    def test_authenticated_main_snapshot_namespace_exports_context(self):
        import ast
        m, package, anchor, _ = self.fixture()
        namespace = {'__name__':'__main__','__file__':m.__file__}
        tree = ast.parse(Path(m.__file__).read_bytes())
        body = [n for n in tree.body if not (isinstance(n,ast.If) and ast.unparse(n.test)=="__name__ == '__main__'")]
        exec(compile(ast.Module(body=body,type_ignores=[]),m.__file__,'exec'),namespace)
        namespace['MANIFEST_SHA256'] = m.MANIFEST_SHA256  # Explicit FAKE trust-root fixture only.
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            namespace['run_control'](package,anchor,'ci/native_ci_v1.py',[])
        self.assertEqual(output.getvalue(),'FAKE_DATA_SELECTED:'+str(package)+'\n')

    def test_PR_noop_driver_helper_exporter_rejected_before_execution(self):
        for target in ('ci/native_ci_v1.py', 'ci/portable_ci_data_v1.py',
                       'ci/ci_evidence_data_v2.py', 'ci/export_ci_evidence_v2.py',
                       'tools/workbench.py', 'tests/lean_rejections.py'):
            with self.subTest(target=target):
                m, package, anchor, _ = self.fixture()
                (package / target).write_bytes(b"raise AssertionError('SUBSTITUTED_FAKE_DATA_MUST_NOT_EXECUTE')\n")
                with self.assertRaisesRegex(ValueError, 'untrusted changed control'):
                    self.run_fake(m, package, anchor)

    def test_PR_manifest_cannot_authorize_its_own_changed_driver(self):
        m, package, anchor, value = self.fixture()
        raw = b"print('FAKE_DATA_NOOP')\n"
        (package / 'ci/native_ci_v1.py').write_bytes(raw)
        row = next(r for r in value['files'] if r['path'] == 'ci/native_ci_v1.py')
        row.update(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        (package / m.MANIFEST).write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, 'trusted manifest digest'):
            self.run_fake(m, package, anchor)

    def test_missing_extra_and_bytecode_control_domain_rejects(self):
        for change in ('missing', 'extra', 'cache'):
            with self.subTest(change=change):
                m, package, anchor, _ = self.fixture()
                if change == 'missing':
                    (package / 'ci/portable_ci_data_v1.py').rename(package / 'REMOVED_DATA.txt')
                elif change == 'extra':
                    (package / 'ci/unlisted.py').write_bytes(b"raise AssertionError('UNKNOWN_DATA')\n")
                else:
                    (package / 'tools/__pycache__').mkdir()
                with self.assertRaises((ValueError, OSError)):
                    self.run_fake(m, package, anchor)

    def test_dispatcher_hash_and_manifest_schema_types_are_strict(self):
        m, package, anchor, value = self.fixture()
        with self.assertRaisesRegex(ValueError, 'external dispatcher digest'):
            m.verify_controls(package, 'f'*64)
        import copy
        variants = []
        for key, wrong in [('bytes', True), ('bytes', -1), ('sha256', 'A'*64), ('path', '../escape'),
                           ('path', 'ci/CON.py'), ('path', 'ci/dir./x.py')]:
            item = copy.deepcopy(value);item['files'][0][key] = wrong;variants.append(item)
        item = copy.deepcopy(value);item['files'].append(dict(item['files'][0]));variants.append(item)
        item = copy.deepcopy(value);item['files'][0]['unknown'] = 1;variants.append(item)
        for item in variants:
            raw = json.dumps(item).encode()
            with self.subTest(value=item['files'][0]), self.assertRaises(ValueError):
                m.manifest_rows(raw, hashlib.sha256(raw).hexdigest())
        duplicate = b'{"schema":1,"schema":2}'
        with self.assertRaisesRegex(ValueError, 'duplicate manifest key'):
            m.manifest_rows(duplicate, hashlib.sha256(duplicate).hexdigest())

    def test_real_symlink_and_hardlink_controls_rejected(self):
        for kind in ('symlink', 'hardlink'):
            m, package, anchor, _ = self.fixture()
            p = package / 'ci/portable_ci_data_v1.py';target = package / 'DATA-original.txt'
            p.rename(target)
            try:
                if kind == 'symlink':p.symlink_to(target)
                else:os.link(target, p)
            except OSError as error:
                permitted = {errno.EPERM, errno.EACCES, errno.ENOSYS, errno.ENOTSUP,
                             getattr(errno, 'EOPNOTSUPP', errno.ENOTSUP)}
                if error.errno not in permitted and getattr(error, 'winerror', None) not in {50, 1314}:
                    raise
                self.skipTest('own DATA link capability unavailable: '+str(error))
            with self.assertRaisesRegex(ValueError, 'physical|aliased|single-link'):
                m.verify_controls(package, anchor)

    def test_snapshot_loader_does_not_execute_replacement_bytes(self):
        m, package, anchor, _ = self.fixture()
        snapshots = m.verify_controls(package, anchor)
        path = package / 'ci/portable_ci_data_v1.py'
        loader = m.SnapshotLoader(path, snapshots['ci/portable_ci_data_v1.py'])
        path.write_bytes(b"raise AssertionError('REPLACEMENT_FAKE_DATA')\n")
        module = types.ModuleType('OWN_SNAPSHOT_FAKE_DATA')
        loader.exec_module(module)
        self.assertEqual(module.VALUE, 'FAKE_DATA_ORIGINAL')
        self.assertEqual(module.__file__, str(path))
        with self.assertRaises(ValueError):m.verify_controls(package, anchor)

    def test_link_capability_skips_are_narrow_and_EIO_propagates(self):
        method = self.test_real_symlink_and_hardlink_controls_rejected
        for code in (errno.EPERM, errno.EACCES, errno.ENOSYS, errno.ENOTSUP):
            with self.subTest(errno=code), patch.object(Path, 'symlink_to', side_effect=OSError(code, 'FAKE_DATA_DENIAL')):
                with self.assertRaises(unittest.SkipTest): method()
        for code in (errno.EIO, errno.ENOENT, errno.ENOSPC):
            with self.subTest(errno=code), patch.object(Path, 'symlink_to', side_effect=OSError(code, 'FAKE_DATA_FAILURE')):
                try:
                    with self.assertRaises(OSError) as caught: method()
                except unittest.SkipTest as error:
                    self.fail('unexpected fixture failure hidden as skip: '+str(error))
                self.assertEqual(caught.exception.errno, code)

    def test_combined_failure_keeps_primary_and_integrity_without_add_note(self):
        # Missing/non-callable/raising annotation API equivalents, not Python3.10 execution.
        for behavior in ('missing', 'noncallable', 'raises'):
            m, package, anchor, value = self.fixture()
            body = ['from pathlib import Path', 'class PrimaryDATA(RuntimeError):']
            if behavior == 'missing':
                body += ['    def __getattribute__(self, name):',
                         "        if name == 'add_note': raise AttributeError('FAKE_DATA_MISSING')",
                         '        return super().__getattribute__(name)']
            elif behavior == 'noncallable': body.append('    add_note = None')
            else: body += ['    def add_note(self, note):', "        raise OSError('FAKE_DATA_NOTE_FAILURE')"]
            body += ["(Path(__file__).parents[1]/'ci/portable_ci_data_v1.py').write_text('FAKE_DATA_CHANGED')",
                     "raise PrimaryDATA('FAKE_DATA_PRIMARY')"]
            code = ('\n'.join(body)+'\n').encode()
            (package/'ci/native_ci_v1.py').write_bytes(code)
            row = next(r for r in value['files'] if r['path']=='ci/native_ci_v1.py')
            row.update(bytes=len(code), sha256=hashlib.sha256(code).hexdigest())
            raw = json.dumps(value).encode();(package/m.MANIFEST).write_bytes(raw)
            m.MANIFEST_SHA256 = hashlib.sha256(raw).hexdigest()  # Explicit FAKE root only.
            with self.subTest(behavior=behavior):
                with self.assertRaisesRegex(RuntimeError, 'FAKE_DATA_PRIMARY') as caught:
                    self.run_fake(m, package, anchor)
                self.assertIsInstance(caught.exception.__cause__, ValueError)
                self.assertIn('untrusted changed control', str(caught.exception.__cause__))
                self.assertIsNone(m._ANCHOR);self.assertIsNone(m._PACKAGE)

    def test_owned_launcher_routes_only_registered_python_children(self):
        m, package, anchor, _ = self.fixture();m._ANCHOR = anchor;m._PACKAGE = package
        argv = [sys.executable, '-B', 'tests/lean_rejections.py', '--attempt', 'FAKE_DATA']
        selected = m.control_argv(package, argv)
        self.assertEqual(selected[:4], [sys.executable, '-I', '-S', '-B'])
        self.assertEqual(selected[5:], ['--run', anchor, str(package), *argv[2:]])
        external = ['lake', 'build', 'ProofCore', 'ConditionalSeparation']
        self.assertIs(m.control_argv(package, external), external)
        for script in ('../elsewhere.py', 'ci/noop.py', '/FAKE_DATA/other.py'):
            with self.assertRaises((ValueError, KeyError)):
                m.control_argv(package, [sys.executable, '-B', script])
        with self.assertRaises(ValueError):m.control_argv(package, [sys.executable, '-c', 'pass'])
        with self.assertRaises(ValueError):m.require_control_context(package / 'wrong')

    def test_nonzero_exception_and_missing_context_are_not_success(self):
        m, package, anchor, _ = self.fixture()
        with self.assertRaises(ValueError):m.require_control_context(package)
        old = m._ANCHOR,m._PACKAGE
        with self.assertRaisesRegex(ValueError, 'registered control entry'):
            m.run_control(package, anchor, 'ci/portable_ci_data_v1.py', [])
        self.assertEqual((m._ANCHOR,m._PACKAGE),old)
        for code, error in [(b'raise SystemExit(7)\n', SystemExit),
                            (b"raise RuntimeError('FAKE_DATA_FAILURE')\n", RuntimeError)]:
            m, package, anchor, value = self.fixture()
            (package/'ci/native_ci_v1.py').write_bytes(code)
            row = next(r for r in value['files'] if r['path']=='ci/native_ci_v1.py')
            row.update(bytes=len(code),sha256=hashlib.sha256(code).hexdigest())
            raw = json.dumps(value).encode();(package/m.MANIFEST).write_bytes(raw)
            m.MANIFEST_SHA256 = hashlib.sha256(raw).hexdigest()
            with self.assertRaises(error):self.run_fake(m,package,anchor)
            self.assertIsNone(m._ANCHOR);self.assertIsNone(m._PACKAGE)

    def test_post_execution_integrity_failure_is_not_success(self):
        m, package, anchor, value = self.fixture()
        code = b"from pathlib import Path\n(Path(__file__).parents[1]/'ci/portable_ci_data_v1.py').write_text('FAKE_DATA_CHANGED')\n"
        (package/'ci/native_ci_v1.py').write_bytes(code)
        row = next(r for r in value['files'] if r['path']=='ci/native_ci_v1.py')
        row.update(bytes=len(code),sha256=hashlib.sha256(code).hexdigest())
        raw = json.dumps(value).encode();(package/m.MANIFEST).write_bytes(raw)
        m.MANIFEST_SHA256 = hashlib.sha256(raw).hexdigest()
        with self.assertRaisesRegex(ValueError,'untrusted changed control'):
            self.run_fake(m,package,anchor)

    def exit_fixture_with_restoration_check(self, code, mutate):
        import importlib.util
        m, package, anchor, value = self.fixture()
        lines = ['from pathlib import Path']
        if mutate:
            lines.append("(Path(__file__).parents[1]/'ci/portable_ci_data_v1.py').write_text('FAKE_DATA_CHANGED')")
        lines.append('raise SystemExit('+repr(code)+')')
        raw_code = ('\n'.join(lines)+'\n').encode()
        (package/'ci/native_ci_v1.py').write_bytes(raw_code)
        row = next(r for r in value['files'] if r['path']=='ci/native_ci_v1.py')
        row.update(bytes=len(raw_code),sha256=hashlib.sha256(raw_code).hexdigest())
        raw = json.dumps(value).encode();(package/m.MANIFEST).write_bytes(raw)
        m.MANIFEST_SHA256 = hashlib.sha256(raw).hexdigest()  # FAKE fixture root only.
        names = {Path(r['path']).stem for r in value['files'] if r['path'].endswith('.py')}|{'trusted_controls_v1'}
        missing = object();modules = {n:sys.modules.get(n,missing) for n in names}
        context = m._ANCHOR,m._PACKAGE;hooks = list(sys.meta_path)
        maker,argv = importlib.util.spec_from_file_location,sys.argv
        def dispatch():
            try:self.run_fake(m,package,anchor)
            finally:
                self.assertEqual((m._ANCHOR,m._PACKAGE),context)
                self.assertEqual(sys.meta_path,hooks)
                self.assertIs(importlib.util.spec_from_file_location,maker)
                self.assertIs(sys.argv,argv)
                for name,original in modules.items():self.assertIs(sys.modules.get(name,missing),original)
        return dispatch

    def test_failed_postcheck_cannot_be_successful_SystemExit(self):
        for code in (0,None,False,256,-256):
            with self.subTest(code=code):
                dispatch = self.exit_fixture_with_restoration_check(code,True)
                with self.assertRaisesRegex(RuntimeError,'post-control integrity failed after successful entry exit') as caught:
                    dispatch()
                integrity = caught.exception.__cause__
                self.assertIs(type(integrity),ValueError)
                self.assertIn('untrusted changed control',str(integrity))
                original = integrity.__cause__
                self.assertIs(type(original),SystemExit)
                self.assertIs(type(original.code),type(code));self.assertEqual(original.code,code)
                # A RuntimeError escaping the child is nonzero; own DATA also
                # measures actual waited OS status, not assertRaises alone.
                self.assertNotIsInstance(caught.exception,SystemExit)

    def test_integrity_pass_successful_SystemExit_is_preserved(self):
        for code in (0,None,False):
            with self.subTest(code=code):
                dispatch = self.exit_fixture_with_restoration_check(code,False)
                with self.assertRaises(SystemExit) as caught:dispatch()
                self.assertIs(type(caught.exception.code),type(code))
                self.assertEqual(caught.exception.code,code);self.assertIsNone(caught.exception.__cause__)

    def test_failed_postcheck_preserves_failing_SystemExit_primary(self):
        dispatch = self.exit_fixture_with_restoration_check(7,True)
        with self.assertRaises(SystemExit) as caught:dispatch()
        self.assertEqual(caught.exception.code,7)
        self.assertIs(type(caught.exception.__cause__),ValueError)

    def test_zero_exit_from_postcheck_itself_is_not_success(self):
        # A bounded FAKE postcheck callback; no real native observation claimed.
        for code in (0,None,False):
            with self.subTest(code=code):
                m,package,anchor,_ = self.fixture()
                original = m.verify_controls;calls=[]
                def observe(p,a):
                    calls.append((p,a))
                    if len(calls)==1:return original(p,a)
                    raise SystemExit(code)
                with patch.object(m,'verify_controls',side_effect=observe):
                    with self.assertRaisesRegex(RuntimeError,'^post-control integrity failed$') as caught:
                        self.run_fake(m,package,anchor)
                self.assertEqual(len(calls),2)
                self.assertIs(type(caught.exception.__cause__),SystemExit)
                self.assertIs(type(caught.exception.__cause__.code),type(code))
                self.assertEqual(caught.exception.__cause__.code,code)
                self.assertIsNone(m._ANCHOR);self.assertIsNone(m._PACKAGE)

    def test_direct_dispatch_head_binding_and_wrong_controller_rejected(self):
        path = ROOT / 'ci/ci_evidence_data_v2.py';m = types.ModuleType('OWN_HEAD_DATA')
        exec(compile(path.read_bytes(),str(path),'exec'),m.__dict__)
        event = {'inputs': {'controller_sha':'a'*40,'source_sha':'b'*40}}
        identity = m.resolve_head('workflow_dispatch',event,'a'*40,'b'*40,'refs/heads/feature')
        self.assertEqual((identity['controller_input_sha'],identity['tested_head']),('a'*40,'b'*40))
        for controller,source in [('c'*40,'b'*40),('a'*40,True),('a'*40,'0'*40)]:
            event['inputs'] = dict(controller_sha=controller,source_sha=source)
            with self.assertRaises(ValueError):m.resolve_head('workflow_dispatch',event,'a'*40,'b'*40,'refs/heads/feature')

    def test_physical_workflow_pair_and_every_phase_uses_snapshot_dispatch(self):
        text = (ROOT/'ci/conditional-separation-native-v2.yml').read_text()
        self.assertNotIn('  pull_request:',text)
        self.assertIn('GITHUB_WORKFLOW_SHA',text)
        self.assertEqual(text.count("'--run', anchor"),5)
        self.assertEqual(text.count("exec(compile(b,str(p),'exec')"),5)
        self.assertNotIn("'-B', 'ci/native_ci_v1.py'",text)
        self.assertIn("github.repository == 'khanukov/p-np2'",text)

    def test_actual_remote_push_admission_and_wrong_refs_fail_before_effects(self):
        import textwrap
        workflow = (ROOT/'ci/conditional-separation-native-v2.yml').read_text()
        block = workflow.split('      - name: Package-only raw Git blobs at the exact public feature head\n',1)[1].split('      - name:',1)[0]
        code = textwrap.dedent(block.split('        run: |\n',1)[1]).split('temp = Path(',1)[0]
        event = Path(tempfile.mkdtemp(dir=os.environ['CI_DATA_ROOT']))/'EVENT_FAKE_DATA.json'
        event.write_text(json.dumps({'repository':{'full_name':'khanukov/p-np2','private':False}}))
        remote = 'refs/heads/infrastructure/conditional-separation-package-docfix-20261031'
        env = {'GITHUB_EVENT_PATH':str(event),'GITHUB_EVENT_NAME':'push','GITHUB_REF':remote,
               'GITHUB_SHA':'a'*40,'GITHUB_WORKFLOW_SHA':'a'*40,
               'CI_CONTROLLER_SHA':'a'*40,'CI_EXPECTED_HEAD':'a'*40}
        def call(changes):
            with patch.dict(os.environ,dict(env,**changes)), \
                 patch('subprocess.run',side_effect=AssertionError('NO acquisition effect')), \
                 patch('subprocess.Popen',side_effect=AssertionError('NO child effect')):
                exec(compile(code,'ACTUAL_WORKFLOW_ADMISSION_FAKE_DATA','exec'),{})
        call({})
        variants = [{'GITHUB_REF':ref} for ref in (
            'refs/heads/infrastructure/conditional-separation-package-parallel-20261101',
            'refs/heads/foreign','refs/heads/main','refs/heads/master')]
        variants += [{'CI_EXPECTED_HEAD':'b'*40},{'GITHUB_WORKFLOW_SHA':'c'*40},
                     {'GITHUB_EVENT_NAME':'pull_request'}]
        for changes in variants:
            with self.subTest(changes=changes), self.assertRaises(ValueError): call(changes)
