"""Stdlib DATA tests; fake cores perform only owned marker writes, never Lean."""
import datetime
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent


class BootstrapTests(unittest.TestCase):
    def setUp(self):
        # Keep inert fixtures, including markers and substituted bytes, as DATA.
        self.root = Path(tempfile.mkdtemp(prefix='solver-dag-bootstrap-'))
        spec = importlib.util.spec_from_file_location('checker_under_test', HERE / 'check.py')
        self.checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.checker)

    def run_checker(self, core, *, flags=('-B',)):
        output = self.root / 'must-not-exist'
        argv = [sys.executable, *flags, str(HERE / 'check.py'),
                '--core', str(core), '--output', str(output)]
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            ticks = Path('/proc', str(p.pid), 'stat').read_text().rsplit(')', 1)[1].split()[19]
        except OSError:
            ticks = None
        out, err = p.communicate()
        record = dict(argv=argv, cwd=os.getcwd(), pid=p.pid, startticks=ticks,
                      start_UTC=start, end_UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      waited=True, OS_exit=p.returncode, stdout=out.decode(), stderr=err.decode(),
                      synthetic_DATA=True)
        receipts = os.environ.get('SOLVER_DAG_TEST_RECEIPTS')
        if receipts:
            dest = Path(receipts)
            dest.mkdir(parents=True, exist_ok=True)
            with (dest / (self._testMethodName + '.json')).open('x') as h:
                json.dump(record, h, indent=2)
                h.write('\n')
        return p.returncode, err.decode(), output

    def admitted_core(self):
        value = os.environ.get('SOLVER_DAG_TEST_CORE')
        if not value:
            self.skipTest('set SOLVER_DAG_TEST_CORE to the pre-trusted installed core')
        return Path(value).resolve()

    def trusted_bytes_fixture(self):
        core = self.root / 'inert-copy'
        (core / 'tools').mkdir(parents=True)
        real = self.admitted_core()
        for name in ('tools/workbench.py', 'PACKAGE_FILES.json'):
            (core / name).write_bytes((real / name).read_bytes())
        return core

    def test_rejected_core_never_executes_import_marker(self):
        with tempfile.TemporaryDirectory(prefix='solver-dag-bootstrap-') as td:
            root = Path(td)
            core = root / 'fake-core'
            (core / 'tools').mkdir(parents=True)
            marker = root / 'SYNTHETIC_IMPORT_MARKER'
            (core / 'tools/workbench.py').write_text(
                'from pathlib import Path\n'
                f'Path({str(marker)!r}).write_text("SYNTHETIC DATA ONLY")\n'
                'def verify_core(core):\n'
                '    raise ValueError("SYNTHETIC_FAKE_CORE_REJECTED")\n')
            output = root / 'must-not-exist'
            argv = [sys.executable, '-B', str(HERE / 'check.py'),
                    '--core', str(core), '--output', str(output)]
            start = datetime.datetime.now(datetime.timezone.utc).isoformat()
            p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                ticks = Path('/proc', str(p.pid), 'stat').read_text().rsplit(')', 1)[1].split()[19]
            except OSError:
                ticks = None
            out, err = p.communicate()
            record = dict(argv=argv, cwd=os.getcwd(), pid=p.pid, startticks=ticks,
                          start_UTC=start, end_UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                          waited=True, OS_exit=p.returncode, stdout=out.decode(), stderr=err.decode(),
                          marker_seen=marker.exists(), synthetic_DATA=True)
            receipts = os.environ.get('SOLVER_DAG_TEST_RECEIPTS')
            if receipts:
                dest = Path(receipts)
                dest.mkdir(parents=True, exist_ok=True)
                with (dest / (self._testMethodName + '.json')).open('x') as h:
                    json.dump(record, h, indent=2)
                    h.write('\n')
            self.assertNotEqual(p.returncode, 0)
            self.assertTrue('SYNTHETIC_FAKE_CORE_REJECTED' in err.decode()
                            or 'untrusted installed' in err.decode(), err.decode())
            self.assertFalse(output.exists())
            self.assertFalse(marker.exists(), 'rejected core executed marker before trusted identity')

    def test_missing_loader_fails_closed(self):
        with self.assertRaisesRegex(ValueError, 'untrusted installed source path'):
            self.checker.load_workbench(self.root / 'absent')

    def test_invalid_loader_rejected_before_compilation(self):
        core = self.root / 'invalid'
        (core / 'tools').mkdir(parents=True)
        (core / 'tools/workbench.py').write_bytes(b'not valid Python !!!')
        with self.assertRaisesRegex(ValueError, 'untrusted installed source identity'):
            self.checker.load_workbench(core)

    def test_self_supplied_manifest_does_not_authorize_loader(self):
        core = self.root / 'self-authenticated'
        (core / 'tools').mkdir(parents=True)
        marker = self.root / 'self-marker'
        raw = f'from pathlib import Path\nPath({str(marker)!r}).touch()\n'.encode()
        (core / 'tools/workbench.py').write_bytes(raw)
        import hashlib
        (core / 'PACKAGE_FILES.json').write_text(json.dumps({'files': [
            {'path': 'tools/workbench.py', 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}]}))
        rc, err, output = self.run_checker(core)
        self.assertNotEqual(rc, 0)
        self.assertIn('untrusted installed source identity', err)
        self.assertFalse(marker.exists())
        self.assertFalse(output.exists())

    def test_substituted_inventory_rejected_before_exec(self):
        core = self.trusted_bytes_fixture()
        (core / 'PACKAGE_FILES.json').write_bytes(b'{}')
        with mock.patch('builtins.exec', side_effect=AssertionError('must reject before exec')):
            with self.assertRaisesRegex(ValueError, 'untrusted installed source identity: PACKAGE_FILES'):
                self.checker.load_workbench(core)

    def test_symlinked_loader_rejected(self):
        core = self.root / 'linked'
        (core / 'tools').mkdir(parents=True)
        (core / 'tools/workbench.py').symlink_to(self.admitted_core() / 'tools/workbench.py')
        with self.assertRaisesRegex(ValueError, 'untrusted installed source path'):
            self.checker.load_workbench(core)

    def test_executes_same_checked_buffer_not_reopened_source(self):
        # DATA seam: replace only this inert file immediately after its read.
        core = self.trusted_bytes_fixture()
        loader = core / 'tools/workbench.py'
        marker = self.root / 'reopen-marker'
        original_read = Path.read_bytes
        def read_then_substitute(path):
            raw = original_read(path)
            if path == loader:
                loader.write_text(f'from pathlib import Path\nPath({str(marker)!r}).touch()\n')
            return raw
        with mock.patch.object(Path, 'read_bytes', read_then_substitute):
            wb = self.checker.load_workbench(core)
        self.assertTrue(callable(wb.verify_core))
        self.assertFalse(marker.exists())

    def test_actual_admitted_installed_core_positive(self):
        wb = self.checker.load_workbench(self.admitted_core())
        self.assertEqual(wb.verify_core(self.admitted_core()), self.checker.INVENTORY_SHA256)

    def test_optimized_execution_retains_workbench_rejection(self):
        rc, err, output = self.run_checker(self.admitted_core(), flags=('-O', '-B'))
        self.assertNotEqual(rc, 0)
        self.assertIn('optimized checker rejected', err)
        self.assertFalse(output.exists())


if __name__ == '__main__':
    unittest.main()
