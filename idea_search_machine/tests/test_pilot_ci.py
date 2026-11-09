import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from idea_search_machine.pilot_ci import run_suite


class CIContractTests(unittest.TestCase):
    def test_actual_workflow_uploads_hidden_owned_kernel_receipts(self):
        # Read the shipped workflow, then execute its collector on inert DATA.
        workflow = Path(__file__).resolve().parents[2]/'.github/workflows/idea-lean-pilot.yml'
        steps = json.loads(workflow.read_bytes())['jobs']['addon']['steps']
        uploads = [s for s in steps if s.get('uses', '').startswith('actions/upload-artifact@')]
        self.assertEqual(len(uploads), 1)
        upload = uploads[0]
        self.assertEqual(upload['with'].get('include-hidden-files'), 'true',
                         'owned export must explicitly include hidden kernel receipts')
        self.assertEqual(upload['uses'],
                         'actions/upload-artifact@cf430e030ddbb5b0abf93d22962f4752f3646cd9')
        self.assertEqual(upload['if'], '${{ always() }}')
        self.assertFalse(upload.get('continue-on-error', False))
        self.assertEqual(upload['with']['path'], '${{ runner.temp }}/idea-lean-owned-evidence')
        collectors = [s for s in steps if "<<'PYEXPORT'\n" in s.get('run', '')]
        self.assertEqual(len(collectors), 1)
        collector = collectors[0]
        self.assertEqual(collector['if'], '${{ always() }}')
        script = collector['run'].split("<<'PYEXPORT'\n", 1)[1].rsplit('\nPYEXPORT', 1)[0]
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            hidden = 'idea-lean-verification/kernel/attempt/.lake/conditional-check/runs/DATA/'
            accepted = {
                hidden+'own-0-compile/terminal.json': '{"DATA_fixture_only":true}',
                hidden+'Consumer.lean': '-- inert DATA, never compiled\n',
                hidden+'axioms.txt': 'inert DATA, not an axiom receipt\n',
                'idea-lean-build-evidence/build.json': '{"DATA_fixture_only":true}',
                'idea-lean-verification/candidate-00/PROVIDER.json': '{"DATA_fixture_only":true}',
            }
            rejected = {
                hidden+'Consumer.olean': 'inert object marker',
                hidden+'Consumer.ilean': 'inert object marker',
                'idea-lean-verification/candidate-00/stdout.txt': 'inert transcript marker',
                'idea-lean-verification/candidate-00/response.json': 'inert response marker',
                'unrelated/sentinel.txt': 'outside owned export roots',
            }
            for name, content in {**accepted, **rejected}.items():
                p = root/name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(content)
            (root/hidden/'link.txt').symlink_to(root/'unrelated/sentinel.txt')
            r = subprocess.run([sys.executable, '-B', '-c', script], cwd=root,
                               env=dict(os.environ, RUNNER_TEMP=str(root)),
                               capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout+r.stderr)
            dest = root/'idea-lean-owned-evidence'
            observed = {p.relative_to(dest).as_posix(): p.read_text()
                        for p in dest.rglob('*') if p.is_file()}
            self.assertEqual(observed, accepted)

    def check(self, suite, expected):
        with tempfile.TemporaryDirectory() as d:
            return run_suite(suite,Path(d)/'out',expected)

    def test_skipped_required_case_fails(self):
        class C(unittest.TestCase):
            @unittest.skip('inert DATA')
            def test_required(self): pass
        s=unittest.defaultTestLoader.loadTestsFromTestCase(C)
        self.assertFalse(self.check(s,[C('test_required').id()])['PASS'])

    def test_missing_or_extra_id_fails(self):
        s=unittest.TestSuite([unittest.FunctionTestCase(lambda: None)])
        self.assertFalse(self.check(s,['missing'])['PASS'])

    def test_empty_suite_cannot_fill_expected_roster(self):
        self.assertFalse(self.check(unittest.TestSuite(),['missing'])['PASS'])

    def test_real_complete_case_passes(self):
        t=unittest.FunctionTestCase(lambda: None)
        self.assertTrue(self.check(unittest.TestSuite([t]),[t.id()])['PASS'])
