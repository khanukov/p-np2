"""Finite DATA seams. Kernel integration is a separate no-skip command."""
import json
import tempfile
import unittest
import sys
from unittest import mock
from pathlib import Path

from research.idea_lean_pilot import kernel
from research.idea_lean_pilot import backend


class GoalContractTests(unittest.TestCase):
    def test_candidate_cannot_replace_target_or_add_assumptions(self):
        for text in ('exact True.intro\ntheorem extra : True := True.intro',
                     'import Fake', 'axiom bad : False',
                     'macro "IdeaPilotGoal.statement" : term => `(True)',
                     'run_tac trivial'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                kernel.proof_body(text)

    def test_actual_tactic_body_is_preserved(self):
        self.assertEqual(kernel.proof_body('intro n\nexact Nat.le_refl n'),
                         'intro n\nexact Nat.le_refl n')

    def test_receipt_not_exit_or_text_certification(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'fake.json'
            p.write_text(json.dumps({'status': 'PROVED', 'OS_exit': 0}))
            with self.assertRaises(ValueError):
                kernel.verify_outcome(p, '0'*64, '1'*64)

    def test_provider_cwd_is_owned_output(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'provider'
            code = ('import json,sys; from pathlib import Path; '
                    'Path(sys.argv[2]).write_text(json.dumps({"proof":"exact True.intro"})); '
                    'Path("cwd.marker").write_text(str(Path.cwd()))')
            body, receipt = backend.generate({'kind':'DATA','seconds':3,
                'argv':[sys.executable,'-B','-c',code]}, {}, p)
            self.assertEqual(receipt['OS_exit'], 0)
            self.assertTrue((p/'cwd.marker').is_file(), 'provider actually ran outside recorded cwd')
            self.assertEqual((p/'cwd.marker').read_text(), str(p))

    def test_missing_response_is_not_success(self):
        with tempfile.TemporaryDirectory() as d:
            body, r = backend.generate({'kind':'DATA','seconds':2,
                'argv':[sys.executable,'-B','-c','pass']}, {}, Path(d)/'out')
            self.assertEqual(r['OS_exit'], 0)
            self.assertTrue(r['waited'])
            self.assertIsNone(body)

    def test_signal_error_still_reaps_real_finite_child(self):
        # Owned inert child naturally terminates just after the one-second budget.
        # Injected signalling error is DATA; no arbitrary process is signalled.
        with tempfile.TemporaryDirectory() as d, mock.patch.object(
                backend.os, 'killpg', side_effect=PermissionError('DATA signal seam')):
            body, r = backend.generate({'kind':'DATA','seconds':1,
                'argv':[sys.executable,'-B','-c','import time; time.sleep(1.1)']}, {}, Path(d)/'out')
            self.assertTrue(r['waited'])
            self.assertEqual(r['OS_exit'], 0)
            self.assertTrue(r['cleanup_errors'])
            self.assertIsNone(body)

    def test_no_shell_command_string(self):
        with self.assertRaises(ValueError):
            backend.config({'kind':'command','seconds':1,'argv':'echo bad'})

    def test_native_configuration_is_explicit(self):
        with self.assertRaises(ValueError):
            backend.config({'kind':'codex','seconds':1,'model':'unspecified'})

    def test_fake_core_rejected_before_import_marker(self):
        with tempfile.TemporaryDirectory() as d:
            core = Path(d)/'core'
            (core/'tools').mkdir(parents=True)
            marker = Path(d)/'marker'
            (core/'tools/workbench.py').write_text(f'open({str(marker)!r},"w").write("executed")')
            (core/'PACKAGE_FILES.json').write_text('{}')
            with self.assertRaises(ValueError):
                kernel.load_core(core)
            self.assertFalse(marker.exists())

    def test_context_failure_is_unknown_before_any_provider(self):
        from research.idea_lean_pilot import pilot
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'bad-goal.json';p.write_text('{}')
            for i in range(2):
                result=pilot.run(p,'0'*64,{'kind':'DATA','seconds':1,
                    'argv':['MUST_NOT_RUN']},Path(d)/f'run-{i}',calls=1)
                self.assertEqual(result['status'],'UNKNOWN')
                self.assertEqual(result['candidate_calls'],0)
                self.assertEqual(result['compiler_calls'],0)
                self.assertIn('external goal hash',result['technical_reason'])

    def test_primary_context_bound_cannot_silently_drop_routes(self):
        from idea_search_machine.tools.extract_routes import live_routes_excerpt
        with self.assertRaises(ValueError):
            live_routes_excerpt(max_chars=100)

    def test_frozen_json_or_target_change_is_detected(self):
        # DATA manifest seam: this only tests custody, never authorizes a kernel run.
        import shutil
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            spec = dict(name='DATA',statement='True',imports=['ConditionalSeparation.OpenProblem'],model='DATA',role='DATA')
            target = d/'TARGET.lean'
            target.write_text(kernel.goal_source(spec))
            document = dict(schema='idea-pilot-frozen-goal-v1',spec=spec,
                core_identity=[],target=kernel.pin(target),adapter=kernel.pin(kernel.__file__),
                probe_controls=kernel.runtime_controls(),
                compiler=kernel.pin(Path(shutil.which('lean')).resolve()),
                lake=kernel.pin(Path(shutil.which('lake')).resolve()))
            path = d/'GOAL.json'
            kernel.write(path,document)
            sha = kernel.pin(path)['sha256']
            kernel.frozen(path,sha)
            target.write_text('import Fake\ndef statement : Prop := True')
            with self.assertRaises(ValueError):
                kernel.frozen(path,sha)
            path.write_text('{}')
            with self.assertRaises(ValueError):
                kernel.frozen(path,sha)


class CLIContractTests(unittest.TestCase):
    def test_old_red_record_can_probe_and_unknown_can_retry(self):
        import contextlib
        import io
        from idea_search_machine import registry
        from research.idea_lean_pilot import pilot
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            with mock.patch.multiple(registry,REGISTRY_DIR=root/'registry',
                    IDEAS_DIR=root/'registry/ideas',INDEX_FILE=root/'registry/index.jsonl'):
                idea = registry.Idea(id='old',created_at='past',thesis='DATA',final_verdict='CLOSED_AT_STAGE_4')
                registry.save_idea(idea)
                goal = root/'goal.json'; goal.write_text('{}')
                provider = root/'provider.json'; provider.write_text('{}')
                def seam(g, sha, cfg, output, **kw):
                    output.mkdir()
                    kernel.write(output/'RUN.json', {'status':'UNKNOWN','DATA_seam':True})
                    return dict(status='UNKNOWN',technical_reason='DATA budget',candidate_calls=0,compiler_calls=0)
                with mock.patch.object(pilot,'run',side_effect=seam) as call:
                    for i in range(2):
                        args = ['probe','--idea-id','old','--registry',str(root/'registry'),'--goal',str(goal),
                            '--goal-sha256','1'*64,'--provider',str(provider),'--output',str(root/f'run-{i}')]
                        with mock.patch.object(sys,'argv',['probe']+args), contextlib.redirect_stdout(io.StringIO()) as out:
                            pilot.main()
                        self.assertEqual(json.loads(out.getvalue())['status'],'UNKNOWN')
                    self.assertEqual(call.call_count,2)
                saved = registry.load_idea('old')
                self.assertEqual(saved.final_verdict,'CLOSED_AT_STAGE_4')
                self.assertEqual(saved.formal_outcomes['1'*64]['status'],'UNKNOWN')


if __name__ == '__main__':
    unittest.main()
