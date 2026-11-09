"""DATA capture of the real pilot -> native argv/request-stdin seam; no model/Lean."""
import contextlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock
from . import backend, kernel as K, pilot


@contextlib.contextmanager
def captured_run(root, *, statement='∀ n : Nat, n = n', feedback='DATA compiler failure', real_stdin=False):
    core = root/'core'
    for relative in ('ConditionalSeparation/OpenProblem.lean', 'core/Complexity/DagCompose.lean'):
        p = core/relative
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text('-- inert DATA source, not an admitted core\n')
    target = root/'TARGET.lean'
    target.write_text('-- inert DATA target\n')
    goal = root/'GOAL.json'
    goal.write_text('{}')
    document = dict(core=str(core), target=K.pin(target), spec=dict(statement=statement,
        imports=['ConditionalSeparation.OpenProblem', 'Complexity.DagCompose'],
        model='DATA exact model', role='DATA helper'))
    captures = []
    owned = backend.owned_command
    def validate(g, sha, out):
        out.mkdir()
        K.write(out/'VALIDATED.json', {'DATA': True})
        K.write(out/'DEPENDENCIES.json', {'files': []})
    def transport(argv, out, seconds, receipt):
        # The real native transport opens THIS exact request.json as stdin.
        raw = (out/'request.json').read_bytes()
        captures.append((argv, raw, json.loads(raw)))
        if real_stdin:
            code = ('import sys,json;from pathlib import Path;'
                    'Path("captured-stdin.json").write_bytes(sys.stdin.buffer.read());'
                    'Path("response.json").write_text(json.dumps({"proof":"rfl"}))')
            actual = [sys.executable, '-B', '-c', code]
            receipt.update(DATA_requested_argv=argv, argv=actual, DATA_intercept=True,
                           kind='DATA_native_argv_intercept')
            owned(actual, out, seconds, receipt)
            return
        K.write(out/'response.json', {'proof': 'rfl'})
        (out/'stdout.txt').write_text('')
        (out/'stderr.txt').write_text('')
        receipt.update(OS_exit=0, waited=True, timeout=False, DATA_intercept=True)
    def evaluate(g, sha, body, polarity, out):
        out.mkdir()
        result = dict(status='UNKNOWN', technical_reason=feedback, DATA_intercept=True)
        K.write(out/'RESULT.json', result)
        return result
    with mock.patch.object(K, 'frozen', return_value=document), \
         mock.patch.object(K, 'validate_goal', side_effect=validate), \
         mock.patch.object(K, 'evaluate', side_effect=evaluate), \
         mock.patch.object(K, 'verify_outcome'), \
         mock.patch.object(backend, 'owned_command', side_effect=transport):
        yield document, goal, captures


class NativeRequestTests(unittest.TestCase):
    def test_current_cohort_both_arms_fit_with_real_source_references(self):
        here = Path(__file__).resolve().parent
        cohort = K.read(here/'cohort.json')
        for i, spec in enumerate(cohort):
            for mode in ('direct', 'integrated'):
                with self.subTest(goal=i, mode=mode), tempfile.TemporaryDirectory() as d:
                    root = Path(d)
                    with captured_run(root) as (goal, path, captures):
                        goal.update(spec=spec, core=str(here.parents[1]/'conditional_separation'))
                        result = pilot.run(path, K.pin(path)['sha256'], dict(kind='codex',
                            model='gpt-6.1-sol', effort='xhigh', seconds=1), root/'run', calls=1, mode=mode)
                    self.assertEqual(result['candidate_calls'], 1, result['technical_reason'])
                    _, raw, request = captures[0]
                    self.assertLessEqual(len(raw), 9000)
                    self.assertEqual(request['statement'], spec['statement'])
                    self.assertEqual(request['model'], spec['model'])
                    self.assertEqual(request['research_role'], spec['role'])
                    self.assertTrue(all(Path(p['path']).is_file() for p in request['read_scope']['sources']))

    def test_real_native_request_has_exact_read_scope_and_frozen_inputs(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            with captured_run(root) as (goal, path, captures):
                result = pilot.run(path, K.pin(path)['sha256'], dict(kind='codex',
                    model='gpt-6.1-sol', effort='xhigh', seconds=1), root/'run',
                    calls=1, mode='direct')
            self.assertEqual(result['candidate_calls'], 1)
            argv, raw, request = captures[0]
            self.assertEqual(argv[:4], ['codex', 'exec', '--model', 'gpt-6.1-sol'])
            self.assertEqual(argv[-1], '-')
            self.assertIn('read_scope', request, 'native request omits usable admitted source scope')
            scope = request['read_scope']
            self.assertEqual(scope['installed_core'], goal['core'])
            self.assertEqual(scope['frozen_goal']['path'], str(path))
            self.assertEqual(scope['target'], goal['target'])
            self.assertTrue(Path(scope['validation']['path']).is_file())
            sources = {row['path'] for row in scope['sources']}
            self.assertIn(str(root/'core/core/Complexity/DagCompose.lean'), sources)
            self.assertIn(str(root/'core/ConditionalSeparation/OpenProblem.lean'), sources)
            self.assertEqual(request['statement'], goal['spec']['statement'])
            self.assertEqual(request['imports'], goal['spec']['imports'])
            self.assertLessEqual(len(raw), 9000)

    def test_unicode_feedback_bound_preserves_whole_required_context(self):
        from idea_search_machine.tools.extract_routes import current_context
        statement = '∀ n : Nat, n = n -- exact hypotheses αβγ'
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            with captured_run(root, statement=statement, feedback='λ🙂\\\"\n'*12000) as (_, path, captures):
                result = pilot.run(path, K.pin(path)['sha256'], dict(kind='codex',
                    model='gpt-6.1-sol', effort='xhigh', seconds=1), root/'run', calls=2)
            self.assertEqual(result['candidate_calls'], 2)
            for _, raw, request in captures:
                self.assertLessEqual(len(raw), 9000)
                self.assertEqual(request['statement'], statement)
                self.assertEqual(request['route_context'], current_context())
                self.assertEqual(request['imports'], ['ConditionalSeparation.OpenProblem', 'Complexity.DagCompose'])
                self.assertIn('OUTER loop', request['instructions'])
                self.assertIn('Do not search /root', request['instructions'])
            self.assertTrue(captures[1][2]['feedback_truncated'])

    def test_required_overflow_is_unknown_without_provider(self):
        for field in ('statement', 'primary'):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                text = '∀ n : Nat, n = n' if field == 'primary' else 'λ'*9001
                from idea_search_machine.tools import extract_routes
                with captured_run(root, statement=text) as (_, path, captures), \
                     mock.patch.object(extract_routes, 'current_context', return_value='λ'*9001 if field == 'primary' else 'primary'):
                    result = pilot.run(path, K.pin(path)['sha256'], dict(kind='codex',
                        model='gpt-6.1-sol', effort='xhigh', seconds=1), root/'run', calls=1)
                self.assertEqual(result['status'], 'UNKNOWN')
                self.assertIn('required candidate context exceeds', result['technical_reason'])
                self.assertEqual(result['candidate_calls'], 0)
                self.assertEqual(captures, [])

    def test_backend_rejects_oversized_serialized_input_before_spawn(self):
        with tempfile.TemporaryDirectory() as d, mock.patch.object(backend, 'owned_command') as spawn:
            with self.assertRaisesRegex(ValueError, '9000 UTF-8 bytes'):
                backend.generate(dict(kind='codex', model='gpt-6.1-sol', effort='xhigh', seconds=1),
                                 {'statement': '🙂'*9000}, Path(d)/'provider')
            spawn.assert_not_called()
            self.assertFalse((Path(d)/'provider').exists())

    def test_actual_inert_child_reads_exact_native_stdin_bytes(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            with captured_run(root, real_stdin=True) as (_, path, captures):
                result = pilot.run(path, K.pin(path)['sha256'], dict(kind='codex',
                    model='gpt-6.1-sol', effort='xhigh', seconds=3), root/'run', calls=1)
            provider = root/'run/candidate-00'
            self.assertEqual((provider/'captured-stdin.json').read_bytes(), captures[0][1])
            receipt = K.read(provider/'PROVIDER.json')
            self.assertEqual(receipt['OS_exit'], 0)
            self.assertTrue(receipt['waited'])
            self.assertEqual(receipt['kind'], 'DATA_native_argv_intercept')
            self.assertEqual(receipt['argv'][0], sys.executable)
            self.assertEqual(receipt['DATA_requested_argv'][0], 'codex')
            self.assertEqual(result['status'], 'UNKNOWN')  # no Lean ran

    def test_compare_reports_prove_only_and_probe_negation_remains_separate(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            def run(g, sha, cfg, out, **kw):
                out.mkdir()
                K.write(out/'RUN.json', {'DATA': True})
                return dict(status='UNKNOWN', elapsed_seconds=0, candidate_calls=0, compiler_calls=0)
            with mock.patch.object(pilot, 'run', side_effect=run) as call:
                result = pilot.compare([dict(path='DATA', sha256='0'*64)], {}, root/'compare', 2)
                self.assertEqual(result['branches'], ['prove'])
                self.assertFalse(result['optional_negation_exercised'])
                self.assertEqual([c.kwargs['mode'] for c in call.call_args_list], ['direct', 'integrated'])
                self.assertTrue(all(not c.kwargs.get('negate', False) for c in call.call_args_list))
            with captured_run(root) as (_, path, captures):
                pilot.run(path, K.pin(path)['sha256'], dict(kind='codex', model='gpt-6.1-sol',
                    effort='xhigh', seconds=1), root/'negate', calls=2, negate=True)
            self.assertEqual([c[2]['polarity'] for c in captures], ['prove', 'refute'])


class ProviderReceiptTests(unittest.TestCase):
    def assert_final_receipt(self, output, returned):
        # The caller's existing PROVIDER pin must bind the same final object.
        anchor = K.pin(output/'PROVIDER.json')
        self.assertEqual(K.read(anchor['path']), returned)
        self.assertNotIn('PROVIDER.json', [Path(r['path']).name for r in returned['files']])
        for row in returned['files']:
            K.match(row)

    def test_malformed_response_rejection_is_in_actual_persisted_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/'provider'
            body, receipt = backend.generate(dict(kind='DATA', seconds=3, argv=[sys.executable,
                '-B', '-c', 'import sys;from pathlib import Path;Path(sys.argv[2]).write_text("not-json")']),
                {}, output)
            self.assertIsNone(body)
            self.assertTrue(receipt['waited'])
            self.assertEqual(receipt['OS_exit'], 0)
            saved = K.read(output/'PROVIDER.json')
            self.assertIn('JSONDecodeError', saved.get('response_error', ''),
                          'persisted receipt omits real response rejection')
            self.assertEqual(K.read(output/'RESPONSE_REJECTED.json')['reason'], saved['response_error'])
            self.assertIn('RESPONSE_REJECTED.json', [Path(r['path']).name for r in saved['files']])
            self.assert_final_receipt(output, receipt)

    def test_oversized_response_rejection_is_in_persisted_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/'provider'
            body, receipt = backend.generate(dict(kind='DATA', seconds=3, argv=[sys.executable,
                '-B', '-c', 'import sys;from pathlib import Path;Path(sys.argv[2]).write_text("x"*20001)']),
                {}, output)
            self.assertIsNone(body)
            self.assertEqual(receipt['OS_exit'], 0)
            self.assertIn('response too large', K.read(output/'PROVIDER.json')['response_error'])
            self.assertIn('RESPONSE_REJECTED.json', [Path(r['path']).name for r in receipt['files']])
            self.assert_final_receipt(output, receipt)

    def test_valid_response_has_final_evidence_without_rejection(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/'provider'
            body, receipt = backend.generate(dict(kind='DATA', seconds=3, argv=[sys.executable,
                '-B', '-c', 'import sys,json;from pathlib import Path;Path(sys.argv[2]).write_text(json.dumps({"proof":"rfl"}))']),
                {}, output)
            self.assertEqual(body, 'rfl')  # valid protocol, not a Lean result
            self.assertEqual(receipt['OS_exit'], 0)
            self.assertTrue(receipt['waited'])
            self.assertNotIn('response_error', receipt)
            self.assertFalse((output/'RESPONSE_REJECTED.json').exists())
            self.assertIn('response.json', [Path(r['path']).name for r in receipt['files']])
            self.assert_final_receipt(output, receipt)

    def test_nonzero_transport_preserves_actual_exit_and_final_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/'provider'
            body, receipt = backend.generate(dict(kind='DATA', seconds=3, argv=[sys.executable,
                '-B', '-c', 'import sys,json;from pathlib import Path;Path(sys.argv[2]).write_text(json.dumps({"proof":"rfl"}));sys.exit(7)']),
                {}, output)
            self.assertIsNone(body)
            self.assertEqual(receipt['OS_exit'], 7)
            self.assertTrue(receipt['waited'])
            self.assertFalse(receipt['timeout'])
            self.assertNotIn('response_error', receipt)
            self.assert_final_receipt(output, receipt)

    def test_timeout_transport_preserves_actual_wait_and_final_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/'provider'
            body, receipt = backend.generate(dict(kind='DATA', seconds=1,
                argv=[sys.executable, '-B', '-c', 'import time;time.sleep(3)']), {}, output)
            self.assertIsNone(body)
            self.assertTrue(receipt['timeout'])
            self.assertTrue(receipt['waited'])
            self.assertIsInstance(receipt['OS_exit'], int)
            self.assertNotEqual(receipt['OS_exit'], 0)
            self.assertNotIn('response_error', receipt)
            self.assert_final_receipt(output, receipt)


if __name__ == '__main__':
    unittest.main()
