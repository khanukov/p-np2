import unittest
import tempfile
from pathlib import Path
from unittest import mock
from idea_search_machine import registry
from idea_search_machine.llm import LLMResult
from idea_search_machine.stages import stage3_repo_surface
from idea_search_machine.tools.extract_routes import live_routes_excerpt


class CurrentContextTests(unittest.TestCase):
    def test_stage3_call_retains_late_historical_routes(self):
        # Actual Stage3 prompt/query/registry path, with an inert DATA client.
        client = mock.Mock(spec=['query'])
        client.query.return_value = LLMResult('VERDICT: REPO_YELLOW', 'DATA', True)
        with tempfile.TemporaryDirectory() as d, mock.patch.multiple(registry,
                REGISTRY_DIR=Path(d), IDEAS_DIR=Path(d)/'ideas', INDEX_FILE=Path(d)/'index.jsonl'):
            idea = registry.Idea(id='stage3-DATA', created_at='past', thesis='DATA')
            result = stage3_repo_surface.run(client, idea)
        client.query.assert_called_once()
        prompt = client.query.call_args.args[0]
        for name in (
            'formulaCircuitPublishedLowerBoundContract_of_publishedLocalPRGRoute',
            'PublishedOneSidedLocalPRGRouteContract',
            'PublishedLocalPRGRouteContract',
            'CKLMFormulaCircuitLocalPRGSourceSpec',
            'CKLMFormulaCircuitLocalPRGSourceContract',
        ):
            self.assertIn('`'+name+'`', prompt)
        self.assertEqual(result.verdict, 'REPO_YELLOW')
        self.assertTrue(result.is_mock)

    def test_primary_routes_survive_context_bound(self):
        text = live_routes_excerpt(max_chars=4000)
        for name in ('ConditionalSeparation.OpenProblem.R',
                     'Research.LengthwiseSearch.LengthwiseR',
                     'Research.SolverToDag.LowerBound.TreeMCSPDAGLowerBound'):
            self.assertIn(name, text)
        self.assertLessEqual(len(text), 4000)

    def test_historical_budget_and_small_bounds_are_separate_from_primary(self):
        text = live_routes_excerpt(include_primary=False)
        self.assertLessEqual(len(text), 4000)
        self.assertIn('`CKLMFormulaCircuitLocalPRGSourceContract`', text)
        self.assertEqual(live_routes_excerpt(max_chars=0, include_primary=False), '')
        self.assertLessEqual(len(live_routes_excerpt(max_chars=100, include_primary=False)), 100)
        with self.assertRaises(ValueError):
            live_routes_excerpt(max_chars=-1, include_primary=False)
        with self.assertRaises(ValueError):
            live_routes_excerpt(max_chars=100)

    def test_old_closed_audit_is_not_formal_refutation(self):
        idea = registry.Idea.from_dict(dict(id='old', created_at='past',
            final_verdict='CLOSED_AT_STAGE_4'))
        self.assertEqual(idea.to_dict().get('formal_outcomes'), {})
        self.assertEqual(idea.final_verdict, 'CLOSED_AT_STAGE_4')


if __name__ == '__main__':
    unittest.main()
