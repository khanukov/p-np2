import unittest
from idea_search_machine import registry
from idea_search_machine.tools.extract_routes import live_routes_excerpt


class CurrentContextTests(unittest.TestCase):
    def test_primary_routes_survive_context_bound(self):
        text = live_routes_excerpt(max_chars=4000)
        for name in ('ConditionalSeparation.OpenProblem.R',
                     'Research.LengthwiseSearch.LengthwiseR',
                     'Research.SolverToDag.LowerBound.TreeMCSPDAGLowerBound'):
            self.assertIn(name, text)
        self.assertLessEqual(len(text), 4000)

    def test_old_closed_audit_is_not_formal_refutation(self):
        idea = registry.Idea.from_dict(dict(id='old', created_at='past',
            final_verdict='CLOSED_AT_STAGE_4'))
        self.assertEqual(idea.to_dict().get('formal_outcomes'), {})
        self.assertEqual(idea.final_verdict, 'CLOSED_AT_STAGE_4')


if __name__ == '__main__':
    unittest.main()
