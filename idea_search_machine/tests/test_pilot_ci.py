import tempfile
import unittest
from pathlib import Path
from idea_search_machine.pilot_ci import run_suite


class CIContractTests(unittest.TestCase):
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
