"""Inert DATA consumer regressions, separate from the nine bootstrap tests."""
from pathlib import Path
import tempfile
import unittest
import ci_runner as ci


class RunnerTests(unittest.TestCase):
    def good(self):
        return dict(schema='solver-dag-bootstrap-v1',count=9,ids=list(ci.BOOTSTRAP_IDS),
                    successes=list(ci.BOOTSTRAP_IDS),skipped=[],failures=[],errors=[],
                    expected_failures=[],unexpected_successes=[])

    def test_complete_nine_accepted(self):
        ci.validate_bootstrap(self.good())

    def test_skipped_rejected(self):
        r=self.good();r['skipped']=[[r['ids'][0],'inert skip']]
        with self.assertRaises(ValueError):ci.validate_bootstrap(r)

    def test_missing_test_rejected(self):
        r=self.good();r['count']=8;r['ids'].pop();r['successes'].pop()
        with self.assertRaises(ValueError):ci.validate_bootstrap(r)

    def test_extra_test_rejected(self):
        r=self.good();r['count']=10;r['ids'].append('extra');r['successes'].append('extra')
        with self.assertRaises(ValueError):ci.validate_bootstrap(r)

    def test_duplicate_test_rejected(self):
        r=self.good();r['ids'][-1]=r['ids'][0]
        with self.assertRaises(ValueError):ci.validate_bootstrap(r)

    def test_missing_result_rejected(self):
        with self.assertRaises(ValueError):ci.validate_bootstrap(None)

    def test_missing_field_rejected(self):
        r=self.good();del r['errors']
        with self.assertRaises(ValueError):ci.validate_bootstrap(r)

    def test_failure_and_error_rejected(self):
        for field in ['failures','errors','expected_failures','unexpected_successes']:
            with self.subTest(field=field):
                r=self.good();r[field]=['inert DATA failure']
                with self.assertRaises(ValueError):ci.validate_bootstrap(r)

    def test_false_success_or_boolean_count_rejected(self):
        for field,value in [('successes',[]),('count',True)]:
            with self.subTest(field=field):
                r=self.good();r[field]=value
                with self.assertRaises(ValueError):ci.validate_bootstrap(r)

    def component(self):
        return dict(status='CONDITIONAL_SOLVER_TO_DAG_KERNEL_CHECKED',
                    module_order=sorted(ci.EXPECTED_MODULES),direct_roots=['inert-root'],
                    full_bridge_complete=True,source_rows=[dict(module=n,bytes=1,sha256='0'*64)
                        for n in sorted(ci.EXPECTED_MODULES)])

    def test_component_nonzero_or_missing_rejected(self):
        with self.assertRaises(ValueError):ci.validate_component(self.component(),1)
        with self.assertRaises(ValueError):ci.validate_component(None,0)

    def test_component_wrong_modules_or_missing_roots_rejected(self):
        for field,value in [('module_order',[]),('direct_roots',[]),('source_rows',[]),('full_bridge_complete',False)]:
            with self.subTest(field=field):
                r=self.component();r[field]=value
                with self.assertRaises(ValueError):ci.validate_component(r,0)

    def test_component_complete_accepted_as_data(self):
        # Shape check only; this synthetic row is NOT a compiler receipt.
        ci.validate_component(self.component(),0)

    def test_zero_exit_missing_physical_result_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            a=Path(td);(a/'.lake/conditional-check/runs/one').mkdir(parents=True)
            with self.assertRaisesRegex(ValueError,'COMPONENT_RESULT.json missing'):
                ci.consume_check(a,0)

    def test_zero_exit_malformed_physical_result_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            a=Path(td);r=a/'.lake/conditional-check/runs/one';r.mkdir(parents=True)
            (r/'COMPONENT_RESULT.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'incomplete component status'):
                ci.consume_check(a,0)


if __name__=='__main__':unittest.main()
