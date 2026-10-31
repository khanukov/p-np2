"""Finite workbench tests. Generic validator tests do not prove R."""
import importlib.util
import json
from pathlib import Path
import uuid
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("workbench",ROOT/"tools/workbench.py")
workbench=importlib.util.module_from_spec(spec)
spec.loader.exec_module(workbench)

class WorkbenchTests(unittest.TestCase):
 def test_names(self):
  self.assertEqual(workbench.name("Attempt.lower_bound"),"Attempt.lower_bound")
  for n in ["", "a; axiom", "x\nimport Evil", "..", "A.(B)"]:
   with self.assertRaises(ValueError):workbench.name(n)
 def test_source_tokens(self):
  self.assertEqual(workbench.forbidden('-- sorry\n/- axiom /- unsafe -/ -/ def x := "admit"'),[])
  for token in ["axiom", "sorry", "admit", "native_decide", "unsafe"]:
   self.assertIn(token,workbench.forbidden(token+" x"))
 def test_closed_type_guard(self):
  s=workbench.guard_source("Attempt.lower_bound","ConditionalSeparation.OpenProblem.R")
  self.assertIn("info.type",s)
  self.assertIn("isDefEq",s)
  self.assertIn("collectAxioms",s)
  self.assertIn("missing closed proof",s)
 def test_guard_is_bound_to_installed_api(self):
  s=workbench.guard_source("Attempt.lower_bound","ConditionalSeparation.OpenProblem.R")
  self.assertTrue(s.startswith("import ConditionalSeparation.OpenProblem\nimport Attempt\n"))
  self.assertIn("getModuleIdxFor?",s)
  self.assertIn("installed R owner identity",s)
  self.assertNotIn("import ",workbench.guard_body("Attempt.lower_bound","True"))
 def test_template_is_partial(self):
  s=(ROOT/"template/Attempt.lean").read_text()
  self.assertNotIn("theorem",s)
  self.assertEqual(workbench.forbidden(s),[])
 def test_external_attempt(self):
  p=ROOT/".lake/unit-fixtures"/str(uuid.uuid4())/"independent"
  workbench.create(p,ROOT)
  self.assertTrue((p/"Attempt.lean").is_file())
  self.assertIn(json.dumps(str(ROOT.resolve()), ensure_ascii=False), (p/"lakefile.lean").read_text())
  self.assertNotIn("../..",(p/"lakefile.lean").read_text())

if __name__=="__main__":unittest.main()
