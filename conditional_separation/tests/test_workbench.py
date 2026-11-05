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


class LexicalLiteralTests(unittest.TestCase):
 def test_banned_after_character_literals(self):
  literals = ["'\"'", "'"+"\\"+"'"+"'", "'\\\\'", "'a'", "'\u03bb'", "'\\n'", "'\\x22'", "'\\u0022'"]
  declarations = {'axiom':'axiom hidden : True', 'sorry':'theorem hidden : True := by sorry',
   'admit':'theorem hidden : True := by admit', 'native_decide':'theorem hidden : True := by native_decide',
   'unsafe':'unsafe def hidden : Nat := 0'}
  for literal in literals:
   for token, declaration in declarations.items():
    with self.subTest(literal=literal, token=token):
     self.assertEqual(workbench.forbidden('def q : Char := '+literal+'\n'+declaration), [token])
 def test_banned_after_raw_strings(self):
  for literal in ['r"plain"', 'r#"a"b"#', 'r##"a"#b\\c"##', 'r#####"a"####b"#####']:
   for token in ['axiom','sorry','admit','native_decide','unsafe']:
    with self.subTest(literal=literal, token=token):
     self.assertEqual(workbench.forbidden('def q := '+literal+'\n'+token+' hidden'), [token])
 def test_literal_and_comment_contents_are_not_active(self):
  words = 'axiom sorry admit native_decide unsafe'
  texts = ['"'+words+'"', '"a\\\"'+words+'\\\\b"',
   'r#"'+words+' " inside"#', 'r###"'+words+' "## inside"###',
   '-- '+words+'\n', '/- '+words+' /- '+words+' -/ -/',
   "'\"' '\\\\' '\\n'", '-- '+words+'\rdef ok := 0']
  for text in texts:
   with self.subTest(text=text): self.assertEqual(workbench.forbidden(text), [])
   for token in ['axiom','sorry','admit','native_decide','unsafe']:
    with self.subTest(text=text, following=token):
     self.assertEqual(workbench.forbidden(text+' '+token), [token])
 def test_identifier_apostrophes_and_word_boundaries(self):
  for text in ["def x' := 1", "def foo'' := x'", "def \u03b1' := 0", "def axiom' := 0",
   'my_axiom unsafeName sorry2 _admit native_decideX']:
   with self.subTest(text=text): self.assertEqual(workbench.forbidden(text), [])
  self.assertEqual(workbench.forbidden("def x' := 1; unsafe def hidden := 0"), ['unsafe'])
  self.assertEqual(workbench.forbidden('sorry/- gap -/admit'), ['admit','sorry'])
 def test_malformed_literals_fail_closed(self):
  texts = ['"unfinished', '"escape'+"\\", 'r#"unfinished"', 'r###"wrong"##',
   'r##not_a_literal', "'", "''", "'ab'", "'a", "'\\q'", '"\\uD800"',
   '"\\x0"', '/- unfinished /- nested -/']
  for text in texts:
   with self.subTest(text=text):
    with self.assertRaises(ValueError): workbench.forbidden(text+'\nunsafe def hidden := 0')
 def test_matching_raw_delimiter_not_embedded_quote(self):
  self.assertEqual(workbench.forbidden('r###"unsafe "# sorry "## axiom"### admit'), ['admit'])
  self.assertEqual(workbench.forbidden('"escaped \\\" unsafe" native_decide'), ['native_decide'])

if __name__=="__main__":unittest.main()
