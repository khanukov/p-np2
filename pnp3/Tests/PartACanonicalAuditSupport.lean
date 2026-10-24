import Tests.PartACanonicalSupport

/-! Infrastructure: direct axiom inspection of one literal FQN in the current
invoking environment. No process-global environment snapshot is retained; this
supplies no proofs, proposition types or mathematical premises. -/
open Lean Elab Command
namespace PartACanonical.Audit

-- Preserve the three previously generated, independently pinned helper ABIs.
-- These explicit eliminators retain no state and are not used for name lookup.
def printDirect.match_1.{u} (motive : Option Name → Sort u) (x : Option Name)
    (someCase : ∀ name, motive (some name))
    (fallback : ∀ value, motive value) : motive x :=
  Option.casesOn (motive := motive) x (fallback none) someCase

def printDirect.match_3.{u} (motive : Name × ConstantInfo → Sort u)
    (x : Name × ConstantInfo)
    (pairCase : ∀ name info, motive (name, info)) : motive x :=
  Prod.casesOn (motive := motive) x pairCase

def printDirect.match_5.{u} (motive : Option (Std.HashMap String Name) → Sort u)
    (x : Option (Std.HashMap String Name))
    (someCase : ∀ index, motive (some index))
    (noneCase : Unit → motive none) : motive x :=
  Option.casesOn (motive := motive) x (noneCase ()) someCase

def printDirect (text : String) : CommandElabM Unit := do
  let env ← getEnv
  let name := text.toName
  unless name.toString == text && env.contains name do
    throwError "Missing or nonexact direct axiom root {text}"
  -- Name.toString is not injective for every internal Name. Fail closed on a
  -- collision of the requested literal, without caching any environment.
  for entry in env.constants.toList do
    let other := entry.1
    if other != name && other.toString == text then
      throwError "Ambiguous exact FQN {text}"
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Nonstandard axiom {axiomName} for direct root {name}"
  let record := Json.mkObj [("name", toJson name.toString),
    ("auditModule", toJson (← getMainModule).toString),
    ("axioms", toJson (axioms.map Name.toString))]
  logInfo m!"PART_A_CANONICAL_AXIOMS|{record.compress}"

syntax (name := directAxioms) "#partA_axioms " str : command
@[command_elab directAxioms] def elaborateDirectAxioms : CommandElab := fun stx => do
  let `(#partA_axioms $text:str) := stx | throwUnsupportedSyntax
  printDirect text.getString

end PartACanonical.Audit
