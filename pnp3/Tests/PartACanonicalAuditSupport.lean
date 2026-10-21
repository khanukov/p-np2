import Tests.PartACanonicalSupport

/-! Infrastructure: direct axiom inspection of one literal FQN in the invoking
module. The cache stores only an exact environment name index; it supplies no
proofs, proposition types or mathematical premises. -/
open Lean Elab Command
namespace PartACanonical.Audit

private initialize names : IO.Ref (Option (Std.HashMap String Name)) ← IO.mkRef none

def printDirect (text : String) : CommandElabM Unit := do
  let env ← getEnv
  let index ← match ← names.get with
    | some index => pure index
    | none => do
      let mut index : Std.HashMap String Name := {}
      for (name, _) in env.constants.toList do
        if let some previous := index[name.toString]? then
          unless previous == name do throwError "Ambiguous exact FQN {text}"
        index := index.insert name.toString name
      names.set (some index)
      pure index
  let some name := index[text]? | throwError "Missing direct axiom root {text}"
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
