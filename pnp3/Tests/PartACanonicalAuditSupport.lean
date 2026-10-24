import Tests.PartACanonicalSupport

/-! Infrastructure: direct axiom inspection of one literal FQN in the current
invoking environment. A batch shares one invocation-local index; no index is
retained across commands or environment replacement. This
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

private abbrev InvocationIndex := Std.HashMap String (List Name)

/-- Exactly one traversal, private to an atomic command invocation. -/
private def indexInvocation (env : Environment) : InvocationIndex × Nat := Id.run do
  let mut index : InvocationIndex := {}
  let mut visited := 0
  for entry in env.constants.toList do
    let name := entry.1
    let text := name.toString
    index := index.insert text (name :: (index[text]?.getD []))
    visited := visited + 1
  return (index, visited)

private def auditIndexed (index : InvocationIndex) (text : String) : CommandElabM Unit := do
  let env ← getEnv
  let name := text.toName
  unless name.toString == text && env.contains name do
    throwError "Missing or nonexact direct axiom root {text}"
  let candidates := index[text]?.getD []
  unless candidates.contains name do
    throwError "Current root absent from invocation index {text}"
  if candidates.any (fun other => other != name) then
    throwError "Ambiguous exact FQN {text}"
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Nonstandard axiom {axiomName} for direct root {name}"
  let record := Json.mkObj [("name", toJson name.toString),
    ("auditModule", toJson (← getMainModule).toString),
    ("axioms", toJson (axioms.map Name.toString))]
  logInfo m!"PART_A_CANONICAL_AXIOMS|{record.compress}"

/-- Audit a finite batch in one immutable command context. No index escapes this
invocation, so the next call rebuilds even for equal-size/same-FQN replacements.
The body only reads the environment: collectAxioms is ReaderT/StateM internally.
The returned counter counts actual visited declarations, not a cache-hit claim. -/
def printDirectBatch (texts : Array String) : CommandElabM Nat := do
  let indexed := indexInvocation (← getEnv)
  for text in texts do auditIndexed indexed.1 text
  let record := Json.mkObj [("auditModule", toJson (← getMainModule).toString),
    ("roots", toJson texts.size), ("visited", toJson indexed.2)]
  logInfo m!"PART_A_AUDIT_INDEX|{record.compress}"
  return indexed.2

def printDirect (text : String) : CommandElabM Unit := do
  discard <| printDirectBatch #[text]

syntax (name := directAxioms) "#partA_axioms " str : command
@[command_elab directAxioms] def elaborateDirectAxioms : CommandElab := fun stx => do
  let `(#partA_axioms $text:str) := stx | throwUnsupportedSyntax
  printDirect text.getString

syntax (name := directAxiomsBatch) "#partA_axioms_batch" "[" str,* "]" : command
@[command_elab directAxiomsBatch]
def elaborateDirectAxiomsBatch : CommandElab := fun stx => do
  let `(#partA_axioms_batch [$texts:str,*]) := stx | throwUnsupportedSyntax
  discard <| printDirectBatch (texts.getElems.map fun text => text.getString)

end PartACanonical.Audit
