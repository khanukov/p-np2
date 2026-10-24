import Lean

/-! Infrastructure tooling for explicit typed links to unchanged private owners.
This elaborator returns exactly one already imported constant. It does not infer
or manufacture a theorem proposition, alter an owner, or add mathematical advice.
A future use requires a separate literal expected type. This prefix has no
partA_private% call site: its five helper pins check declaration types, and do not
establish execution/usability for a private case or approval of other families. -/
namespace PartACanonical
open Lean Elab Term Meta
set_option autoImplicit false

def privateNameFromString (text : String) : Name :=
  (text.splitOn ".").foldl (fun name part =>
    match part.toNat? with
    | some value => .num name value
    | none => .str name part) .anonymous

syntax (name := privateABI) "partA_private% " str " owner% " str : term

@[term_elab privateABI]
def elaboratePrivateABI : TermElab := fun stx _expectedType => do
  let `(partA_private% $fqn:str owner% $owner:str) := stx
    | throwUnsupportedSyntax
  let text := fqn.getString
  let name := privateNameFromString text
  unless isPrivateName name && name.toString == text do
    throwErrorAt fqn "Expected an exact round-tripping private FQN"
  let env ← getEnv
  let some index := env.getModuleIdxFor? name
    | throwErrorAt fqn "Private ABI constant has no actual imported owner"
  unless env.header.moduleNames[index]!.toString == owner.getString do
    throwErrorAt owner "Private ABI owner mismatch for {name}"
  let info ← getConstInfo name
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  return mkConst name levels

end PartACanonical
