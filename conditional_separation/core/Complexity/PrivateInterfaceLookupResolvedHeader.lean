import Lean

/- Imported metadata identity only: this API deliberately does not compare types.
   The Bool kind contract is false = definition, true = theorem; all other kinds
   fail. Expected universes are literal names. No cross-environment cache. -/
open Lean Elab Command
namespace PartAPrivateResolved

def resolve (encodedOwner user expectedOwner : Name) (theoremKind : Bool)
    (expectedUniverses : List Name) : CommandElabM Name := do
  let env ← getEnv
  let n := mkPrivateNameCore encodedOwner user
  let some ci := env.find? n | throwError "resolved/missing"
  unless ci.name == n do throwError "resolved/identity"
  let kindOK := match theoremKind, ci with
    | false, .defnInfo _ => true
    | true, .thmInfo _ => true
    | _, _ => false
  unless kindOK do throwError "resolved/kind"
  let some idx := env.getModuleIdxFor? n | throwError "resolved/owner"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "resolved/owner-index"
  unless owner == expectedOwner do throwError "resolved/owner"
  unless ci.levelParams == expectedUniverses do throwError "resolved/universes"
  logInfo m!"resolved-identity|{n}|owner={owner}|theorem={theoremKind}|universes={ci.levelParams}"
  return n

def install (rows : List (Name × Name × Name × Bool × List Name × Name)) : CommandElabM Unit := do
  let validated ← rows.mapM fun (encodedOwner,user,owner,kind,levels,aliasName) => do
    return (← resolve encodedOwner user owner kind levels, aliasName)
  -- No scope change until every row has passed; same ordered scoped explicit opens.
  for (n,aliasName) in validated do
    unless aliasName.isAnonymous do
      modifyScope fun st => {st with openDecls := .explicit aliasName n :: st.openDecls}

#check (resolve : Name → Name → Name → Bool → List Name → CommandElabM Name)
#check (install : List (Name × Name × Name × Bool × List Name × Name) → CommandElabM Unit)
#print axioms resolve
#print axioms install
end PartAPrivateResolved
