import Lean

/- Monomorphic checked lookup for this local FullIngress rollout, not a sandbox
   or a universal private-name/portability/complexity guarantee.
   Kind tags: 0 inductive, 1 constructor, 2 definition, 3 theorem. -/
open Lean Elab Command Term Meta
namespace PartAPrivateLookupCore

def reference (owner user : Name) : TSyntax `term :=
  let n := mkPrivateNameCore owner user
  ⟨.ident .none (toString n).toSubstring n [.decl n []]⟩

def checkExact (n expectedOwner : Name) (kind : Nat) (expected : Syntax) : TermElabM Name := do
  let env ← getEnv
  let some ci := env.find? n | throwError "control/missing"
  unless ci.name == n do throwError "control/identity"
  let kindOK := match kind, ci with
    | 0, .inductInfo _ => true | 1, .ctorInfo _ => true
    | 2, .defnInfo _ => true | 3, .thmInfo _ => true | _, _ => false
  unless kindOK do throwError "control/kind"
  let some i := env.getModuleIdxFor? n | throwError "control/owner"
  unless env.header.moduleNames[i]! == expectedOwner do throwError "control/owner"
  unless ci.levelParams.isEmpty do throwError "control/universes"
  let rawType ← elabType expected
  synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars rawType
  if ty.hasMVar || ty.hasLevelMVar || ty.hasFVar then throwError "control/open-type"
  unless ← isDefEq ci.type ty do throwError "control/type"
  logInfo m!"lookup-checked|{n}|owner={expectedOwner}|kind={kind}|closed-full-type=checked"
  return n

def installChecked (rows : List (Name × Name × Name × Nat × Syntax × Name)) : CommandElabM Unit := do
  let validated ← liftTermElabM do
    rows.mapM fun (encodedOwner, user, owner, kind, ty, aliasName) => do
      return (← checkExact (mkPrivateNameCore encodedOwner user) owner kind ty, aliasName)
  -- References above are syntax only. No alias is installed before ALL rows pass.
  for (n, aliasName) in validated do
    unless aliasName.isAnonymous do
      modifyScope fun st => {st with openDecls := .explicit aliasName n :: st.openDecls}

#check (reference : Name → Name → TSyntax `term)
#check (checkExact : Name → Name → Nat → Syntax → TermElabM Name)
#check (installChecked : List (Name × Name × Name × Nat × Syntax × Name) → CommandElabM Unit)
#print axioms reference
#print axioms checkExact
#print axioms installChecked
end PartAPrivateLookupCore
