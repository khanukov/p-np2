import Complexity.PrivateInterfaceLookupResolvedControl
open Lean Elab Tactic Command
namespace PartAPrivateSuffixFrontier
/- Current-module theorem ownership is not an imported ModuleIdx. The SDK defines
   isImportedConst by that index's presence. No environment/header is modified. -/
def currentTheorem (env : Environment) (owner user : Name) : Except String Name := do
  unless env.mainModule == owner do throw "suffix/current-owner"
  let n := mkPrivateNameCore owner user
  let some ci := env.find? n | throw "suffix/current-missing"
  unless ci.name == n do throw "suffix/current-name"
  unless env.getModuleIdxFor? n == none do throw "suffix/current-imported"
  match ci with
  | .thmInfo info => unless info.levelParams == [] do throw "suffix/current-universes"
  | _ => throw "suffix/current-kind"
  return n
private def contracts : List (Name × Name × String) := [
  (`Cursor.Machine, `Cursor.program, "definition"),
  (`Cursor.Machine, `Cursor.before0, "definition"),
  (`Cursor.Machine, `Cursor.before1, "definition"),
  (`Cursor.Machine, `Cursor.before, "definition"),
  (`Cursor.Machine, `Cursor.decode, "definition"),
  (`Cursor.Proof, `Cursor.er, "definition"),
  (`Cursor.Proof, `Cursor.exits, "definition"),
  (`Cursor.Proof, `Cursor.old_inert, "theorem"),
  (`Cursor.Proof, `Cursor.raw_row, "theorem"),
  (`Cursor.Proof, `Cursor.er_initial, "theorem"),
  (`Cursor.Proof, `Cursor.er_val, "theorem"),
  (`AllArityCursor.Runtime, `AllArityCursor.er, "definition"),
  (`AllArityCursor.Runtime, `AllArityCursor.exits, "definition"),
  (`AllArityCursor.Runtime, `AllArityCursor.old_inert, "theorem"),
  (`AllArityCursor.Runtime, `AllArityCursor.raw_row, "theorem"),
  (`AllArityCursor.Runtime, `AllArityCursor.er_initial, "theorem"),
  (`AllArityCursor.Runtime, `AllArityCursor.map_er, "theorem"),
  (`Stream.Kernel, `Stream.install_exact, "theorem"),
  (`BodyIngress.Machine, `BodyIngress.rows, "definition"),
  (`BodyIngress.Machine, `BodyIngress.extend, "definition"),
  (`BodyIngress.Machine, `BodyIngress.liftOld, "definition"),
  (`CarryReadyCompletion.Native, `CarryReadyCompletion.ready_stays, "theorem")
]
def lookup (env : Environment) (owner user : Name) : Except String Name := do
  if owner == `SuffixCap.Rows && user == `SuffixCap.pin_68_0 && env.mainModule == owner then
    return ← currentTheorem env owner user
  let some (_,_,kind) := contracts.find? (fun r => r.1 == owner && r.2.1 == user)
    | throw "suffix/domain"
  PartAPrivateControl.resolve env owner user owner kind []
def batch (env : Environment) (requests : List (Name × Name)) : Except String (List Name) :=
  requests.mapM fun (o,u) => lookup env o u
def select (owner user : Name) : TacticM Name := do
  match lookup (← getEnv) owner user with
  | .ok n => return n
  | .error e => throwError "{e}"
def selectBatch (requests : List (Name × Name)) : TacticM (List Name) := do
  match batch (← getEnv) requests with
  | .ok ns => return ns
  | .error e => throwError "{e}"
#check (currentTheorem : Environment → Name → Name → Except String Name)
#check (contracts : List (Name × Name × String))
#check (lookup : Environment → Name → Name → Except String Name)
#check (batch : Environment → List (Name × Name) → Except String (List Name))
#check (select : Name → Name → TacticM Name)
#check (selectBatch : List (Name × Name) → TacticM (List Name))
#print axioms currentTheorem
#print axioms contracts
#print axioms lookup
#print axioms batch
#print axioms select
#print axioms selectBatch
end PartAPrivateSuffixFrontier
