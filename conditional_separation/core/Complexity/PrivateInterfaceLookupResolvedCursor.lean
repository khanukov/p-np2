import Lean

/- Metadata identity only, not independent full-signature validation. The pure
   resolver accepts definitions (including abbreviations), never other kinds.
   The TacticM adapter supports only the literal source-backed Cursor domain. -/
open Lean Elab Tactic
namespace PartAPrivateCursor

def resolveDefinition (env : Environment) (encodedOwner user expectedOwner : Name)
    (expectedUniverses : List Name) : Except String Name := do
  let n := mkPrivateNameCore encodedOwner user
  let some ci := env.find? n | throw "cursor/missing"
  unless ci.name == n do throw "cursor/identity"
  match ci with
  | .defnInfo _ => pure ()
  | _ => throw "cursor/kind"
  let some idx := env.getModuleIdxFor? n | throw "cursor/owner"
  let some owner := env.header.moduleNames[idx.toNat]? | throw "cursor/owner-index"
  unless owner == expectedOwner do throw "cursor/owner"
  unless ci.levelParams == expectedUniverses do throw "cursor/universes"
  return n

private def userName? (key : String) : Option Name :=
  if ["program","decode","before","power","middle","add","after","middle0","add0",
    "before0","before1","before2","before3","before4","before5","before6","before7",
    "before8","before9","before10","before11","power0","power1","power2","power3",
    "after0","after1","after2","after3","after4","after5","after6","after7","after8",
    "after9","after10","after11","after12","after13","after14","after15","after16",
    "after17","after18","after19","after20","after21","after22","after23","after24",
    "after25"].contains key then some (Name.str `Cursor key) else none

def select (key : String) : TacticM Name := do
  let some user := userName? key | throwError "cursor/domain"
  match resolveDefinition (← getEnv) `Cursor.Machine user `Cursor.Machine [] with
  | .ok n => return n
  | .error text => throwError text

#check (resolveDefinition : Environment → Name → Name → Name → List Name → Except String Name)
#check (select : String → TacticM Name)
#check (userName? : String → Option Name)
#print axioms resolveDefinition
#print axioms select
#print axioms userName?
end PartAPrivateCursor
