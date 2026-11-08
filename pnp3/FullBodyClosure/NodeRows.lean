import FullBodyClosure.Control
import FullBodyClosure.Operand
namespace FullBodyClosure
open Lean Elab Tactic in
private def checkedFrom (owner : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong owner: {name}"
  logInfo m!"node-row-adapter|{name}|{ci.type}"
  closeMainGoal `checkedFrom (mkConst name (ci.levelParams.map Level.param))
private abbrev constState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Control "constState"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Return "returnState"
private def second (b : Bool) : Fin 9 := if b then 2 else 1
private def third (a b : Bool) : Fin 9 := if a then if b then 6 else 5 else if b then 4 else 3
section LiteralRows
set_option maxRecDepth 4000
private theorem first_row (b : Bool) (m : Fin 3) :
    SerializedBody.machine.step (SerializedBodyRefinement.getExit 0 b m) none=
      (SerializedBodyRefinement.getEntry (second b) m,none,.stay) := by
  cases b <;> fin_cases m <;> rfl
private theorem second_row (a b : Bool) (m : Fin 3) :
    SerializedBody.machine.step (SerializedBodyRefinement.getExit (second a) b m) none=
      (SerializedBodyRefinement.getEntry (third a b) m,none,.stay) := by
  cases a <;> cases b <;> fin_cases m <;> rfl
private theorem const_row (m : Fin 3) :
    SerializedBody.machine.step (constState m) none=(SerializedBodyRefinement.getEntry 7 m,none,.stay) := by
  fin_cases m <;> rfl
end LiteralRows
private theorem const_exit (b : Bool) (m : Fin 3) :
    SerializedBodyRefinement.getExit 7 b m=returnState m b := by
  cases b <;> fin_cases m <;> rfl
private theorem get_exit_safe (s : Fin 9) (b : Bool) (m : Fin 3) :
    4 ≤ (SerializedBodyRefinement.getExit s b m).val := by
  fin_cases s <;> cases b <;> fin_cases m <;> decide
private theorem const_safe (m : Fin 3) : 4 ≤ (constState m).val := by fin_cases m <;> decide
end FullBodyClosure
