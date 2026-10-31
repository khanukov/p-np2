import FullBodyClosure.StackRows
namespace FullBodyClosure
open Lean Elab Tactic in
private def checkedFrom (owner : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let root:=Name.str (Name.num (Name.append `_private owner) 0) "FullBodyClosure"
  let name:=(leaf.splitOn ".").foldl Name.str root
  let some ci:=env.find? name | throwError "Missing exact declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing immutable module: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong owner for {name}"
  logInfo m!"control-adapter|{owner}|{name}|{ci.type}"
  closeMainGoal `checkedFrom (mkConst name (ci.levelParams.map Level.param))
private abbrev st : Nat → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Support "st"
private abbrev pushState : Fin 3 → Fin 7 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.StackRows "pushState"
private abbrev popNextState : Fin 3 → Bool → Fin 7 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.StackRows "popNextState"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Return "returnState"
private def inputState (m : Fin 3) : Fin 7500 := st (#[2226,4842,6943][m.val]!)
private def constState (m : Fin 3) : Fin 7500 := st (#[1507,4133,6266][m.val]!)
private theorem pop_neg (m : Fin 3) (b : Bool) : popNextState m b ⟨0,by decide⟩=returnState m (!b) := by
  fin_cases m <;> cases b <;> rfl
private theorem pop_and_left (m : Fin 3) (b : Bool) :
    popNextState m b ⟨1,by decide⟩=pushState m (if b then ⟨3,by decide⟩ else ⟨2,by decide⟩) := by
  fin_cases m <;> cases b <;> rfl
private theorem pop_and_right_false (m : Fin 3) (b : Bool) :
    popNextState m b ⟨2,by decide⟩=returnState m false := by fin_cases m <;> cases b <;> rfl
private theorem pop_and_right_true (m : Fin 3) (b : Bool) :
    popNextState m b ⟨3,by decide⟩=returnState m b := by fin_cases m <;> cases b <;> rfl
private theorem pop_or_left (m : Fin 3) (b : Bool) :
    popNextState m b ⟨4,by decide⟩=pushState m (if b then ⟨6,by decide⟩ else ⟨5,by decide⟩) := by
  fin_cases m <;> cases b <;> rfl
private theorem pop_or_right_false (m : Fin 3) (b : Bool) :
    popNextState m b ⟨5,by decide⟩=returnState m b := by fin_cases m <;> cases b <;> rfl
private theorem pop_or_right_true (m : Fin 3) (b : Bool) :
    popNextState m b ⟨6,by decide⟩=returnState m true := by fin_cases m <;> cases b <;> rfl
private def tagDestination (m : Fin 3) (b0 b1 b2 : Bool) : Fin 7500 :=
  if b0 then if b1 || b2 then SerializedBodyRefinement.getAbort m else pushState m ⟨4,by decide⟩ else
    if b1 then pushState m (if b2 then ⟨1,by decide⟩ else ⟨0,by decide⟩) else
      if b2 then constState m else inputState m
private theorem tag_exit (m : Fin 3) (b0 b1 b2 : Bool) :
    SerializedBodyRefinement.getExit (if b0 then if b1 then ⟨6,by decide⟩ else ⟨5,by decide⟩
      else if b1 then ⟨4,by decide⟩ else ⟨3,by decide⟩) b2 m=tagDestination m b0 b1 b2 := by
  fin_cases m <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl
end FullBodyClosure
