import PhysicalCallerClosure.FirstFinish
import PhysicalCallerClosure.CompareStep
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | .inductInfo _=>"inductive" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.FirstFinish,["first_finish","work_before_first"]),
      (`PhysicalCallerClosure.CompareStep,["eval_safe"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem first_endpoint {k N B total : Nat} (c d : Config (callerMachine k).stateCount N B)
    (endEq:(callerMachine k).run total c=d) (finish:d.state=(callerMachine k).reject ∨ d.state=rowsDone k) :
    ∃ t,t ≤ total ∧ (callerMachine k).run t c=d ∧
      (∀ u,u < t → ((callerMachine k).run u c).state≠(callerMachine k).reject ∧
        ((callerMachine k).run u c).state≠rowsDone k) ∧
      (∀ u,u ≤ t → ((callerMachine k).run u c).state≠(callerMachine k).accept) ∧
      (∀ u,((callerMachine k).run u c).state≠(callerMachine k).reject ∧
        ((callerMachine k).run u c).state≠rowsDone k → u < t) := by
  obtain ⟨t,bound,eq,first,safe⟩:=first_finish c d endEq finish
  refine ⟨t,bound,eq,first,safe,?_⟩
  intro u work
  exact work_before_first c first (by rw [eq];exact finish) work
private theorem paid_before_endpoint {k N B t u : Nat} (c : Config (callerMachine k).stateCount N B)
    (boundary:∀ u,((callerMachine k).run u c).state≠(callerMachine k).reject ∧
      ((callerMachine k).run u c).state≠rowsDone k → u < t)
    (q : Fin 7500) (h : Fin (tapeLength N B)) (T : Fin (tapeLength N B) → Option Bool)
    (paid:(callerMachine k).run u c=⟨evalState k q,h,T⟩) : u < t := by
  apply boundary
  rw [paid]
  exact (eval_safe k q).2
end PhysicalCallerClosure
