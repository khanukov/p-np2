import NormalClockClosure.NativePrice
import NormalClockClosure.Transport
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaf) in [(`NormalClockClosure.NativePrice,"first_run_small"),
      (`NormalClockClosure.Transport,"actual_room"),(`NormalClockClosure.Transport,"lift_actual"),
      (`NormalClockClosure.Transport,"deadline_decision")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalClockClosure") leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact same-run resource theorem {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing resource theorem owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong resource theorem owner"
    logInfo m!"same-run-resource-interface|{owner}|{n}|kind=theorem|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
/-- The unchanged full frozen all-raw ambient/V1 clock bridge. FIRSTness keeps
the original sealed execution witnesses; all runtime control is unchanged. -/
theorem bridge (k : Nat) : Target.Bridge k := by
  intro N y G M C O oldC rows virtual P
  obtain ⟨d,t,order,price,history,safe,oldFirst,first,outcome⟩:=NormalFinalClosure.normal_raw k N y
  have sharp:t+1 ≤ G:=first_run_small k N y t first
  obtain ⟨allocation,clock⟩:=clock_bound k N
  refine ⟨d,t,allocation,order,price,sharp,clock,?_,?_,?_,history,safe,oldFirst,first,outcome⟩
  · exact actual_room M N G t y sharp
  · exact lift_actual M N G t y sharp (fun b=>NormalFinalClosure.old2 k (virtual b)) first
  · exact deadline_decision M N G P t y sharp allocation (price.trans clock)
end NormalClockClosure
