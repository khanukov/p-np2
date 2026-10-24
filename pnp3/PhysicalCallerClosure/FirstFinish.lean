import PhysicalCallerClosure.CallerSinks
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
private theorem done_run : ∀ {k N B : Nat} (c : Config (callerMachine k).stateCount N B),
    c.state=rowsDone k → ∀ t,(callerMachine k).run t c=c := by
  run_tac select `PhysicalCallerClosure.CallerSinks "done_run" "theorem"
private theorem done_ne_accept (k : Nat) : rowsDone k≠(callerMachine k).accept:=by
  intro bad
  have values:=congrArg Fin.val bad
  change (BodyIngress.machine k).stateCount+7500+1432=(BodyIngress.machine k).accept.val at values
  have small:=(BodyIngress.machine k).accept.isLt
  omega
private theorem done_ne_reject (k : Nat) : rowsDone k≠(callerMachine k).reject:=by
  intro bad
  have values:=congrArg Fin.val bad
  change (BodyIngress.machine k).stateCount+7500+1432=(BodyIngress.machine k).reject.val at values
  have small:=(BodyIngress.machine k).reject.isLt
  omega
private theorem no_accept_to_finish {k N B t : Nat} (c d : Config (callerMachine k).stateCount N B)
    (endEq:(callerMachine k).run t c=d) (finish:d.state=(callerMachine k).reject ∨ d.state=rowsDone k) :
    ∀ u,u ≤ t → ((callerMachine k).run u c).state≠(callerMachine k).accept:=by
  intro u hu bad
  have fixed:=(callerMachine k).run_accept ((callerMachine k).run u c) bad (t-u)
  rw [←UniformTM.run_add,show u+(t-u)=t by omega,endEq] at fixed
  have da:d.state=(callerMachine k).accept:=(congrArg Config.state fixed).trans bad
  rcases finish with h|h
  · exact (callerMachine k).accept_ne_reject (da.symm.trans h)
  · exact done_ne_accept k (h.symm.trans da)
private theorem first_finish {k N B total : Nat} (c d : Config (callerMachine k).stateCount N B)
    (endEq:(callerMachine k).run total c=d) (finish:d.state=(callerMachine k).reject ∨ d.state=rowsDone k) :
    ∃ t,t ≤ total ∧ (callerMachine k).run t c=d ∧
      (∀ u,u < t → ((callerMachine k).run u c).state≠(callerMachine k).reject ∧
        ((callerMachine k).run u c).state≠rowsDone k) ∧
      (∀ u,u ≤ t → ((callerMachine k).run u c).state≠(callerMachine k).accept) := by
  induction total using Nat.strong_induction_on with
  | h total ih =>
    by_cases early:∃ u,u < total ∧ (((callerMachine k).run u c).state=(callerMachine k).reject ∨
        ((callerMachine k).run u c).state=rowsDone k)
    · obtain ⟨u,lt,sink⟩:=early
      have fixed:∀ v,(callerMachine k).run v ((callerMachine k).run u c)=(callerMachine k).run u c:=by
        rcases sink with h|h
        · exact (callerMachine k).run_reject _ h
        · exact done_run _ h
      have same:(callerMachine k).run u c=d:=by
        have f:=fixed (total-u)
        rw [←UniformTM.run_add,show u+(total-u)=total by omega,endEq] at f
        exact f.symm
      obtain ⟨t,tu,eq,first,safe⟩:=ih u lt same
      exact ⟨t,by omega,eq,first,safe⟩
    · refine ⟨total,le_rfl,endEq,?_,no_accept_to_finish c d endEq finish⟩
      intro u hu
      constructor
      · intro h;exact early ⟨u,hu,Or.inl h⟩
      · intro h;exact early ⟨u,hu,Or.inr h⟩
private theorem work_before_first {k N B t u : Nat} (c : Config (callerMachine k).stateCount N B)
    (_first:∀ v,v < t → ((callerMachine k).run v c).state≠(callerMachine k).reject ∧
      ((callerMachine k).run v c).state≠rowsDone k)
    (finish:((callerMachine k).run t c).state=(callerMachine k).reject ∨ ((callerMachine k).run t c).state=rowsDone k)
    (work:((callerMachine k).run u c).state≠(callerMachine k).reject ∧ ((callerMachine k).run u c).state≠rowsDone k) : u < t := by
  by_contra bad
  have future:(callerMachine k).run u c=(callerMachine k).run t c:=by
    have fixed:∀ v,(callerMachine k).run v ((callerMachine k).run t c)=(callerMachine k).run t c:=by
      rcases finish with h|h
      · exact (callerMachine k).run_reject _ h
      · exact done_run _ h
    rw [show u=t+(u-t) by omega,UniformTM.run_add,fixed]
  rw [future] at work
  rcases finish with h|h
  · exact work.1 h
  · exact work.2 h
end PhysicalCallerClosure
