import NormalFinalClosure.Prefix2
import NormalFinalClosure.Rows2Code
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,leaves) in [
    (`NormalFinalClosure.Machine,["oldM","liftOld","code","native"]),
    (`NormalFinalClosure.Machine2,["rows2"]),
    (`NormalFinalClosure.Rows2Code,["ns2"])] do
    for leaf in leaves do
      let name:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure") leaf
      let some (.defnInfo ci):=e.find? name | throwError "Missing exact activated-row definition"
      let some i:=e.getModuleIdxFor? name | throwError "Missing activated-row owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong activated-row owner"
      logInfo m!"literal-first-activation-definition|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private def pick (owner ns : Name) (leaf : String) : TacticM Unit := do
  let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
  let e←getEnv
  let some (.thmInfo ci):=e.find? name | throwError "Missing immutable activation disjointness theorem"
  let some i:=e.getModuleIdxFor? name | throwError "Missing activation disjointness owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong activation disjointness owner"
  logInfo m!"activation-disjointness-full-type|{name}|{ci.type}"
  closeMainGoal `pick (mkConst name (ci.levelParams.map Level.param))
private theorem oldNotDone : ∀ k (s : Fin (CertificateGuardClosure.machine k).stateCount),
    RawCallerClosure.old k s≠RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k) := by
  run_tac pick `RawCallerClosure.Work `RawCallerClosure "old_not_done"
private theorem oldAccept : ∀ k,RawCallerClosure.old k (CertificateGuardClosure.machine k).accept=(RawCallerClosure.machine k).accept := by
  run_tac pick `RawCallerClosure.Rows `RawCallerClosure "old_accept"
private theorem oldReject : ∀ k,RawCallerClosure.old k (CertificateGuardClosure.machine k).reject=(RawCallerClosure.machine k).reject := by
  run_tac pick `RawCallerClosure.Rows `RawCallerClosure "old_reject"
private theorem oldValue (k : Nat) (q : Fin (RawCallerClosure.machine k).stateCount) : (old2 k q).val=q.val := by
  dsimp only [old2,old,liftOld,oldM]
private theorem oldInjective (k : Nat) : Function.Injective (old2 k) := by
  intro q s eq
  have vals:=congrArg (fun t:Fin (machine2 k).stateCount=>t.val) eq
  change (old2 k q).val=(old2 k s).val at vals
  rw [oldValue,oldValue] at vals
  exact Fin.ext vals
private theorem mapAccept (k : Nat) : old2 k (RawCallerClosure.machine k).accept=(machine2 k).accept := rfl
private theorem mapReject (k : Nat) : old2 k (RawCallerClosure.machine k).reject=(machine2 k).reject := rfl
private theorem priorRawProjection (k : Nat) : (machine k).rawStep=code k := rfl
private theorem rawProjection (k : Nat) : (machine2 k).rawStep=rows2 k := rfl
private theorem literal_activation (k : Nat) (b : Option Bool) :
    (machine2 k).step (old2 k (RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k))) b=
      (ns2 k 1,b,.stay) := by
  let q:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
  have cutA:q≠(RawCallerClosure.machine k).accept:=by
    intro bad
    exact oldNotDone k _ ((oldAccept k).trans bad.symm)
  have cutR:q≠(RawCallerClosure.machine k).reject:=by
    intro bad
    exact oldNotDone k _ ((oldReject k).trans bad.symm)
  have na:old2 k q≠(machine2 k).accept:=by
    intro bad
    apply cutA
    exact oldInjective k (bad.trans (mapAccept k).symm)
  have nr:old2 k q≠(machine2 k).reject:=by
    intro bad
    apply cutR
    exact oldInjective k (bad.trans (mapReject k).symm)
  apply (UniformTM.step_of_ne (machine2 k) na nr b).trans
  rw [rawProjection]
  change rows2 k (old2 k q) b=_
  dsimp only [rows2,old2,old,liftOld,oldM]
  rw [if_pos q.isLt]
  rw [priorRawProjection]
  change code k (old k q) b=_
  dsimp only [code,old,liftOld,oldM]
  rw [dif_pos q.isLt]
  have same:(⟨q.val,q.isLt⟩:Fin (RawCallerClosure.machine k).stateCount)=q:=rfl
  rw [same,if_pos rfl]
  rfl
private theorem stationary (M : UniformTM) (N B : Nat) (q v : Fin M.stateCount)
    (h : Fin (tapeLength N B)) (T : Fin (tapeLength N B) → Option Bool)
    (row:M.step q (T h)=(v,T h,.stay)) : M.stepConfig (⟨q,h,T⟩:Config M.stateCount N B)=⟨v,h,T⟩ := by
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · apply Fin.ext
    change (moveHead h (M.step q (T h)).2.2).val=h.val
    rw [row]
    rfl
  · funext i
    change (if i=h then (M.step q (T h)).2.1 else T i)=T i
    rw [row]
    by_cases eq:i=h
    · subst i;simp only [if_true]
    · rw [if_neg eq]
/-- The actual live callback changes only control; head and every tape cell
remain the SAME Config on the SAME dependent allocation. -/
private theorem activate_config (k N B : Nat) (h : Fin (tapeLength N B))
    (T : Fin (tapeLength N B) → Option Bool) :
    (machine2 k).stepConfig
      (⟨old2 k (RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)),h,T⟩ : Config (machine2 k).stateCount N B)=
      ⟨ns2 k 1,h,T⟩ := stationary (machine2 k) N B _ _ h T (literal_activation k (T h))
end NormalFinalClosure
