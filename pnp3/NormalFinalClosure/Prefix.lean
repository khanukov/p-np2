import NormalFinalClosure.Machine
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env←getEnv
  for (leaf,kind) in [("oldM","definition"),("count","definition"),("liftOld","definition"),
      ("code","definition"),("extend","definition"),("nativeCount","definition")] do
    let n:=Name.str (Name.str (Name.num `_private.NormalFinalClosure.Machine 0) "NormalFinalClosure") leaf
    let some (.defnInfo ci):=env.find? n | throwError "Missing exact controller definition {n}"
    let some i:=env.getModuleIdxFor? n | throwError "Missing controller owner"
    unless i.toNat < env.header.moduleNames.size && env.header.moduleNames[i]! == `NormalFinalClosure.Machine do
      throwError "Wrong controller owner"
    logInfo m!"normal-controller-support|{n}|{kind}|{ci.type}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private def incState (M : UniformTM) (q : Fin M.stateCount) : Fin (M.stateCount+nativeCount) :=
  ⟨q.val,by have h:=q.isLt;omega⟩
private theorem extend_rows (M : UniformTM)
    (rows : Fin (M.stateCount+nativeCount) → Option Bool → Fin (M.stateCount+nativeCount) × Option Bool × Move)
    (q : Fin M.stateCount) (b : Option Bool)
    (row : rows (incState M q) b=(incState M (M.step q b).1,(M.step q b).2)) :
    (extend M rows).step (incState M q) b=(incState M (M.step q b).1,(M.step q b).2) := by
  by_cases ha:q=M.accept
  · subst q
    simp only [UniformTM.step_accept]
    exact (extend M rows).step_accept b
  · by_cases hr:q=M.reject
    · subst q
      simp only [UniformTM.step_reject]
      exact (extend M rows).step_reject b
    · have na : incState M q≠(extend M rows).accept := by
        intro h;apply ha;exact Fin.ext (congrArg (fun x : Fin (M.stateCount+nativeCount)=>x.val) h)
      have nr : incState M q≠(extend M rows).reject := by
        intro h;apply hr;exact Fin.ext (congrArg (fun x : Fin (M.stateCount+nativeCount)=>x.val) h)
      simp only [UniformTM.step,if_neg na,if_neg nr]
      exact row
private theorem rows_agree (k : Nat) (q : Fin (RawCallerClosure.machine k).stateCount)
    (uncut:q≠RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)) (b : Option Bool) :
    (machine k).step (old k q) b=
      (old k ((RawCallerClosure.machine k).step q b).1,((RawCallerClosure.machine k).step q b).2) := by
  have codeRow : code k (old k q) b=
      (old k ((RawCallerClosure.machine k).step q b).1,((RawCallerClosure.machine k).step q b).2) := by
    have hq:q.val < (RawCallerClosure.machine k).stateCount:=q.isLt
    dsimp only [code,old,liftOld,oldM]
    rw [dif_pos hq]
    have same : (⟨q.val,hq⟩:Fin (RawCallerClosure.machine k).stateCount)=q:=rfl
    rw [same,if_neg uncut]
  exact extend_rows (oldM k) (code k) q b codeRow
private def mapConfig {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C : Nat} (c : Config A.stateCount N C) : Config B.stateCount N C :=
  ⟨f c.state,c.head,c.tape⟩
private theorem step_map {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C : Nat} (c : Config A.stateCount N C)
    (rows:∀ b,B.step (f c.state) b=(f (A.step c.state b).1,(A.step c.state b).2)) :
    B.stepConfig (mapConfig f c)=mapConfig f (A.stepConfig c) := by
  cases c with
  | mk s h T=>
    change (⟨(B.step (f s) (T h)).1,moveHead h (B.step (f s) (T h)).2.2,
      fun i=>if i=h then (B.step (f s) (T h)).2.1 else T i⟩:Config B.stateCount N C)=_
    rw [rows]
    rfl
private theorem map_run {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C T : Nat} (c : Config A.stateCount N C)
    (rows:∀ u,u < T → ∀ b,B.step (f (A.run u c).state) b=
      (f (A.step (A.run u c).state b).1,(A.step (A.run u c).state b).2)) :
    ∀ u,u ≤ T → B.run u (mapConfig f c)=mapConfig f (A.run u c) := by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>
    simp only [UniformTM.run,ih (by omega)]
    exact step_map f (A.run u c) (rows u (by omega))
/-- Every earlier complete raw Config is preserved through the FIRST old rowsDone
arrival. Only its next literal transition starts the new prefix/padding guard. -/
theorem raw_prefix (k N B T : Nat) (y : Bitstring N)
    (first:∀ u,u < T → ((RawCallerClosure.machine k).run u
      (initialConfig (RawCallerClosure.machine k) B y)).state≠
        RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)) :
    ∀ u,u ≤ T → (machine k).run u (initialConfig (machine k) B y)=
      config k ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)) := by
  exact map_run (old k) (initialConfig (RawCallerClosure.machine k) B y)
    (fun u hu b=>rows_agree k _ (first u hu) b)
/-- Independently restated full same-budget/same-source raw prefix proposition. -/
theorem raw_prefix_mirror (k N B T : Nat) (y : Bitstring N)
    (first:∀ u,u < T → ((RawCallerClosure.machine k).run u
      (initialConfig (RawCallerClosure.machine k) B y)).state≠
        RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)) :
    ∀ u,u ≤ T → (machine k).run u (initialConfig (machine k) B y)=
      ⟨old k ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)).state,
        ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)).head,
        ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)).tape⟩ :=
  raw_prefix k N B T y first
#print axioms raw_prefix
#print axioms raw_prefix_mirror
end NormalFinalClosure
