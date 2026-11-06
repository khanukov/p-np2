import NormalFinalClosure.Machine2
import NormalFinalClosure.Prefix
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.NormalFinalClosure.Machine2 0) "NormalFinalClosure") "rows2"
  let some (.defnInfo ci):=e.find? n | throwError "Missing exact v2 finite row function"
  let some i:=e.getModuleIdxFor? n | throwError "Missing row owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `NormalFinalClosure.Machine2 do throwError "Wrong row owner"
  logInfo m!"normal-v2-row-unfold|{n}|{ci.type}"
  modifyScope fun s=>{s with openDecls:=.explicit `actualRows2 n::s.openDecls}
run_cmd do
  let e←getEnv
  for (leaf,aliasName) in [("liftOld","lift1"),("oldM","base1")] do
    let n:=Name.str (Name.str (Name.num `_private.NormalFinalClosure.Machine 0) "NormalFinalClosure") leaf
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact v1 definition"
    let some i:=e.getModuleIdxFor? n | throwError "Missing v1 owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `NormalFinalClosure.Machine do throwError "Wrong v1 owner"
    logInfo m!"v2-prefix-v1-support|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private def priorProof (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.NormalFinalClosure.Prefix 0) "NormalFinalClosure") leaf
  let some (.thmInfo ci):=e.find? n | throwError "Missing exact prefix theorem"
  let some i:=e.getModuleIdxFor? n | throwError "Missing prefix owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `NormalFinalClosure.Prefix do throwError "Wrong prefix owner"
  logInfo m!"v2-prefix-proof|{n}|{ci.type}"
  closeMainGoal `priorProof (mkConst n (ci.levelParams.map Level.param))
private theorem priorRows : ∀ (k : Nat) (q : Fin (RawCallerClosure.machine k).stateCount),
    q≠RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k) → ∀ b,
    (machine k).step (old k q) b=(old k ((RawCallerClosure.machine k).step q b).1,((RawCallerClosure.machine k).step q b).2) := by
  run_tac priorProof "rows_agree"
private theorem priorRun : ∀ {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C T : Nat} (c : Config A.stateCount N C),
    (∀ u,u < T → ∀ b,B.step (f (A.run u c).state) b=(f (A.step (A.run u c).state b).1,(A.step (A.run u c).state b).2)) →
    ∀ u,u ≤ T → B.run u ⟨f c.state,c.head,c.tape⟩=
      ⟨f (A.run u c).state,(A.run u c).head,(A.run u c).tape⟩ := by
  run_tac priorProof "map_run"
private theorem updated_step (M : UniformTM)
    (rows : Fin M.stateCount → Option Bool → Fin M.stateCount × Option Bool × Move)
    (s : Fin M.stateCount) (b : Option Bool) (same:rows s b=M.rawStep s b) :
    ({M with rawStep:=rows}:UniformTM).step s b=M.step s b := by
  by_cases a:s=M.accept
  · simp [UniformTM.step,a]
  · by_cases r:s=M.reject
    · simp [UniformTM.step,r]
    · simp only [UniformTM.step,if_neg a,if_neg r]
      exact same
private theorem updated_config (M : UniformTM)
    (rows : Fin M.stateCount → Option Bool → Fin M.stateCount × Option Bool × Move)
    {N B : Nat} (c : Config M.stateCount N B)
    (same:∀ b,rows c.state b=M.rawStep c.state b) :
    ({M with rawStep:=rows}:UniformTM).stepConfig c=M.stepConfig c := by
  cases c with
  | mk s h T=>
    change (⟨(({M with rawStep:=rows}:UniformTM).step s (T h)).1,
      moveHead h (({M with rawStep:=rows}:UniformTM).step s (T h)).2.2,
      fun i=>if i=h then (({M with rawStep:=rows}:UniformTM).step s (T h)).2.1 else T i⟩:Config M.stateCount N B)=_
    rw [updated_step M rows s (T h) (same (T h))]
    rfl
private theorem updated_run (M : UniformTM)
    (rows : Fin M.stateCount → Option Bool → Fin M.stateCount × Option Bool × Move)
    {N B T : Nat} (c : Config M.stateCount N B)
    (same:∀ u,u < T → ∀ b,rows (M.run u c).state b=M.rawStep (M.run u c).state b) :
    ∀ u,u ≤ T → ({M with rawStep:=rows}:UniformTM).run u c=M.run u c := by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>
    rw [UniformTM.run,ih (by omega),UniformTM.run]
    exact updated_config M rows (M.run u c) (same u (by omega))
private theorem rowsOld (k : Nat) (q : Fin (RawCallerClosure.machine k).stateCount)
    (uncut:q≠RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)) (b : Option Bool) :
    (machine2 k).step (old2 k q) b=(old2 k ((RawCallerClosure.machine k).step q b).1,((RawCallerClosure.machine k).step q b).2) := by
  have below:(old k q).val < (RawCallerClosure.machine k).stateCount := by
    dsimp only [old,lift1,base1]
    exact q.isLt
  have row:actualRows2 k (old k q) b=(machine k).rawStep (old k q) b := by
    unfold actualRows2
    rw [if_pos below]
  exact (updated_step (machine k) (actualRows2 k) (old k q) b row).trans (priorRows k q uncut b)
/-- Whole same-budget raw prefix on v2, before FIRST old rowsDone. This retains
all actual paid starts and every source/exterior cell without retagging an endpoint. -/
theorem raw_prefix2 (k N B T : Nat) (y : Bitstring N)
    (first:∀ u,u < T → ((RawCallerClosure.machine k).run u
      (initialConfig (RawCallerClosure.machine k) B y)).state≠
        RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)) :
    ∀ u,u ≤ T → (machine2 k).run u (initialConfig (machine2 k) B y)=
      config2 k ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)) := by
  exact priorRun (old2 k) (initialConfig (RawCallerClosure.machine k) B y)
    (fun u hu b=>rowsOld k _ (first u hu) b)
/-- Independently full restatement of same-state/head/tape raw history. -/
theorem raw_prefix2_mirror (k N B T : Nat) (y : Bitstring N)
    (first:∀ u,u < T → ((RawCallerClosure.machine k).run u
      (initialConfig (RawCallerClosure.machine k) B y)).state≠
        RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)) :
    ∀ u,u ≤ T → (machine2 k).run u (initialConfig (machine2 k) B y)=
      ⟨old2 k ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)).state,
        ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)).head,
        ((RawCallerClosure.machine k).run u (initialConfig (RawCallerClosure.machine k) B y)).tape⟩ :=
  raw_prefix2 k N B T y first
#print axioms raw_prefix2
#print axioms raw_prefix2_mirror
end NormalFinalClosure
