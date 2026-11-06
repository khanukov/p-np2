import RawCallerClosure.Rows
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let e←getEnv
  for leaf in ["cut","old_start","old_reject","old_accept","old_injective","old_rows","caller_run","old_body"] do
    let n:=Name.str (Name.str (Name.num `_private.RawCallerClosure.Rows 0) "RawCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact transport support"
    let kind:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
    unless (if leaf=="cut" then kind=="definition" else kind=="theorem") do throwError "Wrong transport kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `RawCallerClosure.Rows do throwError "Wrong transport owner"
    logInfo m!"ordinary-transport|{n}|{kind}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def mapConfig {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C : Nat} (c : Config A.stateCount N C) : Config B.stateCount N C := ⟨f c.state,c.head,c.tape⟩
private theorem step_map {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C : Nat} (c : Config A.stateCount N C)
    (rows:∀ b,B.step (f c.state) b=(f (A.step c.state b).1,(A.step c.state b).2)) :
    B.stepConfig (mapConfig f c)=mapConfig f (A.stepConfig c) := by
  apply Config.ext_parts
  · exact congrArg Prod.fst (rows (c.tape c.head))
  · change moveHead c.head _=moveHead c.head _
    dsimp only [mapConfig]
    rw [rows]
  · funext i
    change (if i=c.head then (B.step (f c.state) (c.tape c.head)).2.1 else c.tape i)=_
    rw [rows]
    rfl
private theorem run_map {A B : UniformTM} (f : Fin A.stateCount → Fin B.stateCount)
    {N C : Nat} (c : Config A.stateCount N C) (T : Nat)
    (rows:∀ u,u<T → ∀ b,B.step (f (A.run u c).state) b=
      (f (A.step (A.run u c).state b).1,(A.step (A.run u c).state b).2)) :
    ∀ u,u≤T → B.run u (mapConfig f c)=mapConfig f (A.run u c) := by
  intro u
  induction u with
  | zero => intro _;rfl
  | succ u ih =>
    intro bound
    rw [UniformTM.run,ih (by omega),step_map f _ (rows u (by omega))]
    rfl
private theorem initial_map (k N B : Nat) (y : Bitstring N) :
    initialConfig (machine k) B y=oldConfig k (initialConfig (CertificateGuardClosure.machine k) B y) := by
  apply Config.ext_parts
  · exact (old_start k).symm
  · rfl
  · rfl
private theorem transport_prefix (k N B T : Nat) (y : Bitstring N)
    (first:∀ u,u<T → ∀ mode,((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) B y)).state≠cut k mode) :
    ∀ u,u≤T → (machine k).run u (initialConfig (machine k) B y)=
      oldConfig k ((CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) B y)) := by
  rw [initial_map]
  exact run_map (A:=CertificateGuardClosure.machine k) (B:=machine k) (old k) _ T
    (fun u hu b=>old_rows k _ (first u hu) b)
end RawCallerClosure
