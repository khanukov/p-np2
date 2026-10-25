import FullFinalClosure.Target
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
namespace Control
-- Symbolic finite-table lemmas keep the large imported ROMs opaque.
private def L (A B : UniformTM) (q : Fin A.stateCount) : Fin (A.stateCount+B.stateCount) :=
  ⟨q.val,by have h:=q.isLt;omega⟩
private def R (A B : UniformTM) (q : Fin B.stateCount) : Fin (A.stateCount+B.stateCount) :=
  if q=B.accept then L A B A.accept else if q=B.reject then L A B A.reject
  else ⟨A.stateCount+q.val,by have h:=q.isLt;omega⟩
private def code (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (s:Fin (A.stateCount+B.stateCount)) (b:Option Bool) : Fin (A.stateCount+B.stateCount) × Option Bool × Move :=
  if h:s.val<A.stateCount then
    let q:Fin A.stateCount:=⟨s.val,h⟩
    match δ q with
    | some mode=>(R A B (β mode),b,Move.stay)
    | none=>let a:=A.step q b;(L A B a.1,a.2)
  else
    let q:Fin B.stateCount:=⟨s.val-A.stateCount,by have h:=s.isLt;omega⟩
    let a:=B.step q b;(R A B a.1,a.2)
private def M (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount) : UniformTM where
  stateCount:=A.stateCount+B.stateCount
  start:=L A B A.start
  accept:=L A B A.accept
  reject:=L A B A.reject
  accept_ne_reject:=by
    intro h;apply A.accept_ne_reject;apply Fin.ext
    exact congrArg (fun q:Fin (A.stateCount+B.stateCount)=>q.val) h
  rawStep:=code A B δ β
private theorem Linj (A B : UniformTM) : Function.Injective (L A B) := by
  intro q s h
  have v:=congrArg (fun t:Fin (A.stateCount+B.stateCount)=>t.val) h
  exact Fin.ext v
private theorem Lrow (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (q:Fin A.stateCount) (b:Option Bool) (uncut:δ q=none) :
    (M A B δ β).step (L A B q) b=(L A B (A.step q b).1,(A.step q b).2) := by
  by_cases ha:q=A.accept
  · subst q;rw [A.step_accept];exact (M A B δ β).step_accept b
  by_cases hr:q=A.reject
  · subst q;rw [A.step_reject];exact (M A B δ β).step_reject b
  have na:L A B q≠(M A B δ β).accept:=fun h=>ha (Linj A B h)
  have nr:L A B q≠(M A B δ β).reject:=fun h=>hr (Linj A B h)
  rw [UniformTM.step_of_ne _ na nr]
  change code A B δ β (L A B q) b=_
  unfold code
  have hq:(L A B q).val<A.stateCount:=q.isLt
  rw [dif_pos hq]
  change (match δ q with |some m=>(R A B (β m),b,Move.stay)|none=>(L A B (A.step q b).1,(A.step q b).2))=_
  rw [uncut]
private theorem Raccept (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount) :
    R A B B.accept=(M A B δ β).accept := by rw [R,if_pos rfl];rfl
private theorem Rreject (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount) :
    R A B B.reject=(M A B δ β).reject := by rw [R,if_neg B.accept_ne_reject.symm,if_pos rfl];rfl
private theorem Rrow (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (q:Fin B.stateCount) (b:Option Bool) :
    (M A B δ β).step (R A B q) b=(R A B (B.step q b).1,(B.step q b).2) := by
  by_cases ha:q=B.accept
  · subst q;rw [B.step_accept,Raccept A B δ β,UniformTM.step_accept]
  by_cases hr:q=B.reject
  · subst q;rw [B.step_reject,Rreject A B δ β,UniformTM.step_reject]
  have value:(R A B q).val=A.stateCount+q.val:=by rw [R,if_neg ha,if_neg hr]
  have na:R A B q≠(M A B δ β).accept:=by
    intro h
    have v:=congrArg (fun s:Fin (A.stateCount+B.stateCount)=>s.val) h
    change (R A B q).val=A.accept.val at v
    rw [value] at v
    have bound:=A.accept.isLt;omega
  have nr:R A B q≠(M A B δ β).reject:=by
    intro h
    have v:=congrArg (fun s:Fin (A.stateCount+B.stateCount)=>s.val) h
    change (R A B q).val=A.reject.val at v
    rw [value] at v
    have bound:=A.reject.isLt;omega
  rw [UniformTM.step_of_ne _ na nr]
  change code A B δ β (R A B q) b=_
  unfold code
  rw [dif_neg (by rw [value];omega)]
  have eta:(⟨(R A B q).val-A.stateCount,by rw [value];have h:=q.isLt;omega⟩:Fin B.stateCount)=q:=by
    apply Fin.ext
    change (R A B q).val-A.stateCount=q.val
    omega
  rw [eta]
private theorem Rreflect (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (q:Fin B.stateCount) :
    (R A B q=(M A B δ β).accept → q=B.accept) ∧ (R A B q=(M A B δ β).reject → q=B.reject) := by
  by_cases ha:q=B.accept
  · subst q;rw [Raccept A B δ β];exact ⟨fun _=>rfl,fun h=>((M A B δ β).accept_ne_reject h).elim⟩
  by_cases hr:q=B.reject
  · subst q;rw [Rreject A B δ β];exact ⟨fun h=>((M A B δ β).accept_ne_reject h.symm).elim,fun _=>rfl⟩
  have value:(R A B q).val=A.stateCount+q.val:=by rw [R,if_neg ha,if_neg hr]
  constructor
  · intro h
    have v:=congrArg (fun s:Fin (A.stateCount+B.stateCount)=>s.val) h
    change (R A B q).val=A.accept.val at v
    rw [value] at v;have bound:=A.accept.isLt;omega
  · intro h
    have v:=congrArg (fun s:Fin (A.stateCount+B.stateCount)=>s.val) h
    change (R A B q).val=A.reject.val at v
    rw [value] at v;have bound:=A.reject.isLt;omega
private theorem switch (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (q:Fin A.stateCount) (mode:Fin 3) (na:q≠A.accept) (nr:q≠A.reject) (hit:δ q=some mode) (b:Option Bool) :
    (M A B δ β).step (L A B q) b=(R A B (β mode),b,Move.stay) := by
  have noA:L A B q≠(M A B δ β).accept:=fun h=>na (Linj A B h)
  have noR:L A B q≠(M A B δ β).reject:=fun h=>nr (Linj A B h)
  rw [UniformTM.step_of_ne _ noA noR]
  change code A B δ β (L A B q) b=_
  unfold code
  have hq:(L A B q).val<A.stateCount:=q.isLt
  rw [dif_pos hq]
  change (match δ q with |some m=>(R A B (β m),b,Move.stay)|none=>_)=_
  rw [hit]
private def cfg {A B : UniformTM} (f:Fin A.stateCount → Fin B.stateCount) {N C:Nat}
    (c:Config A.stateCount N C) : Config B.stateCount N C:=⟨f c.state,c.head,c.tape⟩
private theorem mapStep {A B : UniformTM} (f:Fin A.stateCount → Fin B.stateCount) {N C:Nat}
    (c:Config A.stateCount N C) (row:∀ b,B.step (f c.state) b=(f (A.step c.state b).1,(A.step c.state b).2)) :
    B.stepConfig (cfg (A:=A) (B:=B) f c)=cfg (A:=A) (B:=B) f (A.stepConfig c) := by
  cases c with
  | mk q h T=>
    change (⟨(B.step (f q) (T h)).1,moveHead h (B.step (f q) (T h)).2.2,
      fun i=>if i=h then (B.step (f q) (T h)).2.1 else T i⟩:Config B.stateCount N C)=_
    rw [row];rfl
private theorem mapRun {A B : UniformTM} (f:Fin A.stateCount → Fin B.stateCount) {N C T:Nat}
    (c:Config A.stateCount N C) (rows:∀ u,u<T → ∀ b,
      B.step (f (A.run u c).state) b=(f (A.step (A.run u c).state b).1,(A.step (A.run u c).state b).2)) :
    ∀ u,u≤T → B.run u (cfg (A:=A) (B:=B) f c)=cfg (A:=A) (B:=B) f (A.run u c) := by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>rw [UniformTM.run,ih (by omega),mapStep f _ (rows u (by omega))];rfl
private theorem runR (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (N C t:Nat) (c:Config B.stateCount N C) :
    (M A B δ β).run t ⟨R A B c.state,c.head,c.tape⟩=
      ⟨R A B (B.run t c).state,(B.run t c).head,(B.run t c).tape⟩ :=
  mapRun (A:=B) (B:=M A B δ β) (R A B) c (fun _ _ b=>Rrow A B δ β _ b) t le_rfl
private theorem runL (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (N C t:Nat) (y:Bitstring N) (first:∀ u,u<t → δ (A.run u (initialConfig A C y)).state=none) :
    ∀ u,u≤t → (M A B δ β).run u (initialConfig (M A B δ β) C y)=
      ⟨L A B (A.run u (initialConfig A C y)).state,
        (A.run u (initialConfig A C y)).head,(A.run u (initialConfig A C y)).tape⟩ :=
  mapRun (A:=A) (B:=M A B δ β) (L A B) (initialConfig A C y) (fun u hu b=>Lrow A B δ β _ b (first u hu))
private theorem switchCfg (A B : UniformTM) (δ:Fin A.stateCount → Option (Fin 3)) (β:Fin 3 → Fin B.stateCount)
    (N C:Nat) (q:Fin A.stateCount) (mode:Fin 3) (na:q≠A.accept) (nr:q≠A.reject) (hit:δ q=some mode)
    (h:Fin (tapeLength N C)) (T:Fin (tapeLength N C) → Option Bool) :
    (M A B δ β).stepConfig ⟨L A B q,h,T⟩=⟨R A B (β mode),h,T⟩ := by
  apply Config.ext_parts
  · exact congrArg Prod.fst (switch A B δ β q mode na nr hit (T h))
  · change moveHead h _=h;rw [switch A B δ β q mode na nr hit];rfl
  · funext i
    change (if i=h then ((M A B δ β).step _ (T h)).2.1 else T i)=T i
    rw [switch A B δ β q mode na nr hit]
    split_ifs with eq
    · rw [eq]
    · rfl
end Control
private theorem concrete_L (k : Nat) (q:Fin (VirtualFinalClosure.machine k).stateCount) :
    Control.L (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) q=left k q := by
  apply Fin.ext
  rfl
private theorem concrete_R (k : Nat) (q:Fin (NormalFinalClosure.machine2 k).stateCount) :
    Control.R (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) q=right k q := by
  unfold Control.R right
  split_ifs
  · exact concrete_L k _
  · exact concrete_L k _
  · apply Fin.ext;rfl
private theorem concrete_step (k : Nat) (q:Fin (count k)) (b:Option Bool) :
    (Control.M (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k)).step q b=
      (machine k).step q b := by
  unfold UniformTM.step
  dsimp only [Control.M,machine,Control.L,left]
  split_ifs
  · rfl
  · rfl
  · unfold Control.code rows
    split_ifs
    · dsimp only
      simp only [concrete_R,concrete_L]
      rfl
    · dsimp only
      simp only [concrete_R]
private theorem concrete_config (k N B:Nat) (c:Config (count k) N B) :
    (Control.M (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k)).stepConfig c=
      (machine k).stepConfig c := by
  unfold UniformTM.stepConfig
  rw [concrete_step]
private theorem concrete_run (k N B t:Nat) (c:Config (count k) N B) :
    (Control.M (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k)).run t c=
      (machine k).run t c := by
  induction t with
  | zero=>simp only [UniformTM.run]
  | succ t ih=>simp only [UniformTM.run,ih,concrete_config]
private theorem concrete_initial (k N B:Nat) (y:Bitstring N) :
    initialConfig (Control.M (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k)) B y=
      initialConfig (machine k) B y := by
  unfold initialConfig
  dsimp only [Control.M,machine,Control.L,left,count]
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName) in [
    (`VirtualFinalClosure.FirstCutCore,`VirtualFinalClosure,"control_injective","aControlInj"),
    (`VirtualFinalClosure.NormalRow,`VirtualFinalClosure.NormalRow,"terminal_absent","aBodySafe")] do
    let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact connected control interface {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing connected control owner"
    unless e.header.moduleNames[i]! == owner do throwError "Wrong connected control owner"
    logInfo m!"registered-interface|{owner}|{n}|theorem|{(repr ci.type).pretty 1000000000}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
private theorem entryA_safe (k : Nat) (mode : Fin 3) :
    entryA k mode≠(VirtualFinalClosure.machine k).accept ∧ entryA k mode≠(VirtualFinalClosure.machine k).reject := by
  constructor
  · intro h
    change VirtualFinalClosure.control k _ ⟨8,by decide⟩=VirtualFinalClosure.control k (CertificateGuardClosure.machine k).accept ⟨8,by decide⟩ at h
    exact (aBodySafe k mode).1 (aControlInj k _ _ _ _ h)
  · intro h
    change VirtualFinalClosure.control k _ ⟨8,by decide⟩=VirtualFinalClosure.control k (CertificateGuardClosure.machine k).reject ⟨8,by decide⟩ at h
    exact (aBodySafe k mode).2 (aControlInj k _ _ _ _ h)
private theorem entryA_inj (k : Nat) : Function.Injective (entryA k) := by
  intro i j h
  change VirtualFinalClosure.control k _ _=VirtualFinalClosure.control k _ _ at h
  have old:=aControlInj k _ _ _ _ h
  have v:=congrArg Fin.val old
  have value (m:Fin 3) :
      (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry m)))).val=
        10+(67+(10+((288+Cursor.stateCount k+8+25)+(4+m.val)))) := by fin_cases m <;> rfl
  rw [value,value] at v
  exact Fin.ext (by omega)
private theorem dispatch_none (k : Nat) (q : Fin (VirtualFinalClosure.machine k).stateCount)
    (safe:∀ mode,q≠entryA k mode) : dispatch k q=none := by
  unfold dispatch;rw [if_neg (safe 0),if_neg (safe 1),if_neg (safe 2)]
private theorem dispatch_entry (k : Nat) (mode : Fin 3) : dispatch k (entryA k mode)=some mode := by
  have ne:∀ (i j:Fin 3),i≠j → entryA k i≠entryA k j:=fun i j h eq=>h (entryA_inj k eq)
  fin_cases mode
  · change dispatch k (entryA k 0)=some 0;unfold dispatch;rw [if_pos rfl]
  · change dispatch k (entryA k 1)=some 1;unfold dispatch;rw [if_neg (ne 1 0 (by decide)),if_pos rfl]
  · change dispatch k (entryA k 2)=some 2;unfold dispatch;rw [if_neg (ne 2 0 (by decide)),if_neg (ne 2 1 (by decide)),if_pos rfl]
private theorem left_inj (k : Nat) : Function.Injective (left k) :=
  Control.Linj (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k)
private theorem right_accept (k : Nat) : right k (NormalFinalClosure.machine2 k).accept=(machine k).accept :=
  Control.Raccept (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k)
private theorem right_reject (k : Nat) : right k (NormalFinalClosure.machine2 k).reject=(machine k).reject :=
  Control.Rreject (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k)
private theorem right_reflect_accept (k : Nat) (q : Fin (NormalFinalClosure.machine2 k).stateCount)
    (h:right k q=(machine k).accept) : q=(NormalFinalClosure.machine2 k).accept :=
  (Control.Rreflect (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k) q).1 h
private theorem right_reflect_reject (k : Nat) (q : Fin (NormalFinalClosure.machine2 k).stateCount)
    (h:right k q=(machine k).reject) : q=(NormalFinalClosure.machine2 k).reject :=
  (Control.Rreflect (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k) q).2 h
private theorem runB (k N B t : Nat) (c : Config (NormalFinalClosure.machine2 k).stateCount N B) :
    (machine k).run t (configB k c)=configB k ((NormalFinalClosure.machine2 k).run t c) := by
  have h:=Control.runR (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k) N B t c
  rw [concrete_run] at h
  exact h
private theorem prefixA (k N B t : Nat) (y : Bitstring N)
    (first:∀ u,u<t → ∀ mode,((VirtualFinalClosure.machine k).run u
      (initialConfig (VirtualFinalClosure.machine k) B y)).state≠entryA k mode) :
    ∀ u,u≤t → (machine k).run u (initialConfig (machine k) B y)=
      configA k ((VirtualFinalClosure.machine k).run u (initialConfig (VirtualFinalClosure.machine k) B y)) := by
  have h:=Control.runL (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k) N B t y
    (fun u hu=>dispatch_none k _ (first u hu))
  simp only [concrete_run,concrete_initial] at h
  exact h
private theorem handoff_config (k N B : Nat) (mode : Fin 3) (h : Fin (tapeLength N B))
    (T : Fin (tapeLength N B) → Option Bool) :
    (machine k).stepConfig (⟨left k (entryA k mode),h,T⟩:Config (machine k).stateCount N B)=
      configB k ⟨entryB k mode,h,T⟩ := by
  have run:=Control.switchCfg (VirtualFinalClosure.machine k) (NormalFinalClosure.machine2 k) (dispatch k) (entryB k)
    N B (entryA k mode) mode (entryA_safe k mode).1 (entryA_safe k mode).2 (dispatch_entry k mode) h T
  rw [concrete_config] at run
  exact run
end FullFinalClosure
