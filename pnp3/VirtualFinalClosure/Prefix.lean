import VirtualFinalClosure.OriginalRows
namespace VirtualFinalClosure.Prefix
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName,isThm) in [("Intercept","Intercept",false),("step_projection","stepProjection",true)] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith "_private.VirtualFinalClosure.OriginalRows." &&
      n.toString.endsWith (".VirtualFinalClosure.OriginalRows."++key)
    match found with
    | [(n,ci)]=>
      let correct:=match ci with | .thmInfo _=>isThm | .defnInfo _=>!isThm | _=>false
      unless correct do throwError "Wrong prefix interface kind {n}"
      logInfo m!"private-term|{n}|isTheorem={isThm}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique same-table prefix interface {key}"
private def lift (k : Nat) {N B : Nat} (f : Fin 4)
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) : Config (machine k).stateCount N B :=
  config k ⟨8+f.val,by have h:=f.isLt;omega⟩ c
private def lift_type : ∀ k,{N B : Nat} → Fin 4 →
    Config (CertificateGuardClosure.machine k).stateCount N B → Config (machine k).stateCount N B := lift
private def Intercept_type : ∀ k,Fin (CertificateGuardClosure.machine k).stateCount → Option Bool → Prop := Intercept
private theorem config_row {O M : UniformTM} {N B : Nat}
    (c : Config O.stateCount N B) (q q' : Fin M.stateCount)
    (row : M.step q (c.tape c.head)=(q',(O.step c.state (c.tape c.head)).2)) :
    M.stepConfig ⟨q,c.head,c.tape⟩=
      ⟨q',(O.stepConfig c).head,(O.stepConfig c).tape⟩ := by
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · change moveHead c.head (M.step q (c.tape c.head)).2.2=
      moveHead c.head (O.step c.state (c.tape c.head)).2.2
    rw [row]
  · funext i
    change (if i=c.head then (M.step q (c.tape c.head)).2.1 else c.tape i)=
      (if i=c.head then (O.step c.state (c.tape c.head)).2.1 else c.tape i)
    rw [row]
private theorem step_lift (k : Nat) {N B : Nat}
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) (f : Fin 4)
    (safe : ¬Intercept k c.state (c.tape c.head)) :
    ∃ g : Fin 4,(machine k).stepConfig (lift k f c)=
      lift k g ((CertificateGuardClosure.machine k).stepConfig c) := by
  obtain ⟨g,row⟩:=stepProjection k c.state f (c.tape c.head) safe
  refine ⟨g,?_⟩
  exact config_row c _ _ row
private theorem initial (k : Nat) {N : Nat} (B : Nat) (y : Bitstring N) :
    initialConfig (machine k) B y=lift k ⟨1,by decide⟩
      (initialConfig (CertificateGuardClosure.machine k) B y) := by rfl
/-- Every literal prefix edge is on the same larger tape allocation; the finite
flag may vary, so a fixed-embedding run identity is intentionally not asserted. -/
private theorem run_prefix (k : Nat) {N : Nat} (B : Nat) (y : Bitstring N) (t : Nat)
    (safe : ∀ u,u<t →
      let c:=(CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) B y)
      ¬Intercept k c.state (c.tape c.head)) :
    ∃ f : Fin 4,(machine k).run t (initialConfig (machine k) B y)=
      lift k f ((CertificateGuardClosure.machine k).run t (initialConfig (CertificateGuardClosure.machine k) B y)) := by
  induction t with
  | zero => exact ⟨⟨1,by decide⟩,initial k B y⟩
  | succ t ih =>
    obtain ⟨f,before⟩:=ih (fun u hu=>safe u (by omega))
    obtain ⟨g,one⟩:=step_lift k
      ((CertificateGuardClosure.machine k).run t (initialConfig (CertificateGuardClosure.machine k) B y)) f
      (safe t (by omega))
    refine ⟨g,?_⟩
    change (machine k).stepConfig ((machine k).run t (initialConfig (machine k) B y))=_
    rw [before,one]
    rfl
private theorem every_prefix (k : Nat) {N : Nat} (B : Nat) (y : Bitstring N) (t : Nat)
    (safe : ∀ u,u<t →
      let c:=(CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) B y)
      ¬Intercept k c.state (c.tape c.head)) :
    ∀ u,u ≤ t → ∃ f : Fin 4,(machine k).run u (initialConfig (machine k) B y)=
      lift k f ((CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) B y)) := by
  intro u hu
  exact run_prefix k B y u (fun v hv=>safe v (by omega))
#print axioms lift_type
#print axioms Intercept_type
#print axioms step_lift
#print axioms initial
#print axioms run_prefix
#print axioms every_prefix
end VirtualFinalClosure.Prefix
