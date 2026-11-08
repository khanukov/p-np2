import VirtualFinalClosure.BodyTrapRows
namespace VirtualFinalClosure.BodyTrap
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.BodyTrapRows","VirtualFinalClosure.BodyTrapRows","full","full",(0:Nat)),
      ("VirtualFinalClosure.BodyTrapRows","VirtualFinalClosure.BodyTrapRows","term_pin","termPin",1),
      ("VirtualFinalClosure.BodyTrapRows","VirtualFinalClosure.BodyTrapRows","effective","bodyRow",1),
      ("VirtualFinalClosure.BodyTrapRows","VirtualFinalClosure.BodyTrapRows","full_value","fullValue",1),
      ("VirtualFinalClosure.BodyTrapRows","VirtualFinalClosure.BodyTrapRows","carry_large","carryLarge",1),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","quotient_control","controlQuotient",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_div","packDiv",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual BODY trap term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual BODY trap term {mod}/{key}"
private def Region (k : Nat) (q : Fin (machine k).stateCount) : Prop:=
  q=(machine k).accept ∨ q=(machine k).reject ∨
    ∃ (s : Fin SerializedBody.machine.stateCount) (m : Fin 144),
      s.val≠0 ∧ s.val≠1 ∧ q=control k (full k s) m
private def Region_type : ∀ k,Fin (machine k).stateCount → Prop:=Region
private theorem step (k : Nat) (q : Fin (machine k).stateCount) (b : Option Bool)
    (inside : Region k q) : Region k ((machine k).step q b).1:=by
  rcases inside with rfl|rfl|⟨s,m,s0,s1,rfl⟩
  · left;rw [UniformTM.step_accept]
  · right;left;rw [UniformTM.step_reject]
  · obtain ⟨mm,row,normalized⟩:=bodyRow k s m b s0 s1
    rw [row]
    let next:=(SerializedBody.machine.step s b).1
    by_cases zero : next.val=0
    · have same : next=SerializedBody.machine.accept:=Fin.ext zero
      have terminal : full k next=(CertificateGuardClosure.machine k).accept:=by rw [same];exact (termPin k).1
      have md : mm=⟨8,by decide⟩:=Fin.ext (normalized (Or.inl terminal))
      left
      rw [show (SerializedBody.machine.step s b).1=next from rfl,terminal,md]
      rfl
    · by_cases one : next.val=1
      · have same : next=SerializedBody.machine.reject:=Fin.ext one
        have terminal : full k next=(CertificateGuardClosure.machine k).reject:=by rw [same];exact (termPin k).2
        have md : mm=⟨8,by decide⟩:=Fin.ext (normalized (Or.inr terminal))
        right;left
        rw [show (SerializedBody.machine.step s b).1=next from rfl,terminal,md]
        rfl
      · right;right
        exact ⟨next,mm,zero,one,rfl⟩
private theorem run (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (inside : Region k c.state) (t : Nat) : Region k ((machine k).run t c).state:=by
  induction t with
  | zero=>exact inside
  | succ t ih=>exact step k _ _ ih
/-- Every BODY state and both literal terminals form a real transition trap.
Thus a later native work endpoint proves absence of ALL earlier BODY entries
and verdicts; endpoint equality alone would not establish that firstness. -/
private theorem prefix_outside (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (t : Nat) (outside : ¬Region k ((machine k).run t c).state) :
    ∀ u,u≤t → ¬Region k ((machine k).run u c).state:=by
  intro u hu earlier
  have later:=run k ((machine k).run u c) earlier (t-u)
  rw [←UniformTM.run_add,show u+(t-u)=t by omega] at later
  exact outside later
private theorem native_outside (k i m : Nat) (hi : i<239) (hm : m<144) : ¬Region k (nc k i m):=by
  have quotient : (nc k i m).val/144=(CertificateGuardClosure.machine k).stateCount+i:=
    (packDiv k ((CertificateGuardClosure.machine k).stateCount+i) m (by omega) hm).1
  rintro (equal|equal|⟨s,md,_s0,_s1,equal⟩)
  · have eq:=congrArg (fun q=>q.val/144) equal
    dsimp only at eq
    have pin:=controlQuotient k (CertificateGuardClosure.machine k).accept ⟨8,by decide⟩
    change (machine k).accept.val/144=(CertificateGuardClosure.machine k).accept.val at pin
    rw [quotient,pin] at eq
    have fit:=(CertificateGuardClosure.machine k).accept.isLt
    omega
  · have eq:=congrArg (fun q=>q.val/144) equal
    dsimp only at eq
    have pin:=controlQuotient k (CertificateGuardClosure.machine k).reject ⟨8,by decide⟩
    change (machine k).reject.val/144=(CertificateGuardClosure.machine k).reject.val at pin
    rw [quotient,pin] at eq
    have fit:=(CertificateGuardClosure.machine k).reject.isLt
    omega
  · have eq:=congrArg (fun q=>q.val/144) equal
    dsimp only at eq
    rw [quotient,controlQuotient] at eq
    have fit:=(full k s).isLt
    omega
private theorem leaf_outside (k : Nat) (b : Bool) (m : Fin 144) :
    ¬Region k (control k (leafControl k b) m):=by
  have source:=leafValue k b
  have large:=carryLarge k
  rintro (equal|equal|⟨s,md,s0,s1,equal⟩)
  · have eq:=congrArg (fun q=>q.val/144) equal
    dsimp only at eq
    have pin:=controlQuotient k (CertificateGuardClosure.machine k).accept ⟨8,by decide⟩
    change (machine k).accept.val/144=(CertificateGuardClosure.machine k).accept.val at pin
    rw [controlQuotient,pin] at eq
    have val : (CertificateGuardClosure.machine k).accept.val=414:=rfl
    rw [val,source] at eq
    unfold Cursor.stateCount at eq
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at eq <;> omega
  · have eq:=congrArg (fun q=>q.val/144) equal
    dsimp only at eq
    have pin:=controlQuotient k (CertificateGuardClosure.machine k).reject ⟨8,by decide⟩
    change (machine k).reject.val/144=(CertificateGuardClosure.machine k).reject.val at pin
    rw [controlQuotient,pin] at eq
    have val : (CertificateGuardClosure.machine k).reject.val=415:=rfl
    rw [val,source] at eq
    unfold Cursor.stateCount at eq
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at eq <;> omega
  · have eq:=congrArg (fun q=>q.val/144) equal
    dsimp only at eq
    rw [controlQuotient,controlQuotient,source,fullValue k s s0 s1] at eq
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at eq <;> omega
private theorem safe (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (t : Nat) (outside : ¬Region k ((machine k).run t c).state) :
    ∀ u,u≤t → ((machine k).run u c).state≠(machine k).accept ∧
      ((machine k).run u c).state≠(machine k).reject ∧
      ∀ (mode : Fin 3) (flag : Fin 144),((machine k).run u c).state≠control k
        (CertificateGuardClosure.old k (TotalIngressClosure.old k
          (BodyIngress.body k (SerializedBody.entry mode)))) flag:=by
  intro u hu
  have no:=prefix_outside k c t outside u hu
  refine ⟨fun eq=>no (Or.inl eq),fun eq=>no (Or.inr (Or.inl eq)),?_⟩
  intro mode flag eq
  apply no
  right;right
  exact ⟨SerializedBody.entry mode,flag,by fin_cases mode <;> decide,by fin_cases mode <;> decide,eq⟩
#print axioms Region_type
#print axioms step
#print axioms run
#print axioms prefix_outside
#print axioms native_outside
#print axioms leaf_outside
#print axioms safe
end VirtualFinalClosure.BodyTrap
