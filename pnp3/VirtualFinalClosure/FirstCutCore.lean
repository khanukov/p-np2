import VirtualFinalClosure.ReferenceCut
import VirtualFinalClosure.Prefix
import VirtualFinalClosure.Resources
namespace VirtualFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ReferenceCut","VirtualFinalClosure.ReferenceCut","raw_frontier","parentFrontier",(1:Nat)),
      ("VirtualFinalClosure.ReferenceCut","VirtualFinalClosure.ReferenceCut","first_event","firstEvent",1),
      ("VirtualFinalClosure.ReferenceCut","VirtualFinalClosure.ReferenceCut","isFrontier","parentControl",0),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","every_prefix","everyPrefix",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","lift","liftPrefix",0),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_le_new","oldNew",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_prefix_extension","extendPrefix",1),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_div","packDiv",1)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong raw first-cut term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique raw first-cut term {mod}/{key}"
private theorem extended_read {states N C B : Nat} (h : C ≤ B) (c : Config states N C) :
    (IngressAllocation.extendConfig h c).tape (IngressAllocation.extendConfig h c).head=c.tape c.head := by
  change (if hi : c.head.val < tapeLength N C then c.tape ⟨c.head.val,hi⟩ else none)=c.tape c.head
  rw [dif_pos c.head.isLt]
private theorem extended_intercept (k : Nat) {N C B : Nat} (h : C ≤ B)
    (c : Config (CertificateGuardClosure.machine k).stateCount N C) :
    Intercept k (IngressAllocation.extendConfig h c).state
      ((IngressAllocation.extendConfig h c).tape (IngressAllocation.extendConfig h c).head) ↔
      Intercept k c.state (c.tape c.head) := by
  rw [extended_read]
  rfl
private theorem quotient_control (k : Nat) (q : Fin (CertificateGuardClosure.machine k).stateCount)
    (flag : Fin 144) : (control k q flag).val/144=q.val :=
  (packDiv k q.val flag.val (by have h:=q.isLt;omega) flag.isLt).1
private theorem control_injective (k : Nat) (q r : Fin (CertificateGuardClosure.machine k).stateCount)
    (f g : Fin 144) (same : control k q f=control k r g) : q=r := by
  apply Fin.ext
  exact (quotient_control k q f).symm.trans ((congrArg (fun s=>s.val/144) same).trans (quotient_control k r g))
private theorem inclusion_absent (k : Nat) {N B : Nat} (old : Config (CertificateGuardClosure.machine k).stateCount N B)
    (flag : Fin 144) (a : old.state ≠ (CertificateGuardClosure.machine k).accept)
    (noReject : old.state ≠ (CertificateGuardClosure.machine k).reject) :
    (config k flag old).state ≠ (machine k).accept ∧ (config k flag old).state ≠ (machine k).reject := by
  constructor
  · intro bad
    exact a (control_injective k old.state (CertificateGuardClosure.machine k).accept flag ⟨8,by decide⟩ bad)
  · intro bad
    exact noReject (control_injective k old.state (CertificateGuardClosure.machine k).reject flag ⟨8,by decide⟩ bad)
private theorem included_state (k : Nat) {N C B : Nat} (h : C ≤ B) (flag : Fin 144)
    (small : Config (CertificateGuardClosure.machine k).stateCount N C) :
    (config k flag (IngressAllocation.extendConfig h small)).state=control k small.state flag := by rfl
private theorem control_absent (k : Nat)
    (q : Fin (CertificateGuardClosure.machine k).stateCount) (flag : Fin 144)
    (s : Fin (machine k).stateCount) (eq : s=control k q flag)
    (noAccept : q ≠ (CertificateGuardClosure.machine k).accept)
    (noReject : q ≠ (CertificateGuardClosure.machine k).reject)
    (noBody : ∀ mode : Fin 3,q ≠ CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.body k (SerializedBody.entry mode)))) :
    s ≠ (machine k).accept ∧ s ≠ (machine k).reject ∧
      ∀ (mode : Fin 3) (m : Fin 144),s ≠ control k (CertificateGuardClosure.old k
        (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) m := by
  subst s
  refine ⟨?_,?_,?_⟩
  · intro bad
    exact noAccept (control_injective k q (CertificateGuardClosure.machine k).accept flag ⟨8,by decide⟩ bad)
  · intro bad
    exact noReject (control_injective k q (CertificateGuardClosure.machine k).reject flag ⟨8,by decide⟩ bad)
  · intro mode m bad
    exact noBody mode (control_injective k q _ flag m bad)
private def Event (k : Nat) {N B : Nat} (c : Config (CertificateGuardClosure.machine k).stateCount N B) : Prop :=
  c.state=(CertificateGuardClosure.machine k).reject ∨
    (∃ mode : Fin 3,c.state=CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.body k (SerializedBody.entry mode)))) ∨ Intercept k c.state (c.tape c.head)
private theorem first_cut_core : ∀ (k N : Nat) (y : Bitstring N),
    let O:=CertificateGuardClosure.machine k;let C:=CertificateGuardClosure.allocation k N
    let B:=allocation k N;let c:=initialConfig O C y;let big:=initialConfig (machine k) B y
    ∃ (s : Nat) (h : C ≤ B),s ≤ CertificateGuardClosure.deadline k N ∧
      (∀ u,u ≤ s → (O.run u c).state ≠ O.accept) ∧
      (∀ u,u ≤ s → (O.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ s → ∃ f : Fin 4,(machine k).run u big=
        config k ⟨8+f.val,by have hf:=f.isLt;omega⟩
          (IngressAllocation.extendConfig h (O.run u c))) ∧
      (∀ u,u < s → ((machine k).run u big).state ≠ (machine k).accept ∧
        ((machine k).run u big).state ≠ (machine k).reject ∧
        ∀ (mode : Fin 3) (flag : Fin 144),((machine k).run u big).state ≠ control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) flag) ∧
      (∀ u,u < s → ¬Intercept k (O.run u c).state ((O.run u c).tape (O.run u c).head)) ∧
      Event k (O.run s c) := by
  intro k N y O C B c big
  obtain ⟨t,price,heads,safe,front⟩:=parentFrontier k N y
  have last : Event k (O.run t c) := by
    rcases front with rejected|leaf|body
    · exact Or.inl (Fin.ext rejected)
    · obtain ⟨b,hit⟩:=leaf
      cases b
      · exact Or.inr (Or.inr (Or.inl (Or.inl (Fin.ext hit))))
      · exact Or.inr (Or.inr (Or.inl (Or.inr (Fin.ext hit))))
    · obtain ⟨mode,hit⟩:=body
      exact Or.inr (Or.inl ⟨mode,Fin.ext hit⟩)
  obtain ⟨s,st,event,first⟩:=firstEvent (M:=O) c (Event k) t last
  let h:=oldNew k N
  have before (u : Nat) (hu : u < s) : ¬Intercept k (O.run u c).state ((O.run u c).tape (O.run u c).head) := by
    intro hit
    exact first u hu (Or.inr (Or.inr hit))
  have onLarge (u : Nat) (hu : u ≤ s) : O.run u (initialConfig O B y)=IngressAllocation.extendConfig h (O.run u c) :=
    extendPrefix k N t y heads u (hu.trans st)
  have allowed (u : Nat) (hu : u < s) :
      ¬Intercept k (O.run u (initialConfig O B y)).state
        ((O.run u (initialConfig O B y)).tape (O.run u (initialConfig O B y)).head) := by
    rw [onLarge u hu.le]
    exact fun bad=>before u hu ((extended_intercept k h (O.run u c)).1 bad)
  have runs (u : Nat) (hu : u ≤ s) : ∃ f : Fin 4,(machine k).run u big=
      config k ⟨8+f.val,by have hf:=f.isLt;omega⟩ (IngressAllocation.extendConfig h (O.run u c)) := by
    obtain ⟨f,run⟩:=everyPrefix k B y s allowed u hu
    refine ⟨f,?_⟩
    change (machine k).run u big=config k _ (O.run u (initialConfig O B y)) at run
    exact run.trans (congrArg (config k _) (onLarge u hu))
  refine ⟨s,h,st.trans price,fun u hu=>safe u (hu.trans st),fun u hu=>heads u (hu.trans st),runs,?_,before,event⟩
  intro u hu
  obtain ⟨f,eq⟩:=runs u hu.le
  let flag : Fin 144:=⟨8+f.val,by have hf:=f.isLt;omega⟩
  have stateEq : ((machine k).run u big).state=control k (O.run u c).state flag :=
    (congrArg Config.state eq).trans (included_state k h flag (O.run u c))
  exact control_absent k (O.run u c).state flag ((machine k).run u big).state stateEq
    (safe u (hu.le.trans st)) (fun hit=>first u hu (Or.inl hit))
    (fun mode hit=>first u hu (Or.inr (Or.inl ⟨mode,hit⟩)))

#print axioms first_cut_core
end VirtualFinalClosure
