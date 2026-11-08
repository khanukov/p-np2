import VirtualFinalClosure.NormalRow
import VirtualFinalClosure.OldVirtualTrapLift
import VirtualFinalClosure.Resources
import VirtualFinalClosure.HeadFields
namespace VirtualFinalClosure.NormalRun
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.OldVirtualTrapLift","VirtualFinalClosure.OldVirtualTrapLift","before_body","beforeBody",(1:Nat)),
      ("VirtualFinalClosure.NormalRow","VirtualFinalClosure.NormalRow","config_step","lastStep",1),
      ("VirtualFinalClosure.NormalRow","VirtualFinalClosure.NormalRow","terminal_absent","bodyNotTerminal",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_le_new","oldNew",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_prefix_extension","extendPrefix",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","every_prefix","everyPrefix",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","lift","lift",0),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","extended_intercept","extendedIntercept",1),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",0),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","control_absent","controlAbsent",1),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","included_state","includedState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","extension","extendState",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","extension","extendHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","included","includeHead",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","body_above","bodyAbove",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong full NORMAL prefix transport term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique full NORMAL prefix transport {mod}/{key}"
private theorem extended_state {states N C B : Nat} (h : C ≤ B) (c : Config states N C) :
    (IngressAllocation.extendConfig h c).state=c.state:=Fin.ext (extendState h c)
/-- Actual varying flag on EVERY old raw edge, with the literal final BODY
entry reset to8. The same larger tape is transported by the OLD head footprint,
not elapsed ≤ old allocation and not an endpoint-only fixed flag claim. -/
private theorem normal_prefix (k N t : Nat) (y : Bitstring N) (mode : Fin 3)
    (heads : ∀ u,u ≤ t → ((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).head.val ≤ 12*(N+1)^2)
    (arrived : ((CertificateGuardClosure.machine k).run t
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state=bodyControl k mode)
    (first : ∀ u,u < t →
      ((CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state≠(CertificateGuardClosure.machine k).accept ∧
      ((CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state≠(CertificateGuardClosure.machine k).reject ∧
      ∀ j : Fin 3,((CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state≠bodyControl k j) :
    let O:=CertificateGuardClosure.machine k;let C:=CertificateGuardClosure.allocation k N;let B:=allocation k N
    let old:=initialConfig O C y;let c:=initialConfig (machine k) B y;let h:=oldNew k N
    (∀ u,u ≤ t → ∃ flag : Fin 144,(machine k).run u c=config k flag (IngressAllocation.extendConfig h (O.run u old))) ∧
      (machine k).run t c=config k ⟨8,by decide⟩ (IngressAllocation.extendConfig h (O.run t old)) ∧
      (∀ u,u < t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (j : Fin 3) (flag : Fin 144),((machine k).run u c).state≠control k (bodyControl k j) flag) ∧
      (∀ u,u ≤ t → ((machine k).run u c).head.val ≤ 12*(N+1)^2):=by
  intro O C B old c h
  have extended:=extendPrefix k N t y heads
  have noIntercept:=beforeBody k old t mode arrived
  have safeBig (u : Nat) (hu : u < t) :
      ¬Intercept k
        (O.run u (initialConfig O B y)).state ((O.run u (initialConfig O B y)).tape (O.run u (initialConfig O B y)).head):=by
    rw [extended u hu.le,extendedIntercept]
    exact noIntercept u hu.le
  have rawPrefix:=everyPrefix k B y t safeBig
  have allPrefix (u : Nat) (hu : u ≤ t) : ∃ flag : Fin 144,
      (machine k).run u c=config k flag (IngressAllocation.extendConfig h (O.run u old)):=by
    obtain ⟨f,eq⟩:=rawPrefix u hu
    change (machine k).run u c=config k ⟨8+f.val,by have bound:=f.isLt;omega⟩ (O.run u (initialConfig O B y)) at eq
    rw [extended u hu] at eq
    exact ⟨_,eq⟩
  have positive : 0 < t:=by
    by_contra zero
    have eq : t=0:=by omega
    rw [eq] at arrived
    have value:=congrArg Fin.val arrived
    change 0=(bodyControl k mode).val at value
    have large:=bodyAbove k mode
    omega
  have prev : t-1 < t:=by omega
  obtain ⟨f,atPrevious⟩:=rawPrefix (t-1) prev.le
  have oldStep : O.stepConfig (O.run (t-1) (initialConfig O B y))=O.run t (initialConfig O B y):=by
    change O.run (t-1+1) (initialConfig O B y)=_
    rw [Nat.sub_add_cancel positive]
  have bodyAtStep : (O.stepConfig (O.run (t-1) (initialConfig O B y))).state=bodyControl k mode:=by
    have atBig : (O.run t (initialConfig O B y)).state=bodyControl k mode:=
      (congrArg (fun q=>q.state) (extended t le_rfl)).trans ((extended_state h (O.run t old)).trans arrived)
    exact (congrArg (fun q=>q.state) oldStep).trans atBig
  have final : (machine k).run t c=config k ⟨8,by decide⟩ (IngressAllocation.extendConfig h (O.run t old)):=by
    have normalize:=lastStep k (O.run (t-1) (initialConfig O B y)) f mode (safeBig _ prev) bodyAtStep
    have actual : (machine k).run t c=(machine k).stepConfig ((machine k).run (t-1) c):=by
      conv_lhs=>rw [show t=t-1+1 by omega]
      rfl
    exact actual.trans ((congrArg (fun q=>(machine k).stepConfig q) atPrevious).trans
      (normalize.trans (congrArg (fun q=>config k ⟨8,by decide⟩ q) (oldStep.trans (extended t le_rfl)))))
  refine ⟨allPrefix,final,?_,?_⟩
  · intro u hu
    obtain ⟨flag,eq⟩:=allPrefix u hu.le
    obtain ⟨na,nr,nb⟩:=first u hu
    have stateEq : ((machine k).run u c).state=control k (O.run u old).state flag:=
      (congrArg (fun q=>q.state) eq).trans (includedState k h flag (O.run u old))
    exact controlAbsent k (O.run u old).state flag ((machine k).run u c).state stateEq na nr nb
  · intro u hu
    obtain ⟨flag,eq⟩:=allPrefix u hu
    have value:=congrArg (fun q=>q.head.val) eq
    exact (value.trans ((includeHead k flag _).trans (extendHead h (O.run u old)))).trans_le (heads u hu)
#print axioms extended_state
#print axioms normal_prefix
end VirtualFinalClosure.NormalRun
