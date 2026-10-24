import VirtualFinalClosure.TerminalRow
import VirtualFinalClosure.NormalRun
import VirtualFinalClosure.FirstLiteral
namespace VirtualFinalClosure.RejectedPrefix
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.FirstLiteral","VirtualFinalClosure.FirstLiteral","first","firstLiteral",(1:Nat)),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","low_safe","lowSafe",1),
      ("VirtualFinalClosure.TerminalRow","VirtualFinalClosure.TerminalRow","config_reject","lastStep",1),

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
      unless actual=kind do throwError "Wrong full NORMAL actualPrefix transport term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique full NORMAL actualPrefix transport {mod}/{key}"
private theorem low_body (k : Nat) (q : Fin (CertificateGuardClosure.machine k).stateCount)
    (low : q.val < 625) (mode : Fin 3) : q≠bodyControl k mode:=by
  intro eq
  have high:=bodyAbove k mode
  change 87+(288+Cursor.stateCount k+8) ≤ (bodyControl k mode).val at high
  unfold Cursor.stateCount at high
  have value:=congrArg Fin.val eq
  omega
/-- A genuinely reached low-control literal reject is transported at its FIRST
actual time. The final executed transition itself normalizes metadata8; no
waiting deadline or proof-side state rewrite is used. -/
private theorem rejected (k N t : Nat) (y : Bitstring N)
    (heads : ∀ u,u ≤ t → ((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).head.val ≤ 12*(N+1)^2)
    (low : ∀ u,u ≤ t → ((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state.val < 625)
    (hit : ((CertificateGuardClosure.machine k).run t
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state=(CertificateGuardClosure.machine k).reject) :
    let O:=CertificateGuardClosure.machine k;let C:=CertificateGuardClosure.allocation k N;let B:=allocation k N
    let old:=initialConfig O C y;let c:=initialConfig (machine k) B y;let h:=oldNew k N
    ∃ s,s ≤ t ∧ (O.run s old).state=O.reject ∧
      (machine k).run s c=config k ⟨8,by decide⟩ (IngressAllocation.extendConfig h (O.run s old)) ∧
      (∀ u,u < s → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (j : Fin 3) (flag : Fin 144),((machine k).run u c).state≠control k (bodyControl k j) flag) ∧
      (∀ u,u ≤ s → ((machine k).run u c).head.val ≤ 12*(N+1)^2):=by
  intro O C B old c h
  obtain ⟨s,st,first,same⟩:=firstLiteral O old t
  have arrived : (O.run s old).state=O.reject:=(congrArg (fun q=>q.state) same).trans hit
  have positive : 0 < s:=by
    by_contra notPositive
    have zero : s=0:=by omega
    rw [zero] at arrived
    have value:=congrArg Fin.val arrived
    change 0=415 at value
    omega
  have extended:=extendPrefix k N t y heads
  have safeBig (u : Nat) (hu : u < s) :
      ¬Intercept k (O.run u (initialConfig O B y)).state
        ((O.run u (initialConfig O B y)).tape (O.run u (initialConfig O B y)).head):=by
    rw [extended u (hu.le.trans st),extendedIntercept]
    exact lowSafe k _ _ (low u (hu.le.trans st))
  have actualPrefix:=everyPrefix k B y s safeBig
  have prev : s-1 < s:=by omega
  obtain ⟨f,atPrevious⟩:=actualPrefix (s-1) prev.le
  have oldStep : O.stepConfig (O.run (s-1) (initialConfig O B y))=O.run s (initialConfig O B y):=by
    change O.run (s-1+1) (initialConfig O B y)=_
    rw [Nat.sub_add_cancel positive]
  have rejectAtStep : (O.stepConfig (O.run (s-1) (initialConfig O B y))).state=O.reject:=by
    have oldState : (IngressAllocation.extendConfig h (O.run s old)).state=(O.run s old).state:=Fin.ext (extendState h _)
    exact (congrArg (fun q=>q.state) (oldStep.trans (extended s st))).trans (oldState.trans arrived)
  have final : (machine k).run s c=config k ⟨8,by decide⟩ (IngressAllocation.extendConfig h (O.run s old)):=by
    have normalize:=lastStep k (O.run (s-1) (initialConfig O B y)) f (safeBig _ prev) rejectAtStep
    have actual : (machine k).run s c=(machine k).stepConfig ((machine k).run (s-1) c):=by
      conv_lhs=>rw [show s=s-1+1 by omega]
      rfl
    exact actual.trans ((congrArg (fun q=>(machine k).stepConfig q) atPrevious).trans
      (normalize.trans (congrArg (fun q=>config k ⟨8,by decide⟩ q) (oldStep.trans (extended s st)))))
  refine ⟨s,st,arrived,final,?_,?_⟩
  · intro u hu
    obtain ⟨f,eq⟩:=actualPrefix u hu.le
    let flag : Fin 144:=⟨8+f.val,by have h:=f.isLt;omega⟩
    have full : (machine k).run u c=config k flag (IngressAllocation.extendConfig h (O.run u old)):=
      eq.trans (congrArg (config k flag) (extended u (hu.le.trans st)))
    have value:= (congrArg (fun q=>q.state) full).trans (includedState k h flag (O.run u old))
    exact controlAbsent k _ flag _ value (first u hu).1 (first u hu).2 (low_body k _ (low u (hu.le.trans st)))
  · intro u hu
    obtain ⟨f,eq⟩:=actualPrefix u hu
    let flag : Fin 144:=⟨8+f.val,by have h:=f.isLt;omega⟩
    have full : (machine k).run u c=config k flag (IngressAllocation.extendConfig h (O.run u old)):=
      eq.trans (congrArg (config k flag) (extended u (hu.trans st)))
    have value:=congrArg (fun q=>q.head.val) full
    exact (value.trans ((includeHead k flag _).trans (extendHead h (O.run u old)))).trans_le (heads u (hu.trans st))
#print axioms low_body
#print axioms rejected
end VirtualFinalClosure.RejectedPrefix
