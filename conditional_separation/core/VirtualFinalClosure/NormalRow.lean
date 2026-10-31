import VirtualFinalClosure.Prefix
import VirtualFinalClosure.FirstCutCore
import VirtualFinalClosure.LeafComponent
namespace VirtualFinalClosure.NormalRow
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",(0:Nat)),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","original_phase","phaseZero",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","config_row","configRow",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","lift","lift",0),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","control_injective","injective",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_div","packDiv",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_value","packValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldStep",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","rawStep","rawStep",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","body_above","bodyAbove",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal NORMAL normalization row {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal NORMAL normalization row {mod}/{key}"
private theorem control_value (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) (f : Fin 4) :
    (control k s ⟨8+f.val,by have h:=f.isLt;omega⟩).val=144*s.val+(8+f.val):=
  packValue k s.val (8+f.val) (by have h:=s.isLt;omega) (by have h:=f.isLt;omega)
private theorem terminal_absent (k : Nat) (mode : Fin 3) :
    bodyControl k mode≠(CertificateGuardClosure.machine k).accept ∧
      bodyControl k mode≠(CertificateGuardClosure.machine k).reject:=by
  have high:=bodyAbove k mode
  change 87+(288+Cursor.stateCount k+8)≤(bodyControl k mode).val at high
  unfold Cursor.stateCount at high
  constructor
  · intro eq;have value:=congrArg Fin.val eq
    change (bodyControl k mode).val=414 at value
    omega
  · intro eq;have value:=congrArg Fin.val eq
    change (bodyControl k mode).val=415 at value
    omega
/-- The actual oldStep dispatch writes metadata8 when its real next control is
ANY BODY entry. This is the literal normalizing row, not a post-run retag. -/
private theorem old_row (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (f : Fin 4) (b : Option Bool) (mode : Fin 3) (safe : ¬Intercept k s b)
    (arrived : ((CertificateGuardClosure.machine k).step s b).1=bodyControl k mode) :
    oldStep k s.val (8+f.val) b=
      ((bodyControl k mode).val,8,((CertificateGuardClosure.machine k).step s b).2):=by
  let O:=CertificateGuardClosure.machine k
  have hs : (⟨s.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=s:=Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have leaves : ¬(s=leafControl k false ∨ s=leafControl k true):=fun h=>safe (Or.inl h)
  have caps : b=none → ¬(s=tableControl k 250 ∨ s=tableControl k 304 ∨ s=tableControl k (798+93*k)):=
    fun blank hit=>safe (Or.inr ⟨blank,hit⟩)
  dsimp only [oldStep]
  rw [hs,if_neg leaves]
  rw [if_neg (by intro h;exact caps h.2.1 (by rcases h.2.2 with left|right;exact Or.inl left;exact Or.inr (Or.inl right)))]
  rw [if_neg (by intro h;exact caps h.2.1 (Or.inr (Or.inr h.2.2)))]
  have phase:=phaseZero f
  rw [if_neg (by intro h;rw [phase] at h;omega),if_neg (by intro h;rw [phase] at h;omega)]
  rw [if_pos ⟨mode,arrived⟩,arrived]
  rfl
private theorem step (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (f : Fin 4) (b : Option Bool) (mode : Fin 3) (safe : ¬Intercept k s b)
    (arrived : ((CertificateGuardClosure.machine k).step s b).1=bodyControl k mode) :
    (machine k).step (control k s ⟨8+f.val,by have h:=f.isLt;omega⟩) b=
      (control k (bodyControl k mode) ⟨8,by decide⟩,((CertificateGuardClosure.machine k).step s b).2):=by
  have noOldAccept : s≠(CertificateGuardClosure.machine k).accept:=by
    intro eq
    rw [eq,UniformTM.step_accept] at arrived
    exact (terminal_absent k mode).1 arrived.symm
  have noOldReject : s≠(CertificateGuardClosure.machine k).reject:=by
    intro eq
    rw [eq,UniformTM.step_reject] at arrived
    exact (terminal_absent k mode).2 arrived.symm
  have noAccept : control k s ⟨8+f.val,by have h:=f.isLt;omega⟩≠(machine k).accept:=by
    intro eq
    have value:=congrArg Fin.val eq
    rw [control_value,(terminalValues k).1] at value
    exact noOldAccept (Fin.ext (by have bound:=f.isLt;omega))
  have noReject : control k s ⟨8+f.val,by have h:=f.isLt;omega⟩≠(machine k).reject:=by
    intro eq
    have value:=congrArg Fin.val eq
    rw [control_value,(terminalValues k).2] at value
    exact noOldReject (Fin.ext (by have bound:=f.isLt;omega))
  rw [UniformTM.step_of_ne (machine k) noAccept noReject b]
  change rawStep k (pack k s.val (8+f.val)) b=_
  have bounds:=packDiv k s.val (8+f.val) (by have h:=s.isLt;omega) (by have h:=f.isLt;omega)
  dsimp only [rawStep]
  rw [bounds.1,bounds.2,if_pos s.isLt,old_row k s f b mode safe arrived]
  change (pack k (bodyControl k mode).val (if _ then 8 else 8),_)=_
  rw [ite_self]
  rfl
private theorem config_step (k : Nat) {N B : Nat} (c : Config (CertificateGuardClosure.machine k).stateCount N B)
    (f : Fin 4) (mode : Fin 3) (safe : ¬Intercept k c.state (c.tape c.head))
    (arrived : ((CertificateGuardClosure.machine k).stepConfig c).state=bodyControl k mode) :
    (machine k).stepConfig (lift k f c)=config k ⟨8,by decide⟩ ((CertificateGuardClosure.machine k).stepConfig c):=by
  have row:=step k c.state f (c.tape c.head) mode safe arrived
  rw [←arrived] at row
  exact configRow c _ _ row
#print axioms control_value
#print axioms terminal_absent
#print axioms old_row
#print axioms step
#print axioms config_step
end VirtualFinalClosure.NormalRow
