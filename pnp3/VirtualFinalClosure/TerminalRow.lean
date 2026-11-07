import VirtualFinalClosure.NormalRow
namespace VirtualFinalClosure.TerminalRow
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","row_projection","rowProjection",(1:Nat)),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",0),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","config_row","configRow",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","lift","lift",0),
      ("VirtualFinalClosure.NormalRow","VirtualFinalClosure.NormalRow","control_value","controlValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_div","packDiv",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","rawStep","rawStep",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal rejection normalizer {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal rejection normalizer {mod}/{key}"
private theorem raw_reject (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (f : Fin 4) (b : Option Bool) (safe : ¬Intercept k s b)
    (arrived : ((CertificateGuardClosure.machine k).step s b).1=(CertificateGuardClosure.machine k).reject) :
    (machine k).rawStep (control k s ⟨8+f.val,by have h:=f.isLt;omega⟩) b=
      ((machine k).reject,((CertificateGuardClosure.machine k).step s b).2):=by
  obtain ⟨g,row⟩:=rowProjection k s f b safe
  have div:=packDiv k s.val (8+f.val) (by have h:=s.isLt;omega) (by have h:=f.isLt;omega)
  change rawStep k (pack k s.val (8+f.val)) b=_
  dsimp only [rawStep]
  rw [div.1,div.2,if_pos s.isLt,row,if_pos (Or.inr (congrArg Fin.val arrived)),arrived]
  rfl
private theorem step_reject (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (f : Fin 4) (b : Option Bool) (safe : ¬Intercept k s b)
    (arrived : ((CertificateGuardClosure.machine k).step s b).1=(CertificateGuardClosure.machine k).reject) :
    (machine k).step (control k s ⟨8+f.val,by have h:=f.isLt;omega⟩) b=
      ((machine k).reject,((CertificateGuardClosure.machine k).step s b).2):=by
  have noAccept : control k s ⟨8+f.val,by have h:=f.isLt;omega⟩≠(machine k).accept:=by
    intro eq
    have value:=congrArg Fin.val eq
    rw [controlValue,(terminalValues k).1] at value
    have old : s=(CertificateGuardClosure.machine k).accept:=Fin.ext (by have h:=f.isLt;omega)
    rw [old,UniformTM.step_accept] at arrived
    exact (CertificateGuardClosure.machine k).accept_ne_reject arrived
  by_cases terminal : control k s ⟨8+f.val,by have h:=f.isLt;omega⟩=(machine k).reject
  · have value:=congrArg Fin.val terminal
    rw [controlValue,(terminalValues k).2] at value
    have old : s=(CertificateGuardClosure.machine k).reject:=Fin.ext (by have h:=f.isLt;omega)
    rw [terminal,old,UniformTM.step_reject,UniformTM.step_reject]
  · rw [UniformTM.step_of_ne (machine k) noAccept terminal b]
    exact raw_reject k s f b safe arrived
private theorem config_reject (k : Nat) {N B : Nat}
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) (f : Fin 4)
    (safe : ¬Intercept k c.state (c.tape c.head))
    (arrived : ((CertificateGuardClosure.machine k).stepConfig c).state=(CertificateGuardClosure.machine k).reject) :
    (machine k).stepConfig (lift k f c)=config k ⟨8,by decide⟩ ((CertificateGuardClosure.machine k).stepConfig c):=by
  have row:=step_reject k c.state f (c.tape c.head) safe arrived
  refine (configRow c _ _ row).trans ?_
  apply Config.ext_parts
  · change (machine k).reject=control k ((CertificateGuardClosure.machine k).stepConfig c).state ⟨8,by decide⟩
    rw [arrived]
    rfl
  · rfl
  · rfl
#print axioms raw_reject
#print axioms step_reject
#print axioms config_reject
end VirtualFinalClosure.TerminalRow
