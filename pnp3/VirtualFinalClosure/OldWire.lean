import VirtualFinalClosure.BaseCursorRows
namespace VirtualFinalClosure.OldWire
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_value","packValue",(1:Nat)),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_div","packDiv",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","rawStep","raw",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldStep",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual old-control wire interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual old-control wire interface {mod}/{key}"
/-- Actual product-row expansion for ANY finite mode, not just phase0. It
retains the terminal normalizer and makes no passive-projection assumption. -/
private theorem old_step (k : Nat) (q : Fin (CertificateGuardClosure.machine k).stateCount)
    (m : Nat) (b : Option Bool) (hm : m < 144)
    (na : q≠(CertificateGuardClosure.machine k).accept)
    (nr : q≠(CertificateGuardClosure.machine k).reject) :
    (machine k).step (control k q ⟨m,hm⟩) b=
      (let a:=oldStep k q.val m b
       (pack k a.1 (if a.1=(CertificateGuardClosure.machine k).accept.val ∨
         a.1=(CertificateGuardClosure.machine k).reject.val then 8 else a.2.1),a.2.2)) := by
  have bound : q.val < (CertificateGuardClosure.machine k).stateCount+239 := by
    have h:=q.isLt
    omega
  have value:=packValue k q.val m bound hm
  have div:=packDiv k q.val m bound hm
  have terminal:=terminalValues k
  have noAccept : pack k q.val m≠(machine k).accept := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [value,terminal.1] at values
    apply na
    exact Fin.ext (by omega)
  have noReject : pack k q.val m≠(machine k).reject := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [value,terminal.2] at values
    apply nr
    exact Fin.ext (by omega)
  change (machine k).step (pack k q.val m) b=_
  rw [UniformTM.step_of_ne (machine k) noAccept noReject b]
  change raw k (pack k q.val m) b=_
  dsimp only [raw]
  rw [div.1,div.2,if_pos q.isLt]
  rfl
#print axioms old_step
end VirtualFinalClosure.OldWire
