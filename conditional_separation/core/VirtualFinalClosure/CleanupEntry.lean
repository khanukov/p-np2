import VirtualFinalClosure.GrowEntry
import VirtualFinalClosure.MetaFields
import VirtualFinalClosure.EventValues
namespace VirtualFinalClosure.CleanupEntry
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","native_step","nativeStep",(1:Nat)),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","tail_def","tailDef",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","tailWith","tailWith",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","evalTail","evalTail",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","readCode","readCode",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","romPin","rom",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","tailStep","tailStep",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolve",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","mode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","encodeMeta","encodeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual arithmetic reentry interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual arithmetic reentry interface {mod}/{key}"
private theorem cleanup_phase (m : Nat) : phase (changeMeta 7 m)=2 := by
  dsimp only [changeMeta,phase,encodeMeta,flag,mode,seen,bad]
  omega
/-- The final literal guard row enters the ORIGINAL dirty-bank cleanup D0
with phase2, physically bypassing the cap interception on the NEXT real edge. -/
private theorem cleanup_row (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 238 m) none=
      (control k (tableControl k (798+93*k)) ⟨changeMeta 7 m,metaBound 7 m⟩,none,.stay) := by
  have cell : rom[714]?=some (247,0,1,7) := by run_tac cellTac 714
  have evaluation : tailStep k 238 m none=
      ((tableControl k (798+93*k)).val,changeMeta 7 m,none,.stay) := by
    rw [tailDef]
    dsimp only [tailWith,readCode]
    rw [cell]
    rfl
  have ha : (tableControl k (798+93*k)).val≠(CertificateGuardClosure.machine k).accept.val := by
    rw [tableValue k (798+93*k) (by unfold Cursor.stateCount;omega)]
    change 375+(798+93*k)≠414
    omega
  have hr : (tableControl k (798+93*k)).val≠(CertificateGuardClosure.machine k).reject.val := by
    rw [tableValue k (798+93*k) (by unfold Cursor.stateCount;omega)]
    change 375+(798+93*k)≠415
    omega
  dsimp only [nc]
  rw [nativeStep k 238 m none (by decide) hm,evaluation]
  dsimp only
  have notTerminal : ¬((tableControl k (798+93*k)).val=(CertificateGuardClosure.machine k).accept.val ∨
      (tableControl k (798+93*k)).val=(CertificateGuardClosure.machine k).reject.val) := not_or_intro ha hr
  rw [if_neg notTerminal]
  rfl
#print axioms cleanup_phase
#print axioms cleanup_row
end VirtualFinalClosure.CleanupEntry
