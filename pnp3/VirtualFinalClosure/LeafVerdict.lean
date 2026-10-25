import VirtualFinalClosure.ConfigStay
import VirtualFinalClosure.OldWire
import VirtualFinalClosure.InterceptRows
namespace VirtualFinalClosure.LeafVerdict
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ConfigStay","VirtualFinalClosure.ConfigStay","one","oneStay",(1:Nat)),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_value","packValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",0),
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",(1:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual FINAL-dispatch term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual FINAL-dispatch term {mod}/{key}"
private theorem row (k : Nat) (value : Bool) (m : Fin 144) (b : Option Bool) :
    (machine k).step (control k (leafControl k value) m) b=
      (if flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,b,.stay):=by
  let O:=CertificateGuardClosure.machine k
  let q:=leafControl k value
  have na : q≠O.accept:=by
    intro e;have h:=congrArg Fin.val e
    change (leafControl k value).val=(CertificateGuardClosure.machine k).accept.val at h
    rw [leafValue,(oldTerminals k).1] at h
    unfold Cursor.stateCount at h
    cases value <;> omega
  have nr : q≠O.reject:=by
    intro e;have h:=congrArg Fin.val e
    change (leafControl k value).val=(CertificateGuardClosure.machine k).reject.val at h
    rw [leafValue,(oldTerminals k).2] at h
    unfold Cursor.stateCount at h
    cases value <;> omega
  have hs : (⟨q.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=q:=Fin.ext (Nat.mod_eq_of_lt q.isLt)
  have literal : oldRow k q.val m.val b=
      ((if flag m.val%2=1 ∧ bad m.val=0 then O.accept else O.reject).val,m.val,b,.stay):=by
    dsimp only [oldRow]
    have member : q=leafControl k false ∨ q=leafControl k true:=by
      by_cases h : value=false
      · exact Or.inl (congrArg (leafControl k) h)
      · exact Or.inr (congrArg (leafControl k) (Bool.eq_true_of_not_eq_false h))
    rw [hs,if_pos member]
  have oa : O.accept.val < (CertificateGuardClosure.machine k).stateCount:=O.accept.isLt
  have orj : O.reject.val < (CertificateGuardClosure.machine k).stateCount:=O.reject.isLt
  have toAccept : pack k O.accept.val 8=(machine k).accept:=by
    apply Fin.ext
    rw [packValue k _ 8 (by omega) (by decide),(terminalValues k).1]
  have toReject : pack k O.reject.val 8=(machine k).reject:=by
    apply Fin.ext
    rw [packValue k _ 8 (by omega) (by decide),(terminalValues k).2]
  rw [wire k q m.val b m.isLt na nr,literal]
  dsimp only
  by_cases good : flag m.val%2=1 ∧ bad m.val=0
  · have normalization : O.accept.val=(CertificateGuardClosure.machine k).accept.val ∨
        O.accept.val=(CertificateGuardClosure.machine k).reject.val:=Or.inl rfl
    simpa only [if_pos good,if_pos normalization] using congrArg (fun s=>(s,b,Move.stay)) toAccept
  · have normalization : O.reject.val=(CertificateGuardClosure.machine k).accept.val ∨
        O.reject.val=(CertificateGuardClosure.machine k).reject.val:=Or.inr rfl
    simpa only [if_neg good,if_pos normalization] using congrArg (fun s=>(s,b,Move.stay)) toReject
/-- One REAL literal FINAL row after canonical WORK leaf. WORKfalse is not a
reject condition: the independently accumulated table/prefix predicates decide.
No source semantics/rho fact is smuggled into this transition theorem. -/
private theorem run_one (k N B : Nat) (value : Bool) (m : Fin 144)
    (h : Fin (tapeLength N B)) (T : Fin (tapeLength N B) → Option Bool) :
    (machine k).run 1 ⟨control k (leafControl k value) m,h,T⟩=
      ⟨if flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,h,T⟩:=by
  exact oneStay _ _ h T (row k value m (T h))
#print axioms row
#print axioms run_one
end VirtualFinalClosure.LeafVerdict
