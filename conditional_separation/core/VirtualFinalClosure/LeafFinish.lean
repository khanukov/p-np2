import VirtualFinalClosure.LeafFive
import VirtualFinalClosure.LeafVerdict
import VirtualFinalClosure.FirstCutCore
namespace VirtualFinalClosure.LeafFinish
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LeafFive","VirtualFinalClosure.LeafFive","prepared","five",(1:Nat)),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","result","result",0),
      ("VirtualFinalClosure.LeafVerdict","VirtualFinalClosure.LeafVerdict","run_one","finalRow",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","inclusion_absent","includedSafe",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual canonical FINAL execution term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual canonical FINAL execution term {mod}/{key}"
private theorem leaf_work (k : Nat) (value : Bool) :
    leafControl k value≠(CertificateGuardClosure.machine k).accept ∧
    leafControl k value≠(CertificateGuardClosure.machine k).reject:=by
  constructor <;> intro e <;> have h:=congrArg Fin.val e
  · rw [leafValue,(oldTerminals k).1] at h
    unfold Cursor.stateCount at h
    cases value <;> omega
  · rw [leafValue,(oldTerminals k).2] at h
    unfold Cursor.stateCount at h
    cases value <;> omega
/-- Canonical arbitrary-beta virtual input0 is really read and written by five
rows, then the SIXTH literal row decides using independently accumulated flags.
A false computed beta0 is never treated as a rejection condition. -/
private theorem prepared (k N B P L n : Nat) (m : Fin 144) (T : Nat → Option Bool)
    (beta : Fin n → Bool) (pos : 0 < n) (fit : L+n+1 ≤ P) (finite : P < tapeLength N B)
    (sep : T L=none) (last : T (L+n+1)=none)
    (digits : ∀ j : Fin n,T (L+n-j.val)=some (beta j)) :
    let hH : L+n+1 < tapeLength N B:=lt_of_le_of_lt fit finite
    let c : Config (machine k).stateCount N B:=⟨ready k m,⟨L+n+1,hH⟩,fun j=>T j.val⟩
    (machine k).run 6 c=
      ⟨if flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
        ⟨L+n+1,hH⟩,fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val⟩ ∧
    (∀ u,u<6 → ((machine k).run u c).state≠(machine k).accept ∧
      ((machine k).run u c).state≠(machine k).reject) ∧
    (∀ u,u≤6 → ((machine k).run u c).head.val≤P):=by
  intro hH c
  have path:=five k P L n m T beta fit sep last digits
  rw [dif_pos pos] at path
  have done : (machine k).run 5 c=
      ⟨result k m (beta ⟨0,pos⟩),⟨L+n+1,hH⟩,fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val⟩:=execute path finite
  have lastEdge:=finalRow k N B (beta ⟨0,pos⟩) m ⟨L+n+1,hH⟩
    (fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val)
  have actual : (machine k).run 6 c=
      ⟨if flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
        ⟨L+n+1,hH⟩,fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val⟩:=by
    change (machine k).run (5+1) c=_
    rw [UniformTM.run_add,done]
    exact lastEdge
  have safeEnd : ((machine k).run 5 c).state≠(machine k).accept ∧
      ((machine k).run 5 c).state≠(machine k).reject:=by
    rw [done]
    exact includedSafe k ⟨leafControl k (beta ⟨0,pos⟩),⟨L+n+1,hH⟩,
      fun j=>put T (L+n+1) (some (beta ⟨0,pos⟩)) j.val⟩ m
      (leaf_work k _).1 (leaf_work k _).2
  refine ⟨actual,?_,?_⟩
  · intro u hu
    exact (machine k).no_terminal_of_le c safeEnd.1 safeEnd.2 u (by omega)
  · intro u hu
    by_cases early : u≤5
    · exact through path finite u early
    · have same : u=6:=by omega
      subst u
      rw [actual]
      exact fit
#print axioms leaf_work
#print axioms prepared
end VirtualFinalClosure.LeafFinish
