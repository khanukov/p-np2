import VirtualFinalClosure.OriginalRows
import VirtualFinalClosure.RawLengthLift
import VirtualFinalClosure.ConfigFields
namespace VirtualFinalClosure.EventValues
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl"),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl"),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.defnInfo ci)]=>
      logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique concrete intercept-control value {mod}/{key}"
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.RawLengthLift","VirtualFinalClosure.RawLengthLift","embed_state","embedState"),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","guarded","guardedState"),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","total","totalState"),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","sequential","sequentialState")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique shallow configuration field interface {mod}/{key}"
private theorem table_value (k i : Nat) (hi : i<Cursor.stateCount k) : (tableControl k i).val=375+i := by
  change 10+(67+(10+(288+i%Cursor.stateCount k)))=375+i
  rw [Nat.mod_eq_of_lt hi]
  omega
private theorem leaf_value (k : Nat) (b : Bool) :
    (leafControl k b).val=375+Cursor.stateCount k+(if b then 7 else 6) := by
  cases b
  · change 10+(67+(10+(288+Cursor.stateCount k+6)))=375+Cursor.stateCount k+6
    omega
  · change 10+(67+(10+(288+Cursor.stateCount k+7)))=375+Cursor.stateCount k+7
    omega
private theorem low_safe (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (b : Option Bool) (low : s.val<625) : ¬Intercept k s b := by
  have leafLow (value : Bool) : 625≤(leafControl k value).val := by
    rw [leaf_value]
    unfold Cursor.stateCount
    cases value <;> omega
  have tableLow (i : Nat) (range : i=250 ∨ i=304 ∨ i=798+93*k) : 625≤(tableControl k i).val := by
    rw [table_value k i (by rcases range with rfl|rfl|rfl <;> unfold Cursor.stateCount <;> omega)]
    rcases range with rfl|rfl|rfl <;> omega
  intro bad
  rcases bad with leaf|⟨_none,caps⟩
  · rcases leaf with hit|hit
    · exact (Nat.ne_of_lt (lt_of_lt_of_le low (leafLow false))) (congrArg Fin.val hit)
    · exact (Nat.ne_of_lt (lt_of_lt_of_le low (leafLow true))) (congrArg Fin.val hit)
  · rcases caps with hit|hit|hit
    · exact (Nat.ne_of_lt (lt_of_lt_of_le low (tableLow 250 (Or.inl rfl)))) (congrArg Fin.val hit)
    · exact (Nat.ne_of_lt (lt_of_lt_of_le low (tableLow 304 (Or.inr (Or.inl rfl))))) (congrArg Fin.val hit)
    · exact (Nat.ne_of_lt (lt_of_lt_of_le low (tableLow _ (Or.inr (Or.inr rfl))))) (congrArg Fin.val hit)
/-- Exact prefix-control identification through repaired/canonical/carry/ingress
embeddings. It does not identify runs of different families without transport. -/
private theorem embedded_table (k : Nat) (q : Fin (Cursor.machine k).stateCount)
    {N B : Nat} (h : Fin (tapeLength N B)) (T : Fin (tapeLength N B) → Option Bool) :
    (CertificateGuardClosure.config k (TotalIngressClosure.config k (BodyIngress.config k
      (CarryWindow.config k (VirtualLeaf.config k (SmallIngress.producer.seqEmbedRight (Cursor.machine k) ⟨q,h,T⟩)))))).state=
      tableControl k q.val := by
  apply Fin.ext
  rw [guardedState,totalState,embedState,sequentialState,table_value k q.val q.isLt]
  change 77+(10+(288+q.val))=375+q.val
  omega
#print axioms table_value
#print axioms leaf_value
#print axioms low_safe
#print axioms embedded_table
end VirtualFinalClosure.EventValues
