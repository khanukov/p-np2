import VirtualFinalClosure.ReplayBounds
import CanonicalLeaf.Rows
import CarryWindow.Rows
import BodyIngress.Transport
namespace VirtualFinalClosure.WideCursorRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entryValue",(1:Nat)),
      ("CarryWindow.Rows","CarryWindow","oldq_val","oldqValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong repaired Cursor row interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique repaired Cursor row interface {mod}/{key}"
private def p0 (k : Nat) (q : Fin (Cursor.machine k).stateCount) : Fin (IngressRepair.machine k).stateCount :=
  IngressRepair.producer.seqRight (Cursor.machine k) q
private def p1 (k : Nat) (q : Fin (Cursor.machine k).stateCount) : Fin (CanonicalLeaf.machine k).stateCount :=
  VirtualLeaf.embed k (p0 k q)
private def p0_type : ∀ k,Fin (Cursor.machine k).stateCount → Fin (IngressRepair.machine k).stateCount := p0
private def p1_type : ∀ k,Fin (Cursor.machine k).stateCount → Fin (CanonicalLeaf.machine k).stateCount := p1
private theorem p0_value (k : Nat) (q : Fin (Cursor.machine k).stateCount) : (p0 k q).val=288+q.val := by rfl
private theorem p1_value (k : Nat) (q : Fin (Cursor.machine k).stateCount) : (p1 k q).val=288+q.val := by rfl
private theorem canonical_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 430) :
    (CanonicalLeaf.machine k).step (p1 k q) b=
      (p1 k ((Cursor.machine k).step q b).1,((Cursor.machine k).step q b).2) := by
  have notEntry : p0 k q≠VirtualLeaf.entry k := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [p0_value,entryValue] at values
    omega
  have row:=CanonicalLeaf.repaired_rows k (p0 k q) b
  rw [if_neg (fun h=>notEntry h.1)] at row
  have base : (IngressRepair.machine k).step (p0 k q) b=
      (p0 k ((Cursor.machine k).step q b).1,((Cursor.machine k).step q b).2) := by
    dsimp only [IngressRepair.machine,p0]
    rw [UniformTM.seq_step_right]
  rw [base] at row
  exact row
private theorem carry_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 430) :
    (CarryWindow.machine k).step (CarryWindow.embed k (p1 k q)) b=
      (CarryWindow.embed k (p1 k ((Cursor.machine k).step q b).1),((Cursor.machine k).step q b).2) := by
  have notSpecial (i : Nat) (large : 430 ≤ i) (bound : i < Cursor.stateCount k) :
      p1 k q≠VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i)) := by
    have value : (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i))).val=288+i :=
      oldqValue k i bound
    intro equal
    have values:=congrArg Fin.val equal
    rw [p1_value,value] at values
    omega
  have ne430:=notSpecial (430+93*k) (by omega) (by unfold Cursor.stateCount;omega)
  have ne613:=notSpecial (613+93*k) (by omega) (by unfold Cursor.stateCount;omega)
  rw [CarryWindow.table_delta,if_neg (fun h=>ne430 h.1),if_neg (fun h=>ne613 h.1),canonical_row k q b upper]
private theorem body_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 430) :
    (BodyIngress.machine k).step (BodyIngress.old k (CarryWindow.embed k (p1 k q))) b=
      (BodyIngress.old k (CarryWindow.embed k (p1 k ((Cursor.machine k).step q b).1)),
        ((Cursor.machine k).step q b).2) := by
  have notReady : CarryWindow.embed k (p1 k q)≠CarryWindow.ready k := by
    intro equal
    have values:=congrArg Fin.val equal
    change (p1 k q).val=(CanonicalLeaf.machine k).stateCount+24 at values
    have bound:=(p1 k q).isLt
    omega
  rw [BodyIngress.table_delta,if_neg (fun h=>notReady h.1),carry_row k q b upper]
private theorem total_row (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) (b : Option Bool) :
    (TotalIngressClosure.machine k).step (TotalIngressClosure.old k s) b=
      (TotalIngressClosure.old k ((BodyIngress.machine k).step s b).1,((BodyIngress.machine k).step s b).2) := by
  dsimp only [TotalIngressClosure.machine,TotalIngressClosure.old]
  rw [UniformTM.seq_step_right]
private theorem certificate_row (k : Nat) (s : Fin (TotalIngressClosure.machine k).stateCount) (b : Option Bool) :
    (CertificateGuardClosure.machine k).step (CertificateGuardClosure.old k s) b=
      (CertificateGuardClosure.old k ((TotalIngressClosure.machine k).step s b).1,((TotalIngressClosure.machine k).step s b).2) := by
  dsimp only [CertificateGuardClosure.machine,CertificateGuardClosure.old]
  rw [UniformTM.seq_step_right,UniformTM.seq_step_right]
private theorem full_state (k : Nat) (q : Fin (Cursor.machine k).stateCount) :
    CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.old k (CarryWindow.embed k (p1 k q))))=
      tableControl k q.val := by
  have eta : Cursor.q k q.val=q := by
    apply Fin.ext
    change q.val%Cursor.stateCount k=q.val
    exact Nat.mod_eq_of_lt q.isLt
  dsimp only [tableControl,p1,p0]
  rw [eta]
/-- Literal row equality through ALL repaired component embeddings. This is
not a run retag: phase1 finite-mode projection and actual replay follow later. -/
private theorem base_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 430) :
    (CertificateGuardClosure.machine k).step (tableControl k q.val) b=
      (tableControl k ((Cursor.machine k).step q b).1.val,((Cursor.machine k).step q b).2) := by
  rw [←full_state k q,←full_state k ((Cursor.machine k).step q b).1]
  rw [certificate_row,total_row,body_row k q b upper]
#print axioms p0_type
#print axioms p1_type
#print axioms p0_value
#print axioms p1_value
#print axioms canonical_row
#print axioms carry_row
#print axioms body_row
#print axioms total_row
#print axioms certificate_row
#print axioms full_state
#print axioms base_row
end VirtualFinalClosure.WideCursorRows
