import VirtualFinalClosure.WideCursorRows
import VirtualFinalClosure.BaseCursorRows
namespace VirtualFinalClosure.FullCursorRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entryValue",(1:Nat)),
      ("CarryWindow.Rows","CarryWindow","oldq_val","oldqValue",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p0","p0",0),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p1","p1",0),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p0_value","p0Value",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p1_value","p1Value",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","total_row","totalRow",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","certificate_row","certificateRow",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","full_state","fullState",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual full arithmetic component row {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual full arithmetic component row {mod}/{key}"
private theorem canonical (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 798+93*k) :
    (CanonicalLeaf.machine k).step (p1 k q) b=
      (p1 k ((Cursor.machine k).step q b).1,((Cursor.machine k).step q b).2) := by
  have ne : p0 k q≠VirtualLeaf.entry k := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [p0Value,entryValue] at values
    omega
  have row:=CanonicalLeaf.repaired_rows k (p0 k q) b
  rw [if_neg (fun h=>ne h.1)] at row
  have repaired : (IngressRepair.machine k).step (p0 k q) b=
      (p0 k ((Cursor.machine k).step q b).1,((Cursor.machine k).step q b).2) := by
    dsimp only [IngressRepair.machine,p0]
    rw [UniformTM.seq_step_right]
  rw [repaired] at row
  exact row
private theorem carry (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 798+93*k) (ne430 : q.val≠430+93*k) (ne613 : q.val≠613+93*k) :
    (CarryWindow.machine k).step (CarryWindow.embed k (p1 k q)) b=
      (CarryWindow.embed k (p1 k ((Cursor.machine k).step q b).1),((Cursor.machine k).step q b).2) := by
  have notSpecial (i : Nat) (different : q.val≠i) (bound : i < Cursor.stateCount k) :
      p1 k q≠VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i)) := by
    intro equal
    have values:=congrArg Fin.val equal
    have v : (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i))).val=288+i:=oldqValue k i bound
    rw [p1Value,v] at values
    omega
  rw [CarryWindow.table_delta,
    if_neg (fun h=>notSpecial (430+93*k) ne430 (by unfold Cursor.stateCount;omega) h.1),
    if_neg (fun h=>notSpecial (613+93*k) ne613 (by unfold Cursor.stateCount;omega) h.1),canonical k q b upper]
private theorem body (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 798+93*k) (ne430 : q.val≠430+93*k) (ne613 : q.val≠613+93*k) :
    (BodyIngress.machine k).step (BodyIngress.old k (CarryWindow.embed k (p1 k q))) b=
      (BodyIngress.old k (CarryWindow.embed k (p1 k ((Cursor.machine k).step q b).1)),((Cursor.machine k).step q b).2) := by
  have notReady : CarryWindow.embed k (p1 k q)≠CarryWindow.ready k := by
    intro equal
    have values:=congrArg Fin.val equal
    change (p1 k q).val=(CanonicalLeaf.machine k).stateCount+24 at values
    have bound:=(p1 k q).isLt
    omega
  rw [BodyIngress.table_delta,if_neg (fun h=>notReady h.1),carry k q b upper ne430 ne613]
/-- All repaired component rows below final W-cap; the two old CarryWindow
hooks are explicitly excluded, never silently copied onto phase1 replay. -/
private theorem base_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (upper : q.val < 798+93*k) (ne430 : q.val≠430+93*k) (ne613 : q.val≠613+93*k) :
    (CertificateGuardClosure.machine k).step (tableControl k q.val) b=
      (tableControl k ((Cursor.machine k).step q b).1.val,((Cursor.machine k).step q b).2) := by
  rw [←fullState k q,←fullState k ((Cursor.machine k).step q b).1]
  rw [certificateRow,totalRow,body k q b upper ne430 ne613]
#print axioms canonical
#print axioms carry
#print axioms body
#print axioms base_row
end VirtualFinalClosure.FullCursorRows
