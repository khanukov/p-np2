import VirtualFinalClosure.OldWire
import VirtualFinalClosure.InterceptRows
import VirtualFinalClosure.CleanupRows
import CanonicalLeaf.Body
namespace VirtualFinalClosure.LeafComponent
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","total_row","totalRow",(1:Nat)),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","certificate_row","certificateRow",1),
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual canonical-leaf component term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual canonical-leaf component term {mod}/{key}"
private def full (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) : Fin (CertificateGuardClosure.machine k).stateCount:=
  CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.old k (CarryWindow.embed k s)))
private def full_type : ∀ k,Fin (CanonicalLeaf.machine k).stateCount → Fin (CertificateGuardClosure.machine k).stateCount:=full
private theorem full_value (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) : (full k s).val=87+s.val:=by
  dsimp only [full,CertificateGuardClosure.old,TotalIngressClosure.old,BodyIngress.old,CarryWindow.embed,UniformTM.seqRight]
  change 10+(67+(10+s.val))=87+s.val
  omega
private theorem component (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (b : Option Bool)
    (lower : 1224+93*k ≤ s.val) :
    (CertificateGuardClosure.machine k).step (full k s) b=
      (full k ((CanonicalLeaf.machine k).step s b).1,((CanonicalLeaf.machine k).step s b).2):=by
  have noHook (i : Nat) (small : i < 936+93*k) (fit : i < Cursor.stateCount k) :
      s≠VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i)):=by
    intro e;have h:=congrArg Fin.val e
    change s.val=288+i%Cursor.stateCount k at h
    rw [Nat.mod_eq_of_lt fit] at h
    omega
  have cr : (CarryWindow.machine k).step (CarryWindow.embed k s) b=
      (CarryWindow.embed k ((CanonicalLeaf.machine k).step s b).1,((CanonicalLeaf.machine k).step s b).2):=by
    rw [CarryWindow.table_delta,if_neg (fun h=>noHook (430+93*k) (by omega) (by unfold Cursor.stateCount;omega) h.1),
      if_neg (fun h=>noHook (613+93*k) (by omega) (by unfold Cursor.stateCount;omega) h.1)]
  have noReady : CarryWindow.embed k s≠CarryWindow.ready k:=by
    intro e;have h:=congrArg Fin.val e
    dsimp only [CarryWindow.embed,CarryWindow.ready,CarryWindow.extra] at h
    have fit:=s.isLt
    omega
  dsimp only [full]
  rw [certificateRow,totalRow,BodyIngress.table_delta,if_neg (fun h=>noReady h.1),cr]
private theorem body_above (k : Nat) (j : Fin 3) :
    87+(CanonicalLeaf.machine k).stateCount ≤ (bodyControl k j).val := by
  fin_cases j
  · change 87+(288+Cursor.stateCount k+8) ≤ 10+(67+(10+((288+Cursor.stateCount k+8+25)+4)))
    omega
  · change 87+(288+Cursor.stateCount k+8) ≤ 10+(67+(10+((288+Cursor.stateCount k+8+25)+5)))
    omega
  · change 87+(288+Cursor.stateCount k+8) ≤ 10+(67+(10+((288+Cursor.stateCount k+8+25)+6)))
    omega
private theorem old_row (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (m : Fin 144) (b : Option Bool)
    (ph : phase m.val=2) (lower : 1224+93*k ≤ s.val)
    (upper : s.val < 288+Cursor.stateCount k+6) :
    oldRow k (full k s).val m.val b=
      ((full k ((CanonicalLeaf.machine k).step s b).1).val,m.val,((CanonicalLeaf.machine k).step s b).2):=by
  let O:=CertificateGuardClosure.machine k
  let q:=full k s
  have hs : (⟨q.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=q:=Fin.ext (Nat.mod_eq_of_lt q.isLt)
  have noLeaves : ¬(q=leafControl k false ∨ q=leafControl k true):=by
    have no (v : Bool) : q≠leafControl k v:=by
      intro e;have h:=congrArg Fin.val e
      change (full k s).val=(leafControl k v).val at h
      rw [full_value,leafValue] at h
      cases v <;> norm_num at h <;> omega
    exact fun h=>h.elim (no false) (no true)
  dsimp only [oldRow]
  rw [hs,if_neg noLeaves,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have row:=component k s b lower
  change O.step q b=(full k ((CanonicalLeaf.machine k).step s b).1,((CanonicalLeaf.machine k).step s b).2) at row
  rw [row]
  dsimp only
  have noBody : ¬∃ j,full k ((CanonicalLeaf.machine k).step s b).1=bodyControl k j:=by
    rintro ⟨j,e⟩;have h:=congrArg Fin.val e
    rw [full_value] at h
    have fit:=((CanonicalLeaf.machine k).step s b).1.isLt
    have above:=body_above k j
    omega
  rw [if_neg noBody]
  have noPaid (i : Nat) (small : i < 936+93*k) (fit : i < Cursor.stateCount k) : q≠tableControl k i:=by
    intro e;have h:=congrArg Fin.val e
    change (full k s).val=(tableControl k i).val at h
    rw [full_value,tableValue k i fit] at h
    omega
  rw [if_neg (fun h=>noPaid 43 (by omega) (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noPaid 47 (by omega) (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noPaid 51 (by omega) (by unfold Cursor.stateCount;omega) h.2)]
#print axioms full_type
#print axioms full_value
#print axioms component
#print axioms body_above
#print axioms old_row
end VirtualFinalClosure.LeafComponent
