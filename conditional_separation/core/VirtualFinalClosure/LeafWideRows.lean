import VirtualFinalClosure.LeafComponent
namespace VirtualFinalClosure.LeafWideRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full","full",(0:Nat)),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full_value","fullValue",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","component","component",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","body_above","bodyAbove",1),
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",0),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_value","packValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual canonical five-edge replay term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual canonical five-edge replay term {mod}/{key}"
private theorem old_row (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (m : Fin 144) (b : Option Bool)
    (lower : 1224+93*k ≤ s.val)
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
      rw [fullValue,leafValue] at h
      cases v <;> norm_num at h <;> omega
    exact fun h=>h.elim (no false) (no true)
  have noHook (i : Nat) (small : i < 936+93*k) (fit : i < Cursor.stateCount k) : q≠tableControl k i:=by
    intro e;have h:=congrArg Fin.val e
    change (full k s).val=(tableControl k i).val at h
    rw [fullValue,tableValue k i fit] at h
    omega
  dsimp only [oldRow]
  rw [hs,if_neg noLeaves]
  rw [if_neg (by
    intro h
    rcases h.2.2 with h|h
    · exact noHook 250 (by omega) (by unfold Cursor.stateCount;omega) h
    · exact noHook 304 (by omega) (by unfold Cursor.stateCount;omega) h)]
  rw [if_neg (fun h=>noHook (798+93*k) (by omega) (by unfold Cursor.stateCount;omega) h.2.2)]
  rw [if_neg (fun h=>noHook (430+93*k) (by omega) (by unfold Cursor.stateCount;omega) h.2)]
  rw [if_neg (fun h=>noHook (613+93*k) (by omega) (by unfold Cursor.stateCount;omega) h.2.2)]
  have row:=component k s b lower
  change O.step q b=(full k ((CanonicalLeaf.machine k).step s b).1,((CanonicalLeaf.machine k).step s b).2) at row
  rw [row]
  dsimp only
  have noBody : ¬∃ j,full k ((CanonicalLeaf.machine k).step s b).1=bodyControl k j:=by
    rintro ⟨j,e⟩;have h:=congrArg Fin.val e
    rw [fullValue] at h
    have fit:=((CanonicalLeaf.machine k).step s b).1.isLt
    have above:=bodyAbove k j
    omega
  rw [if_neg noBody]
  have noPaid (i : Nat) (small : i < 936+93*k) (fit : i < Cursor.stateCount k) : q≠tableControl k i:=by
    intro e;have h:=congrArg Fin.val e
    change (full k s).val=(tableControl k i).val at h
    rw [fullValue,tableValue k i fit] at h
    omega
  rw [if_neg (fun h=>noPaid 43 (by omega) (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noPaid 47 (by omega) (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noPaid 51 (by omega) (by unfold Cursor.stateCount;omega) h.2)]
private theorem effective (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (m : Fin 144) (b : Option Bool)
    (lower : 1224+93*k ≤ s.val) (upper : s.val < 288+Cursor.stateCount k+6)
    (after : 1224+93*k ≤ ((CanonicalLeaf.machine k).step s b).1.val) :
    (machine k).step (control k (full k s) m) b=
      (control k (full k ((CanonicalLeaf.machine k).step s b).1) m,((CanonicalLeaf.machine k).step s b).2):=by
  have noSource (v : Bool) : full k s≠(if v then (CertificateGuardClosure.machine k).accept else (CertificateGuardClosure.machine k).reject):=by
    intro e;have h:=congrArg Fin.val e
    cases v
    · rw [if_neg (by decide),fullValue,(oldTerminals k).2] at h;omega
    · rw [if_pos rfl,fullValue,(oldTerminals k).1] at h;omega
  rw [wire k (full k s) m.val b m.isLt (noSource true) (noSource false),old_row k s m b lower upper]
  dsimp only
  rw [if_neg (by rw [fullValue,(oldTerminals k).1,(oldTerminals k).2];omega)]
  rfl
private theorem reject_value (k : Nat) : (CanonicalLeaf.machine k).reject.val=328:=by
  change 288+40%Cursor.stateCount k=328
  rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]
private theorem reject_row (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (m : Fin 144)
    (b w : Option Bool) (mv : Move)
    (lower : 1224+93*k ≤ s.val) (upper : s.val < 288+Cursor.stateCount k+6)
    (old : (CanonicalLeaf.machine k).step s b=((CanonicalLeaf.machine k).reject,w,mv)) :
    (machine k).step (control k (full k s) m) b=((machine k).reject,w,mv):=by
  have na : full k s≠(CertificateGuardClosure.machine k).accept:=by
    intro e;have h:=congrArg Fin.val e
    rw [fullValue,(oldTerminals k).1] at h;omega
  have nr : full k s≠(CertificateGuardClosure.machine k).reject:=by
    intro e;have h:=congrArg Fin.val e
    rw [fullValue,(oldTerminals k).2] at h;omega
  have rej : full k (CanonicalLeaf.machine k).reject=(CertificateGuardClosure.machine k).reject:=by
    apply Fin.ext
    rw [fullValue,reject_value,(oldTerminals k).2]
  have rv : (CertificateGuardClosure.machine k).reject.val < (CertificateGuardClosure.machine k).stateCount:=Fin.isLt _
  have finalPack : pack k (CertificateGuardClosure.machine k).reject.val 8=(machine k).reject:=by
    apply Fin.ext
    rw [packValue k _ 8 (by omega) (by decide),(terminalValues k).2]
  rw [wire k (full k s) m.val b m.isLt na nr,old_row k s m b lower upper,old]
  dsimp only
  rw [rej]
  have normalization : (CertificateGuardClosure.machine k).reject.val=(CertificateGuardClosure.machine k).accept.val ∨
      (CertificateGuardClosure.machine k).reject.val=(CertificateGuardClosure.machine k).reject.val:=Or.inr rfl
  rw [if_pos normalization]
  exact congrArg (fun s=>(s,w,mv)) finalPack
#print axioms old_row
#print axioms effective
#print axioms reject_value
#print axioms reject_row
end VirtualFinalClosure.LeafWideRows
