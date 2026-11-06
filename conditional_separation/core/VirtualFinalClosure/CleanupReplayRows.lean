import VirtualFinalClosure.CleanupRows
import VirtualFinalClosure.OldWire
import VirtualFinalClosure.InterceptRows
namespace VirtualFinalClosure.CleanupReplayRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.CleanupRows","VirtualFinalClosure.CleanupRows","base_row","baseRow",1),
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual phase2 cleanup row interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual phase2 cleanup row interface {mod}/{key}"
private theorem body_high (k : Nat) (j : Fin 3) : 375+Cursor.stateCount k < (bodyControl k j).val:=by
  fin_cases j
  · change 375+Cursor.stateCount k < 10+(67+(10+((288+Cursor.stateCount k+8+25)+4)))
    omega
  · change 375+Cursor.stateCount k < 10+(67+(10+((288+Cursor.stateCount k+8+25)+5)))
    omega
  · change 375+Cursor.stateCount k < 10+(67+(10+((288+Cursor.stateCount k+8+25)+6)))
    omega
/-- Literal PHASE2 cleanup rows; the active cap/length hooks are disabled by
an actual finite metadata phase, never by a proof-side retag. -/
private theorem old_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (m : Nat) (b : Option Bool)
    (ph : phase m=2) (lower : 798+93*k ≤ q.val) (noReady : q.val≠936+93*k) :
    oldRow k (tableControl k q.val).val m b=
      ((tableControl k ((Cursor.machine k).step q b).1.val).val,m,((Cursor.machine k).step q b).2):=by
  let O:=CertificateGuardClosure.machine k
  let s:=tableControl k q.val
  have hs : (⟨s.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=s:=Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have leaves : ¬(s=leafControl k false ∨ s=leafControl k true):=by
    have noLeaf (v : Bool) : s≠leafControl k v:=by
      intro equal
      have val:=congrArg Fin.val equal
      change (tableControl k q.val).val=(leafControl k v).val at val
      rw [tableValue k q.val q.isLt,leafValue] at val
      have fit:=q.isLt
      change q.val < Cursor.stateCount k at fit
      cases v <;> omega
    exact fun h=>h.elim (noLeaf false) (noLeaf true)
  dsimp only [oldRow]
  rw [hs,if_neg leaves,if_neg (by intro h;exact h.1 ph),if_neg (by intro h;exact h.1 ph),
    if_neg (by intro h;have impossible:=h.1;rw [ph] at impossible;cases impossible),
    if_neg (by intro h;have impossible:=h.1;rw [ph] at impossible;cases impossible)]
  have row:=baseRow k q b noReady (by omega) (by omega)
  change O.step s b=(tableControl k ((Cursor.machine k).step q b).1.val,((Cursor.machine k).step q b).2) at row
  rw [row]
  dsimp only
  have noBody : ¬∃ j : Fin 3,tableControl k ((Cursor.machine k).step q b).1.val=bodyControl k j:=by
    rintro ⟨j,equal⟩
    have val:=congrArg Fin.val equal
    rw [tableValue k ((Cursor.machine k).step q b).1.val ((Cursor.machine k).step q b).1.isLt] at val
    have high:=body_high k j
    have fit:=((Cursor.machine k).step q b).1.isLt
    change ((Cursor.machine k).step q b).1.val < Cursor.stateCount k at fit
    omega
  have different (i : Nat) (small : i < 798+93*k) (bound : i < Cursor.stateCount k) : s≠tableControl k i:=by
    intro equal
    have val:=congrArg Fin.val equal
    change (tableControl k q.val).val=(tableControl k i).val at val
    rw [tableValue k q.val q.isLt,tableValue k i bound] at val
    omega
  rw [if_neg noBody,
    if_neg (fun h=>different 43 (by omega) (by unfold Cursor.stateCount;omega) h.2),
    if_neg (fun h=>different 47 (by omega) (by unfold Cursor.stateCount;omega) h.2),
    if_neg (fun h=>different 51 (by omega) (by unfold Cursor.stateCount;omega) h.2)]
private theorem effective (k : Nat) (q : Fin (Cursor.machine k).stateCount) (m : Fin 144) (b : Option Bool)
    (ph : phase m.val=2) (lower : 798+93*k ≤ q.val) (noReady : q.val≠936+93*k)
    (afterLo : 798+93*k ≤ ((Cursor.machine k).step q b).1.val) :
    (machine k).step (control k (tableControl k q.val) m) b=
      (control k (tableControl k ((Cursor.machine k).step q b).1.val) m,((Cursor.machine k).step q b).2):=by
  have value:=tableValue k q.val q.isLt
  have nextValue:=tableValue k ((Cursor.machine k).step q b).1.val ((Cursor.machine k).step q b).1.isLt
  have terms:=oldTerminals k
  have na : tableControl k q.val≠(CertificateGuardClosure.machine k).accept:=by
    intro equal
    have val:=congrArg Fin.val equal
    rw [value,terms.1] at val
    omega
  have nr : tableControl k q.val≠(CertificateGuardClosure.machine k).reject:=by
    intro equal
    have val:=congrArg Fin.val equal
    rw [value,terms.2] at val
    omega
  rw [wire k (tableControl k q.val) m.val b m.isLt na nr,old_row k q m.val b ph lower noReady]
  dsimp only
  rw [if_neg (by rw [nextValue,terms.1,terms.2];omega)]
  rfl
#print axioms body_high
#print axioms old_row
#print axioms effective
end VirtualFinalClosure.CleanupReplayRows
