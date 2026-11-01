import VirtualFinalClosure.FullReplayRows
import VirtualFinalClosure.OldWire
import VirtualFinalClosure.InterceptRows
namespace VirtualFinalClosure.FullEarlyRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.FullReplayRows","VirtualFinalClosure.FullReplayRows","body_high","bodyHigh",(1:Nat)),
      ("VirtualFinalClosure.FullCursorRows","VirtualFinalClosure.FullCursorRows","base_row","baseRow",(1:Nat)),
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual active replay row interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual active replay row interface {mod}/{key}"
private theorem old_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (m : Nat) (b : Option Bool)
    (no430 : q.val≠430+93*k) (lower : 98 ≤ q.val) (upper : q.val < 798+93*k)
    (no250 : q.val≠250) (no304 : q.val≠304) (no613 : q.val≠613+93*k)
    (afterHi : ((Cursor.machine k).step q b).1.val ≤ 798+93*k) :
    oldRow k (tableControl k q.val).val m b=
      ((tableControl k ((Cursor.machine k).step q b).1.val).val,m,((Cursor.machine k).step q b).2) := by
  let O:=CertificateGuardClosure.machine k
  let s:=tableControl k q.val
  have hs : (⟨s.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=s:=Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have different (i : Nat) (bound : i < Cursor.stateCount k) (ne : q.val≠i) : s≠tableControl k i := by
    intro equal
    have val:=congrArg Fin.val equal
    change (tableControl k q.val).val=(tableControl k i).val at val
    rw [tableValue k q.val q.isLt,tableValue k i bound] at val
    omega
  have leaves : ¬(s=leafControl k false ∨ s=leafControl k true) := by
    have ne (v : Bool) : s≠leafControl k v := by
      intro equal
      have val:=congrArg Fin.val equal
      change (tableControl k q.val).val=(leafControl k v).val at val
      rw [tableValue k q.val q.isLt,leafValue] at val
      unfold Cursor.stateCount at val
      cases v <;> omega
    exact fun h=>h.elim (ne false) (ne true)
  dsimp only [oldRow]
  rw [hs,if_neg leaves]
  rw [if_neg (by
    intro h
    rcases h.2.2 with h|h
    · exact different 250 (by unfold Cursor.stateCount;omega) no250 h
    · exact different 304 (by unfold Cursor.stateCount;omega) no304 h)]
  rw [if_neg (fun h=>different (798+93*k) (by unfold Cursor.stateCount;omega) (by omega) h.2.2)]
  rw [if_neg (fun h=>different (430+93*k) (by unfold Cursor.stateCount;omega) no430 h.2)]
  rw [if_neg (fun h=>different (613+93*k) (by unfold Cursor.stateCount;omega) no613 h.2.2)]
  have row:=baseRow k q b upper no430 no613
  change O.step s b=(tableControl k ((Cursor.machine k).step q b).1.val,((Cursor.machine k).step q b).2) at row
  rw [row]
  dsimp only
  have noBody : ¬∃ j : Fin 3,tableControl k ((Cursor.machine k).step q b).1.val=bodyControl k j := by
    rintro ⟨j,equal⟩
    have val:=congrArg Fin.val equal
    rw [tableValue k ((Cursor.machine k).step q b).1.val ((Cursor.machine k).step q b).1.isLt] at val
    have high:=bodyHigh k j
    omega
  rw [if_neg noBody]
  have noPaid (i : Nat) (small : i < 98) : s≠tableControl k i:=
    different i (by unfold Cursor.stateCount;omega) (by omega)
  rw [if_neg (fun h=>noPaid 43 (by decide) h.2),if_neg (fun h=>noPaid 47 (by decide) h.2),if_neg (fun h=>noPaid 51 (by decide) h.2)]
/-- Any finite metadata before q430: every literal row agrees with Cursor.
The live q430/cap boundaries themselves are excluded before they execute. -/
private theorem effective (k : Nat) (q : Fin (Cursor.machine k).stateCount) (m : Fin 144) (b : Option Bool)
    (no430 : q.val≠430+93*k) (lower : 98 ≤ q.val) (upper : q.val < 798+93*k)
    (no250 : q.val≠250) (no304 : q.val≠304) (no613 : q.val≠613+93*k)
    (afterLo : 98 ≤ ((Cursor.machine k).step q b).1.val)
    (afterHi : ((Cursor.machine k).step q b).1.val ≤ 798+93*k) :
    (machine k).step (control k (tableControl k q.val) m) b=
      (control k (tableControl k ((Cursor.machine k).step q b).1.val) m,((Cursor.machine k).step q b).2) := by
  have value:=tableValue k q.val q.isLt
  have nextValue:=tableValue k ((Cursor.machine k).step q b).1.val ((Cursor.machine k).step q b).1.isLt
  have terms:=oldTerminals k
  have na : tableControl k q.val≠(CertificateGuardClosure.machine k).accept := by
    intro equal
    have val:=congrArg Fin.val equal
    rw [value,terms.1] at val
    omega
  have nr : tableControl k q.val≠(CertificateGuardClosure.machine k).reject := by
    intro equal
    have val:=congrArg Fin.val equal
    rw [value,terms.2] at val
    omega
  rw [wire k (tableControl k q.val) m.val b m.isLt na nr,
    old_row k q m.val b no430 lower upper no250 no304 no613 afterHi]
  dsimp only
  rw [if_neg (by rw [nextValue,terms.1,terms.2];omega)]
  rfl
#print axioms old_row
#print axioms effective
end VirtualFinalClosure.FullEarlyRows
