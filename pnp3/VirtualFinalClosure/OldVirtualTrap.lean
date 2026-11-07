import VirtualFinalClosure.CleanupState
import VirtualFinalClosure.LeafComponent
import VirtualFinalClosure.BaseCursorRows
import CanonicalLeaf.Rows
namespace VirtualFinalClosure.OldVirtualTrap
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.CleanupState","VirtualFinalClosure.CleanupState","region","cleanRegion",(0:Nat)),
      ("VirtualFinalClosure.CleanupState","VirtualFinalClosure.CleanupState","row_closed","cleanClosed",1),
      ("VirtualFinalClosure.CleanupState","VirtualFinalClosure.CleanupState","q_value","qValue",1),
      ("VirtualReady.Kernel","VirtualReady","route_rows","routeRows",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p0","p0",0),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p1","p1",0),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p0_value","p0Value",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p1_value","p1Value",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full","full",0),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","component","fullRow",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full_value","fullValue",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","body_above","bodyAbove",1),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entryValue",1),
      ("CanonicalLeaf.Rows","CanonicalLeaf","region","extraRegion",0),
      ("CanonicalLeaf.Rows","CanonicalLeaf","region_step","extraClosed",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual old virtual-trap term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual old virtual-trap term {mod}/{key}"
private def cursorRegion (k : Nat) (q : Fin (Cursor.machine k).stateCount) : Prop:=
  cleanRegion k q ∨ (250 ≤ q.val ∧ q.val < 254) ∨ (304 ≤ q.val ∧ q.val < 308)
private def cursorRegion_type : ∀ k,Fin (Cursor.machine k).stateCount → Prop:=cursorRegion
private theorem route_closed (k : Nat) (odd : Bool) (j : Fin 4) (b : Option Bool) :
    cursorRegion k (((Cursor.machine k).step (Cursor.q k ((if odd then 250 else 304)+j.val)) b).1):=by
  cases odd <;> fin_cases j <;> cases b with
  | none =>
    have rF:=routeRows k false none false
    have rT:=routeRows k true none false
    simp only [Bool.false_eq_true,↓reduceIte,Nat.reduceAdd] at rF rT ⊢
    first
    | rw [rF.1]
    | rw [rF.2.2.1]
    | rw [rF.2.2.2.1]
    | rw [rF.2.2.2.2.2]
    | rw [rT.1]
    | rw [rT.2.2.1]
    | rw [rT.2.2.2.1]
    | rw [rT.2.2.2.2.2]
    all_goals
      dsimp only [cursorRegion,cleanRegion]
      rw [qValue k _ (by unfold Cursor.stateCount;omega)]
      omega
  | some v =>
    have rF:=routeRows k false (some v) v
    have rT:=routeRows k true (some v) v
    simp only [Bool.false_eq_true,↓reduceIte,Nat.reduceAdd] at rF rT ⊢
    first
    | rw [rF.1]
    | rw [rF.2.1]
    | rw [rF.2.2.2.1]
    | rw [rF.2.2.2.2.1]
    | rw [rT.1]
    | rw [rT.2.1]
    | rw [rT.2.2.2.1]
    | rw [rT.2.2.2.2.1]
    all_goals
      dsimp only [cursorRegion,cleanRegion]
      rw [qValue k _ (by unfold Cursor.stateCount;omega)]
      omega
private theorem cursor_closed (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (inside : cursorRegion k q) : cursorRegion k (((Cursor.machine k).step q b).1):=by
  rcases inside with clean|odd|even
  · exact Or.inl (cleanClosed k q b clean)
  · let j : Fin 4:=⟨q.val-250,by omega⟩
    have eq : q=Cursor.q k (250+j.val):=Fin.ext (by rw [qValue k _ (by unfold Cursor.stateCount;have bound:=j.isLt;omega)];dsimp only [j];omega)
    rw [eq];exact route_closed k true j b
  · let j : Fin 4:=⟨q.val-304,by omega⟩
    have eq : q=Cursor.q k (304+j.val):=Fin.ext (by rw [qValue k _ (by unfold Cursor.stateCount;have bound:=j.isLt;omega)];dsimp only [j];omega)
    rw [eq];exact route_closed k false j b
private def Region (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) : Prop:=
  (∃ q,cursorRegion k q ∧ s=p1 k q) ∨ extraRegion k s
private def Region_type : ∀ k,Fin (CanonicalLeaf.machine k).stateCount → Prop:=Region
private theorem extra_closed (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (b : Option Bool)
    (inside : extraRegion k s) : extraRegion k (((CanonicalLeaf.machine k).step s b).1):=by
  rw [CanonicalLeaf.table_delta]
  cases b with
  | none=>exact extraClosed k s none inside
  | some v=>
    by_cases special : s=VirtualLeaf.extra k ⟨2,by decide⟩
    · cases v <;> dsimp only <;> rw [if_pos special]
      all_goals
        left
        dsimp only [VirtualLeaf.extra]
        omega
    · cases v <;> dsimp only <;> rw [if_neg special]
      all_goals exact extraClosed k s _ inside
private theorem row_closed (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (b : Option Bool)
    (inside : Region k s) : Region k (((CanonicalLeaf.machine k).step s b).1):=by
  rcases inside with ⟨q,allowed,eq⟩|extras
  · rw [eq]
    dsimp only [p1]
    rw [CanonicalLeaf.repaired_rows]
    split_ifs with entry
    · right;left
      dsimp only [VirtualLeaf.extra]
      omega
    · have native : (IngressRepair.machine k).step (p0 k q) b=
          (p0 k ((Cursor.machine k).step q b).1,((Cursor.machine k).step q b).2):=by
        dsimp only [IngressRepair.machine,p0]
        rw [UniformTM.seq_step_right]
      rw [native]
      exact Or.inl ⟨_,cursor_closed k q b allowed,rfl⟩
  · exact Or.inr (extra_closed k s b extras)
#print axioms cursorRegion_type
#print axioms route_closed
#print axioms cursor_closed
#print axioms Region_type
#print axioms extra_closed
#print axioms row_closed
end VirtualFinalClosure.OldVirtualTrap
