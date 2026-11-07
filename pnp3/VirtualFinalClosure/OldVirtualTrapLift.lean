import VirtualFinalClosure.OldVirtualTrap
import VirtualFinalClosure.Prefix
import VirtualFinalClosure.LeafNativeRows
namespace VirtualFinalClosure.OldVirtualTrapLift
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.OldVirtualTrap","VirtualFinalClosure.OldVirtualTrap","Region","Region",(0:Nat)),
      ("VirtualFinalClosure.OldVirtualTrap","VirtualFinalClosure.OldVirtualTrap","row_closed","canonicalClosed",1),
      ("VirtualFinalClosure.OldVirtualTrap","VirtualFinalClosure.OldVirtualTrap","cursorRegion","cursorRegion",0),
      ("VirtualFinalClosure.CleanupState","VirtualFinalClosure.CleanupState","region","cleanRegion",0),
      ("VirtualFinalClosure.CleanupRows","VirtualFinalClosure.CleanupRows","canonical","canonicalRow",1),
      ("VirtualFinalClosure.CleanupRows","VirtualFinalClosure.CleanupRows","base_row","cursorRow",1),
      ("VirtualFinalClosure.CleanupState","VirtualFinalClosure.CleanupState","q_value","qValue",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p1","p1",0),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","p1_value","p1Value",1),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","full_state","fullState",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full","full",0),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","component","component",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full_value","fullValue",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","body_above","bodyAbove",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","result_pin","resultPin",1),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual normal-prefix/cap-trap term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual normal-prefix/cap-trap {mod}/{key}"
private theorem cursor_pin (k : Nat) (q : Fin (Cursor.machine k).stateCount) :
    full k (p1 k q)=tableControl k q.val:=fullState k q
private theorem no_hooks (k : Nat) (q : Fin (Cursor.machine k).stateCount) (inside : cursorRegion k q) :
    q.val≠430+93*k ∧ q.val≠613+93*k:=by
  rcases inside with (gate|middle|ready|reject)|odd|even
  all_goals try omega
  have eq:=congrArg Fin.val reject
  change q.val=40 at eq
  omega
private theorem projected (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (b : Option Bool)
    (inside : Region k s) :
    ((CertificateGuardClosure.machine k).step (full k s) b).1=
      full k (((CanonicalLeaf.machine k).step s b).1):=by
  rcases inside with ⟨q,allowed,eq⟩|extras
  · rw [eq]
    by_cases ready : q.val=936+93*k
    · exact congrArg Prod.fst (component k (p1 k q) b (by rw [p1Value,ready];omega))
    · have hooks:=no_hooks k q allowed
      rw [canonicalRow k q b ready,cursor_pin,cursor_pin,cursorRow k q b ready hooks.1 hooks.2]
  · rcases extras with high|reject
    · exact congrArg Prod.fst (component k s b (by
        change 288+Cursor.stateCount k ≤ s.val at high
        unfold Cursor.stateCount at high
        omega))
    · have rejectPin : full k (CanonicalLeaf.machine k).reject=(CertificateGuardClosure.machine k).reject:=rfl
      change s=(CanonicalLeaf.machine k).reject at reject
      rw [reject,rejectPin,UniformTM.step_reject,UniformTM.step_reject]
      exact rejectPin.symm
private def OldRegion (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) : Prop:=
  ∃ q,Region k q ∧ s=full k q
private def OldRegion_type : ∀ k,Fin (CertificateGuardClosure.machine k).stateCount → Prop:=OldRegion
private theorem row_closed (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) (b : Option Bool)
    (inside : OldRegion k s) : OldRegion k (((CertificateGuardClosure.machine k).step s b).1):=by
  obtain ⟨q,allowed,eq⟩:=inside
  rw [eq]
  exact ⟨_,canonicalClosed k q b allowed,projected k q b allowed⟩
private theorem run_closed (k : Nat) {N B : Nat} (c : Config (CertificateGuardClosure.machine k).stateCount N B)
    (inside : OldRegion k c.state) (t : Nat) : OldRegion k (((CertificateGuardClosure.machine k).run t c).state):=by
  induction t with
  | zero=>exact inside
  | succ t ih=>exact row_closed k _ _ ih
private theorem no_body (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) (mode : Fin 3)
    (inside : OldRegion k s) : s≠bodyControl k mode:=by
  obtain ⟨q,_allowed,eq⟩:=inside
  intro hit
  have values:=congrArg Fin.val (eq.symm.trans hit)
  rw [fullValue] at values
  have upper:=q.isLt
  have lower:=bodyAbove k mode
  omega
private theorem intercept_inside (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) (b : Option Bool)
    (event : Intercept k s b) : OldRegion k s:=by
  have leafMember (value : Bool) : OldRegion k (leafControl k value):=by
    refine ⟨CanonicalLeaf.result k value,Or.inr (Or.inl ?_),?_⟩
    · change 288+Cursor.stateCount k ≤ 288+Cursor.stateCount k+(if value then 7 else 6)
      cases value <;> omega
    · exact (resultPin k value).symm
  have capMember (i : Nat) (valid : i=250 ∨ i=304 ∨ i=798+93*k) : OldRegion k (tableControl k i):=by
    have fit : i < Cursor.stateCount k:=by rcases valid with rfl|rfl|rfl <;> unfold Cursor.stateCount <;> omega
    refine ⟨p1 k (Cursor.q k i),Or.inl ⟨_,?_,rfl⟩,?_⟩
    · dsimp only [cursorRegion,cleanRegion]
      rw [qValue k i fit]
      rcases valid with rfl|rfl|rfl <;> omega
    · simpa only [qValue k i fit] using (cursor_pin k (Cursor.q k i)).symm
  rcases event with (left|right)|⟨_blank,left|right|last⟩
  · rw [left];exact leafMember false
  · rw [right];exact leafMember true
  · rw [left];exact capMember 250 (Or.inl rfl)
  · rw [right];exact capMember 304 (Or.inr (Or.inl rfl))
  · rw [last];exact capMember (798+93*k) (Or.inr (Or.inr rfl))
/-- A real old NORMAL BODY arrival excludes every earlier arithmetic-cap or
leaf intercept by actual row closure, independent of head/tape contents. -/
private theorem before_body (k : Nat) {N B : Nat} (c : Config (CertificateGuardClosure.machine k).stateCount N B)
    (T : Nat) (mode : Fin 3) (arrived : ((CertificateGuardClosure.machine k).run T c).state=bodyControl k mode) :
    ∀ u,u ≤ T → ¬Intercept k (((CertificateGuardClosure.machine k).run u c).state)
      (((CertificateGuardClosure.machine k).run u c).tape ((CertificateGuardClosure.machine k).run u c).head):=by
  intro u hu event
  have trapped:=run_closed k ((CertificateGuardClosure.machine k).run u c) (intercept_inside k _ _ event) (T-u)
  have same:=UniformTM.run_add (CertificateGuardClosure.machine k) u (T-u) c
  rw [Nat.add_sub_of_le hu] at same
  have closed : OldRegion k (((CertificateGuardClosure.machine k).run T c).state):=by
    rw [same];exact trapped
  exact no_body k _ mode closed arrived
#print axioms cursor_pin
#print axioms no_hooks
#print axioms projected
#print axioms OldRegion_type
#print axioms row_closed
#print axioms run_closed
#print axioms no_body
#print axioms intercept_inside
#print axioms before_body
end VirtualFinalClosure.OldVirtualTrapLift
