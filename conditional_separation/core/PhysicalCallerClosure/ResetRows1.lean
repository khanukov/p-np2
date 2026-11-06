import PhysicalCallerClosure.Engine
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def checkedEngine (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure") leaf
  let some ci:=e.find? n | throwError "Missing exact Engine constant {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | _=>"other"
  unless actual==kind do throwError "Wrong Engine kind {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing Engine owner"
  unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong Engine owner"
  logInfo m!"literal-support|{actual}|{n}|{ci.type}"
  closeMainGoal `checkedEngine (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["ns","NativeSafe","ClearRows","FromHRows","nativeRoute","nativeRow","ns_safe"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing Engine support owner"
    unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong support owner"
    logInfo m!"literal-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev pin_ns : ∀ k,Nat → Fin (callerMachine k).stateCount := by run_tac checkedEngine "ns" "definition"
private abbrev pin_NativeSafe : ∀ k,Fin (callerMachine k).stateCount → Prop := by run_tac checkedEngine "NativeSafe" "definition"
private abbrev pin_ClearRows : {M : UniformTM} → {_Safe : Fin M.stateCount → Prop} →
    Nat → Bool → Fin M.stateCount → Fin M.stateCount → Prop := by run_tac checkedEngine "ClearRows" "definition"
private abbrev pin_FromHRows : {M : UniformTM} → {_Safe : Fin M.stateCount → Prop} →
    Fin M.stateCount → Fin M.stateCount → Prop := by run_tac checkedEngine "FromHRows" "definition"
private abbrev pin_nativeRoute : Nat → TacticM Unit := by run_tac checkedEngine "nativeRoute" "definition"
private abbrev pin_nativeRow : TacticM Unit := by run_tac checkedEngine "nativeRow" "definition"
private theorem pin_ns_safe : ∀ k i,i<3337 → i≠1432 → NativeSafe k (ns k i) := by
  run_tac checkedEngine "ns_safe" "theorem"
section LiteralRows
set_option maxRecDepth 4000
private theorem clear_1_11 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 11 false (ns k 731) (ns k 601) := by
  refine ⟨ns k 695,ns k 696,ns k 709,ns_safe k 695 (by decide) (by decide),
    ns_safe k 696 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_1_6 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 6 false (ns k 759) (ns k 731) := by
  refine ⟨ns k 733,ns k 734,ns k 747,ns_safe k 733 (by decide) (by decide),
    ns_safe k 734 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_1_4 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 4 false (ns k 779) (ns k 759) := by
  refine ⟨ns k 761,ns k 762,ns k 771,ns_safe k 761 (by decide) (by decide),
    ns_safe k 762 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_1_5 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 false (ns k 803) (ns k 779) := by
  refine ⟨ns k 781,ns k 782,ns k 793,ns_safe k 781 (by decide) (by decide),
    ns_safe k 782 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem fromH_1 (k : Nat) :
    FromHRows (Safe:=NativeSafe k) (ns k 805) (ns k 803) := by
  refine ⟨ns k 806,ns k 807,ns_safe k 805 (by decide) (by decide),
    ns_safe k 806 (by decide) (by decide),ns_safe k 807 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
end LiteralRows
private theorem code_all_1 (k : Nat) :
    ∃ s0 s1 s2 s3 : Fin (callerMachine k).stateCount,
      FromHRows (Safe:=NativeSafe k) (resetEntry k ⟨1,by decide⟩) s0 ∧
      ClearRows (Safe:=NativeSafe k) 5 false s0 s1 ∧
      ClearRows (Safe:=NativeSafe k) 4 false s1 s2 ∧
      ClearRows (Safe:=NativeSafe k) 6 false s2 s3 ∧
      ClearRows (Safe:=NativeSafe k) 11 false s3 (resetCopyEntry k ⟨1,by decide⟩) := by
  exact ⟨ns k 803,ns k 779,ns k 759,ns k 731,fromH_1 k,clear_1_5 k,clear_1_4 k,clear_1_6 k,clear_1_11 k⟩
end PhysicalCallerClosure
