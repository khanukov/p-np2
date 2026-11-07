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
private theorem clear_0_11 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 11 false (ns k 262) (ns k 132) := by
  refine ⟨ns k 226,ns k 227,ns k 240,ns_safe k 226 (by decide) (by decide),
    ns_safe k 227 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_0_6 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 6 false (ns k 290) (ns k 262) := by
  refine ⟨ns k 264,ns k 265,ns k 278,ns_safe k 264 (by decide) (by decide),
    ns_safe k 265 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_0_4 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 4 false (ns k 310) (ns k 290) := by
  refine ⟨ns k 292,ns k 293,ns k 302,ns_safe k 292 (by decide) (by decide),
    ns_safe k 293 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_0_5 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 false (ns k 334) (ns k 310) := by
  refine ⟨ns k 312,ns k 313,ns k 324,ns_safe k 312 (by decide) (by decide),
    ns_safe k 313 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem fromH_0 (k : Nat) :
    FromHRows (Safe:=NativeSafe k) (ns k 336) (ns k 334) := by
  refine ⟨ns k 337,ns k 338,ns_safe k 336 (by decide) (by decide),
    ns_safe k 337 (by decide) (by decide),ns_safe k 338 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
end LiteralRows
private theorem code_all_0 (k : Nat) :
    ∃ s0 s1 s2 s3 : Fin (callerMachine k).stateCount,
      FromHRows (Safe:=NativeSafe k) (resetEntry k ⟨0,by decide⟩) s0 ∧
      ClearRows (Safe:=NativeSafe k) 5 false s0 s1 ∧
      ClearRows (Safe:=NativeSafe k) 4 false s1 s2 ∧
      ClearRows (Safe:=NativeSafe k) 6 false s2 s3 ∧
      ClearRows (Safe:=NativeSafe k) 11 false s3 (resetCopyEntry k ⟨0,by decide⟩) := by
  exact ⟨ns k 334,ns k 310,ns k 290,ns k 262,fromH_0 k,clear_0_5 k,clear_0_4 k,clear_0_6 k,clear_0_11 k⟩
end PhysicalCallerClosure
