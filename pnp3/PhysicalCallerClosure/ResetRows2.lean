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
private theorem clear_2_11 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 11 false (ns k 1208) (ns k 1078) := by
  refine ⟨ns k 1172,ns k 1173,ns k 1186,ns_safe k 1172 (by decide) (by decide),
    ns_safe k 1173 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_2_6 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 6 false (ns k 1236) (ns k 1208) := by
  refine ⟨ns k 1210,ns k 1211,ns k 1224,ns_safe k 1210 (by decide) (by decide),
    ns_safe k 1211 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_2_4 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 4 false (ns k 1256) (ns k 1236) := by
  refine ⟨ns k 1238,ns k 1239,ns k 1248,ns_safe k 1238 (by decide) (by decide),
    ns_safe k 1239 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem clear_2_5 (k : Nat) :
    ClearRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 false (ns k 1280) (ns k 1256) := by
  refine ⟨ns k 1258,ns k 1259,ns k 1270,ns_safe k 1258 (by decide) (by decide),
    ns_safe k 1259 (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem fromH_2 (k : Nat) :
    FromHRows (Safe:=NativeSafe k) (ns k 1282) (ns k 1280) := by
  refine ⟨ns k 1283,ns k 1284,ns_safe k 1282 (by decide) (by decide),
    ns_safe k 1283 (by decide) (by decide),ns_safe k 1284 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
end LiteralRows
private theorem code_all_2 (k : Nat) :
    ∃ s0 s1 s2 s3 : Fin (callerMachine k).stateCount,
      FromHRows (Safe:=NativeSafe k) (resetEntry k ⟨2,by decide⟩) s0 ∧
      ClearRows (Safe:=NativeSafe k) 5 false s0 s1 ∧
      ClearRows (Safe:=NativeSafe k) 4 false s1 s2 ∧
      ClearRows (Safe:=NativeSafe k) 6 false s2 s3 ∧
      ClearRows (Safe:=NativeSafe k) 11 false s3 (resetCopyEntry k ⟨2,by decide⟩) := by
  exact ⟨ns k 1280,ns k 1256,ns k 1236,ns k 1208,fromH_2 k,clear_2_5 k,clear_2_4 k,clear_2_6 k,clear_2_11 k⟩
end PhysicalCallerClosure
