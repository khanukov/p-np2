import PhysicalCallerClosure.SourcePrepare
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
  for leaf in ["ns","NativeSafe","nativeRoute","nativeRow","ns_safe"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing Engine support owner"
    unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong support owner"
    logInfo m!"literal-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev pin_ns : ∀ k,Nat → Fin (callerMachine k).stateCount := by run_tac checkedEngine "ns" "definition"
private abbrev pin_NativeSafe : ∀ k,Fin (callerMachine k).stateCount → Prop := by run_tac checkedEngine "NativeSafe" "definition"
private abbrev pin_nativeRoute : Nat → TacticM Unit := by run_tac checkedEngine "nativeRoute" "definition"
private abbrev pin_nativeRow : TacticM Unit := by run_tac checkedEngine "nativeRow" "definition"
private theorem pin_ns_safe : ∀ k i,i<3337 → i≠1432 → NativeSafe k (ns k i) := by
  run_tac checkedEngine "ns_safe" "theorem"
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Navigation,["ToHRows"]),
      (`PhysicalCallerClosure.SourcePrepare,["CrossRows","PrepareRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing navigation support {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"navigation-rows-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
section LiteralRows
set_option maxRecDepth 4000
private theorem cross_28 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 28) (ns k 26) := by
  refine ⟨ns k 29,ns_safe k 28 (by decide) (by decide),ns_safe k 29 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_26 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 26) (ns k 24) := by
  refine ⟨ns k 27,ns_safe k 26 (by decide) (by decide),ns_safe k 27 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_24 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 24) (ns k 12) := by
  refine ⟨ns k 25,ns_safe k 24 (by decide) (by decide),ns_safe k 25 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_497 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 497) (ns k 495) := by
  refine ⟨ns k 498,ns_safe k 497 (by decide) (by decide),ns_safe k 498 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_495 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 495) (ns k 493) := by
  refine ⟨ns k 496,ns_safe k 495 (by decide) (by decide),ns_safe k 496 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_493 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 493) (ns k 491) := by
  refine ⟨ns k 494,ns_safe k 493 (by decide) (by decide),ns_safe k 494 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_17 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 17) (ns k 15) := by
  refine ⟨ns k 18,ns_safe k 17 (by decide) (by decide),ns_safe k 18 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_15 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 15) (evalState k (SerializedBody.entry ⟨0,by decide⟩)) := by
  refine ⟨ns k 16,ns_safe k 15 (by decide) (by decide),ns_safe k 16 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_22 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 22) (ns k 20) := by
  refine ⟨ns k 23,ns_safe k 22 (by decide) (by decide),ns_safe k 23 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_20 (k : Nat) :
    CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 20) (evalState k (SerializedBody.entry ⟨1,by decide⟩)) := by
  refine ⟨ns k 21,ns_safe k 20 (by decide) (by decide),ns_safe k 21 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem home_0 (k : Nat) :
    ToHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 30) (ns k 28) := by
  refine ⟨ns k 31,ns k 32,ns k 33,ns_safe k 30 (by decide) (by decide),ns_safe k 31 (by decide) (by decide),ns_safe k 32 (by decide) (by decide),ns_safe k 33 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
private theorem home_1 (k : Nat) :
    ToHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 499) (ns k 497) := by
  refine ⟨ns k 500,ns k 501,ns k 502,ns_safe k 499 (by decide) (by decide),ns_safe k 500 (by decide) (by decide),ns_safe k 501 (by decide) (by decide),ns_safe k 502 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
private theorem home_2 (k : Nat) :
    ToHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 976) (evalState k (SerializedBody.entry ⟨2,by decide⟩)) := by
  refine ⟨ns k 977,ns k 978,ns k 979,ns_safe k 976 (by decide) (by decide),ns_safe k 977 (by decide) (by decide),ns_safe k 978 (by decide) (by decide),ns_safe k 979 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
private theorem prepare_0_false (k : Nat) :
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 28) (evalState k (SerializedBody.entry ⟨0,by decide⟩)) := by
  refine ⟨ns k 26,ns k 24,ns k 12,ns k 13,ns k 14,ns k 17,ns k 15,
    cross_28 k,cross_26 k,cross_24 k,ns_safe k 12 (by decide) (by decide),ns_safe k 13 (by decide) (by decide),ns_safe k 14 (by decide) (by decide),?_,?_,?_,?_,cross_17 k,cross_15 k⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem prepare_0_true (k : Nat) :
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 28) (evalState k (SerializedBody.entry ⟨1,by decide⟩)) := by
  refine ⟨ns k 26,ns k 24,ns k 12,ns k 13,ns k 19,ns k 22,ns k 20,
    cross_28 k,cross_26 k,cross_24 k,ns_safe k 12 (by decide) (by decide),ns_safe k 13 (by decide) (by decide),ns_safe k 19 (by decide) (by decide),?_,?_,?_,?_,cross_22 k,cross_20 k⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem prepare_1_false (k : Nat) :
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 497) (evalState k (SerializedBody.entry ⟨0,by decide⟩)) := by
  refine ⟨ns k 495,ns k 493,ns k 491,ns k 492,ns k 14,ns k 17,ns k 15,
    cross_497 k,cross_495 k,cross_493 k,ns_safe k 491 (by decide) (by decide),ns_safe k 492 (by decide) (by decide),ns_safe k 14 (by decide) (by decide),?_,?_,?_,?_,cross_17 k,cross_15 k⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem prepare_1_true (k : Nat) :
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 497) (evalState k (SerializedBody.entry ⟨1,by decide⟩)) := by
  refine ⟨ns k 495,ns k 493,ns k 491,ns k 492,ns k 19,ns k 22,ns k 20,
    cross_497 k,cross_495 k,cross_493 k,ns_safe k 491 (by decide) (by decide),ns_safe k 492 (by decide) (by decide),ns_safe k 19 (by decide) (by decide),?_,?_,?_,?_,cross_22 k,cross_20 k⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
