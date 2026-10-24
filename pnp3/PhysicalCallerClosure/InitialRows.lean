import PhysicalCallerClosure.InitialNative
import PhysicalCallerClosure.ShiftSource
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
  for (owner,leaves) in [(`PhysicalCallerClosure.SourcePrepare,["CrossRows"]),
      (`PhysicalCallerClosure.InitialNative,["InitialRows","GammaStopRows"]),(`PhysicalCallerClosure.ShiftSource,["PlainSeekRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing exact initial type {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong initial owner"
      logInfo m!"initial-rows-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev initialMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {b : Bool} →
    {entry : Fin M.stateCount} → {gamma : Bool → Fin M.stateCount} →
    (eL eS restore readAnchor : Fin M.stateCount) → CrossRows (Safe:=Safe) .left entry eL →
    CrossRows (Safe:=Safe) .left eL eS → CrossRows (Safe:=Safe) .left eS restore → Safe restore → Safe readAnchor →
    M.step restore none=(readAnchor,some b,.left) → (∀ a,M.step readAnchor (some a)=(gamma a,none,.left)) →
    InitialRows (Safe:=Safe) b entry gamma := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.InitialNative 0) "PhysicalCallerClosure") "InitialRows") "mk"
    let some (.ctorInfo ci):=e.find? n | throwError "Missing exact initial constructor"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.InitialNative do throwError "Wrong initial constructor owner"
    logInfo m!"initial-rows-constructor|{n}|{ci.type}"
    closeMainGoal `initialMk (mkConst n (ci.levelParams.map Level.param))
section LiteralRows
set_option maxRecDepth 4000
private theorem cross_5 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 5) (ns k 3) := by
  refine ⟨ns k 6,ns_safe k 5 (by decide) (by decide),ns_safe k 6 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_3 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 3) (ns k 0) := by
  refine ⟨ns k 4,ns_safe k 3 (by decide) (by decide),ns_safe k 4 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_0 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 0) (ns k 2) := by
  refine ⟨ns k 1,ns_safe k 0 (by decide) (by decide),ns_safe k 1 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_0 (k : Nat) : InitialRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 5)
    (fun a=>if a then ns k 488 else ns k 9) := by
  refine initialMk (ns k 3) (ns k 0) (ns k 2) (ns k 8) (cross_5 k) (cross_3 k) (cross_0 k)
    (ns_safe k 2 (by decide) (by decide)) (ns_safe k 8 (by decide) (by decide)) ?_ ?_
  · run_tac nativeRow
  · intro a;cases a <;> run_tac nativeRow
private theorem cross_962 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 962) (ns k 960) := by
  refine ⟨ns k 963,ns_safe k 962 (by decide) (by decide),ns_safe k 963 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_960 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 960) (ns k 957) := by
  refine ⟨ns k 961,ns_safe k 960 (by decide) (by decide),ns_safe k 961 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_957 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 957) (ns k 959) := by
  refine ⟨ns k 958,ns_safe k 957 (by decide) (by decide),ns_safe k 958 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1 (k : Nat) : InitialRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 962)
    (fun a=>if a then ns k 488 else ns k 9) := by
  refine initialMk (ns k 960) (ns k 957) (ns k 959) (ns k 965) (cross_962 k) (cross_960 k) (cross_957 k)
    (ns_safe k 959 (by decide) (by decide)) (ns_safe k 965 (by decide) (by decide)) ?_ ?_
  · run_tac nativeRow
  · intro a;cases a <;> run_tac nativeRow
private theorem cross_971 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 971) (ns k 969) := by
  refine ⟨ns k 972,ns_safe k 971 (by decide) (by decide),ns_safe k 972 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_969 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 969) (ns k 966) := by
  refine ⟨ns k 970,ns_safe k 969 (by decide) (by decide),ns_safe k 970 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_966 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 966) (ns k 968) := by
  refine ⟨ns k 967,ns_safe k 966 (by decide) (by decide),ns_safe k 967 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem virtual_seek (k : Nat) : PlainSeekRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 971) (ns k 968) :=
  ⟨ns k 969,ns k 966,cross_971 k,cross_969 k,cross_966 k⟩
private theorem stop_9 (k : Nat) : GammaStopRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 9) (ns k 11) := by
  refine ⟨ns k 10,ns_safe k 9 (by decide) (by decide),ns_safe k 10 (by decide) (by decide),?_,?_⟩
  all_goals run_tac nativeRow
private theorem loop_9 (k : Nat) : ∀ b,(callerMachine k).step (ns k 9) (some b)=(ns k 9,some b,.left) := by
  intro b;cases b <;> run_tac nativeRow
private theorem stop_488 (k : Nat) : GammaStopRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 488) (ns k 490) := by
  refine ⟨ns k 489,ns_safe k 488 (by decide) (by decide),ns_safe k 489 (by decide) (by decide),?_,?_⟩
  all_goals run_tac nativeRow
private theorem loop_488 (k : Nat) : ∀ b,(callerMachine k).step (ns k 488) (some b)=(ns k 488,some b,.left) := by
  intro b;cases b <;> run_tac nativeRow
private theorem stop_968 (k : Nat) : GammaStopRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 968) (ns k 975) := by
  refine ⟨ns k 974,ns_safe k 968 (by decide) (by decide),ns_safe k 974 (by decide) (by decide),?_,?_⟩
  all_goals run_tac nativeRow
private theorem start_0 (k : Nat) : ∀ b,(callerMachine k).step (ns k 7) b=(ns k 5,b,.stay) := by
  intro b;cases b with
  | none => run_tac nativeRow
  | some b => cases b <;> run_tac nativeRow
private theorem start_1 (k : Nat) : ∀ b,(callerMachine k).step (ns k 964) b=(ns k 962,b,.stay) := by
  intro b;cases b with
  | none => run_tac nativeRow
  | some b => cases b <;> run_tac nativeRow
private theorem start_2 (k : Nat) : ∀ b,(callerMachine k).step (ns k 973) b=(ns k 971,b,.stay) := by
  intro b;cases b with
  | none => run_tac nativeRow
  | some b => cases b <;> run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
