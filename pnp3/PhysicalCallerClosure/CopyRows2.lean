import PhysicalCallerClosure.CopyKernel
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
  for leaf in ["ns","NativeSafe","DecRows","IncRows","nativeRoute","nativeRow","ns_safe"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing Engine support owner"
    unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong support owner"
    logInfo m!"literal-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev pin_ns : ∀ k,Nat → Fin (callerMachine k).stateCount := by run_tac checkedEngine "ns" "definition"
private abbrev pin_NativeSafe : ∀ k,Fin (callerMachine k).stateCount → Prop := by run_tac checkedEngine "NativeSafe" "definition"
private abbrev pin_DecRows : {M : UniformTM} → {_Safe : Fin M.stateCount → Prop} →
    Nat → Fin M.stateCount → Fin M.stateCount → Fin M.stateCount → Prop := by run_tac checkedEngine "DecRows" "definition"
private abbrev pin_IncRows : {M : UniformTM} → {_Safe : Fin M.stateCount → Prop} →
    Nat → Fin M.stateCount → Fin M.stateCount → Prop := by run_tac checkedEngine "IncRows" "definition"
private abbrev pin_nativeRoute : Nat → TacticM Unit := by run_tac checkedEngine "nativeRoute" "definition"
private abbrev pin_nativeRow : TacticM Unit := by run_tac checkedEngine "nativeRow" "definition"
private theorem pin_ns_safe : ∀ k i,i<3337 → i≠1432 → NativeSafe k (ns k i) := by
  run_tac checkedEngine "ns_safe" "theorem"
run_cmd do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.CopyKernel 0) "PhysicalCallerClosure") "CopyRows"
  let some ci:=e.find? n | throwError "Missing exact CopyRows"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.CopyKernel do throwError "Wrong owner"
  logInfo m!"copy-rows-type|{n}|{ci.type}"
  modifyScope fun st=>{st with openDecls:=.explicit `CopyRows n::st.openDecls}
private abbrev copyMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {s d : Nat} →
    {start out : Fin M.stateCount} → (rd restore rr id it ir : Fin M.stateCount) →
    Safe start → Safe restore → M.step start none=(rd,none,.stay) →
    DecRows (Safe:=Safe) s rd restore id → IncRows (Safe:=Safe) d id it → IncRows (Safe:=Safe) 5 it start →
    M.step restore none=(rr,none,.stay) → DecRows (Safe:=Safe) 5 rr out ir →
    IncRows (Safe:=Safe) s ir restore → CopyRows (Safe:=Safe) s d start out := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.CopyKernel 0) "PhysicalCallerClosure") "CopyRows"
    let n:=Name.str n "mk"
    let some (.ctorInfo ci):=e.find? n | throwError "Missing exact CopyRows constructor"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.CopyKernel do throwError "Wrong constructor owner"
    logInfo m!"copy-rows-constructor|{n}|{ci.type}"
    closeMainGoal `copyMk (mkConst n (ci.levelParams.map Level.param))
section LiteralRows
set_option maxRecDepth 4000
private theorem dec_1137 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 (ns k 1137) (ns k 1121) (ns k 1114) := by
  refine ⟨ns k 1116,ns k 1117,ns k 1118,ns k 1126,ns k 1124,ns k 1131,
    ns_safe k 1116 (by decide) (by decide),ns_safe k 1117 (by decide) (by decide),
    ns_safe k 1118 (by decide) (by decide),ns_safe k 1126 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb; cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_1114 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 4 (ns k 1114) (ns k 1095) := by
  refine ⟨ns k 1097,ns k 1098,ns k 1099,ns k 1106,ns_safe k 1097 (by decide) (by decide),
    ns_safe k 1098 (by decide) (by decide),ns_safe k 1099 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_1095 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 1095) (ns k 1078) := by
  refine ⟨ns k 1073,ns k 1074,ns k 1075,ns k 1085,ns_safe k 1073 (by decide) (by decide),
    ns_safe k 1074 (by decide) (by decide),ns_safe k 1075 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem dec_1170 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 1170) (ns k 985) (ns k 1146) := by
  refine ⟨ns k 1148,ns k 1149,ns k 1150,ns k 1151,ns k 992,ns k 1160,
    ns_safe k 1148 (by decide) (by decide),ns_safe k 1149 (by decide) (by decide),
    ns_safe k 1150 (by decide) (by decide),ns_safe k 1151 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb; cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_1146 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 (ns k 1146) (ns k 1121) := by
  refine ⟨ns k 1139,ns k 1140,ns k 1141,ns k 1124,ns_safe k 1139 (by decide) (by decide),
    ns_safe k 1140 (by decide) (by decide),ns_safe k 1141 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def copy_3_4_2 (k : Nat) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 4 (ns k 1078) (ns k 985) := by
  refine copyMk (ns k 1137) (ns k 1121) (ns k 1170) (ns k 1114) (ns k 1095) (ns k 1146)
    (ns_safe k 1078 (by decide) (by decide)) (ns_safe k 1121 (by decide) (by decide)) ?_
    (dec_1137 k) (inc_1114 k) (inc_1095 k) ?_ (dec_1170 k) (inc_1146 k)
  all_goals run_tac nativeRow
private theorem dec_1031 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 (ns k 1031) (ns k 1034) (ns k 1029) := by
  refine ⟨ns k 1031,ns k 1032,ns k 1033,ns k 1035,ns k 1034,ns k 1029,
    ns_safe k 1031 (by decide) (by decide),ns_safe k 1032 (by decide) (by decide),
    ns_safe k 1033 (by decide) (by decide),ns_safe k 1035 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb; cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_1029 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 6 (ns k 1029) (ns k 1002) := by
  refine ⟨ns k 1004,ns k 1005,ns k 1006,ns k 1017,ns_safe k 1004 (by decide) (by decide),
    ns_safe k 1005 (by decide) (by decide),ns_safe k 1006 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_1002 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 1002) (ns k 985) := by
  refine ⟨ns k 980,ns k 981,ns k 982,ns k 992,ns_safe k 980 (by decide) (by decide),
    ns_safe k 981 (by decide) (by decide),ns_safe k 982 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem dec_1071 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 1071) (ns k 976) (ns k 1036) := by
  refine ⟨ns k 1039,ns k 1040,ns k 1041,ns k 1052,ns k 1050,ns k 1061,
    ns_safe k 1039 (by decide) (by decide),ns_safe k 1040 (by decide) (by decide),
    ns_safe k 1041 (by decide) (by decide),ns_safe k 1052 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb; cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_1036 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 (ns k 1036) (ns k 1034) := by
  refine ⟨ns k 1036,ns k 1037,ns k 1038,ns k 1034,ns_safe k 1036 (by decide) (by decide),
    ns_safe k 1037 (by decide) (by decide),ns_safe k 1038 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def copy_0_6_2 (k : Nat) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 6 (ns k 985) (ns k 976) := by
  refine copyMk (ns k 1031) (ns k 1034) (ns k 1071) (ns k 1029) (ns k 1002) (ns k 1036)
    (ns_safe k 985 (by decide) (by decide)) (ns_safe k 1034 (by decide) (by decide)) ?_
    (dec_1031 k) (inc_1029 k) (inc_1002 k) ?_ (dec_1071 k) (inc_1036 k)
  all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
