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
private theorem dec_191 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 (ns k 191) (ns k 175) (ns k 168) := by
  refine ⟨ns k 170,ns k 171,ns k 172,ns k 180,ns k 178,ns k 185,
    ns_safe k 170 (by decide) (by decide),ns_safe k 171 (by decide) (by decide),
    ns_safe k 172 (by decide) (by decide),ns_safe k 180 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_168 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 4 (ns k 168) (ns k 149) := by
  refine ⟨ns k 151,ns k 152,ns k 153,ns k 160,ns_safe k 151 (by decide) (by decide),
    ns_safe k 152 (by decide) (by decide),ns_safe k 153 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_149 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 149) (ns k 132) := by
  refine ⟨ns k 127,ns k 128,ns k 129,ns k 139,ns_safe k 127 (by decide) (by decide),
    ns_safe k 128 (by decide) (by decide),ns_safe k 129 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem dec_224 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 224) (ns k 39) (ns k 200) := by
  refine ⟨ns k 202,ns k 203,ns k 204,ns k 205,ns k 46,ns k 214,
    ns_safe k 202 (by decide) (by decide),ns_safe k 203 (by decide) (by decide),
    ns_safe k 204 (by decide) (by decide),ns_safe k 205 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_200 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 (ns k 200) (ns k 175) := by
  refine ⟨ns k 193,ns k 194,ns k 195,ns k 178,ns_safe k 193 (by decide) (by decide),
    ns_safe k 194 (by decide) (by decide),ns_safe k 195 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def copy_3_4_0 (k : Nat) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 4 (ns k 132) (ns k 39) := by
  refine copyMk (ns k 191) (ns k 175) (ns k 224) (ns k 168) (ns k 149) (ns k 200)
    (ns_safe k 132 (by decide) (by decide)) (ns_safe k 175 (by decide) (by decide)) ?_
    (dec_191 k) (inc_168 k) (inc_149 k) ?_ (dec_224 k) (inc_200 k)
  all_goals run_tac nativeRow
private theorem dec_85 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 (ns k 85) (ns k 88) (ns k 83) := by
  refine ⟨ns k 85,ns k 86,ns k 87,ns k 89,ns k 88,ns k 83,
    ns_safe k 85 (by decide) (by decide),ns_safe k 86 (by decide) (by decide),
    ns_safe k 87 (by decide) (by decide),ns_safe k 89 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_83 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 6 (ns k 83) (ns k 56) := by
  refine ⟨ns k 58,ns k 59,ns k 60,ns k 71,ns_safe k 58 (by decide) (by decide),
    ns_safe k 59 (by decide) (by decide),ns_safe k 60 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_56 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 56) (ns k 39) := by
  refine ⟨ns k 34,ns k 35,ns k 36,ns k 46,ns_safe k 34 (by decide) (by decide),
    ns_safe k 35 (by decide) (by decide),ns_safe k 36 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem dec_125 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 125) (ns k 30) (ns k 90) := by
  refine ⟨ns k 93,ns k 94,ns k 95,ns k 106,ns k 104,ns k 115,
    ns_safe k 93 (by decide) (by decide),ns_safe k 94 (by decide) (by decide),
    ns_safe k 95 (by decide) (by decide),ns_safe k 106 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_90 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 (ns k 90) (ns k 88) := by
  refine ⟨ns k 90,ns k 91,ns k 92,ns k 88,ns_safe k 90 (by decide) (by decide),
    ns_safe k 91 (by decide) (by decide),ns_safe k 92 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def copy_0_6_0 (k : Nat) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 6 (ns k 39) (ns k 30) := by
  refine copyMk (ns k 85) (ns k 88) (ns k 125) (ns k 83) (ns k 56) (ns k 90)
    (ns_safe k 39 (by decide) (by decide)) (ns_safe k 88 (by decide) (by decide)) ?_
    (dec_85 k) (inc_83 k) (inc_56 k) ?_ (dec_125 k) (inc_90 k)
  all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
