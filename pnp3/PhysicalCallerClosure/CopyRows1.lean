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
private theorem dec_660 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 (ns k 660) (ns k 644) (ns k 637) := by
  refine ⟨ns k 639,ns k 640,ns k 641,ns k 649,ns k 647,ns k 654,
    ns_safe k 639 (by decide) (by decide),ns_safe k 640 (by decide) (by decide),
    ns_safe k 641 (by decide) (by decide),ns_safe k 649 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_637 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 4 (ns k 637) (ns k 618) := by
  refine ⟨ns k 620,ns k 621,ns k 622,ns k 629,ns_safe k 620 (by decide) (by decide),
    ns_safe k 621 (by decide) (by decide),ns_safe k 622 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_618 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 618) (ns k 601) := by
  refine ⟨ns k 596,ns k 597,ns k 598,ns k 608,ns_safe k 596 (by decide) (by decide),
    ns_safe k 597 (by decide) (by decide),ns_safe k 598 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem dec_693 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 693) (ns k 508) (ns k 669) := by
  refine ⟨ns k 671,ns k 672,ns k 673,ns k 674,ns k 515,ns k 683,
    ns_safe k 671 (by decide) (by decide),ns_safe k 672 (by decide) (by decide),
    ns_safe k 673 (by decide) (by decide),ns_safe k 674 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_669 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 (ns k 669) (ns k 644) := by
  refine ⟨ns k 662,ns k 663,ns k 664,ns k 647,ns_safe k 662 (by decide) (by decide),
    ns_safe k 663 (by decide) (by decide),ns_safe k 664 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def copy_3_4_1 (k : Nat) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 4 (ns k 601) (ns k 508) := by
  refine copyMk (ns k 660) (ns k 644) (ns k 693) (ns k 637) (ns k 618) (ns k 669)
    (ns_safe k 601 (by decide) (by decide)) (ns_safe k 644 (by decide) (by decide)) ?_
    (dec_660 k) (inc_637 k) (inc_618 k) ?_ (dec_693 k) (inc_669 k)
  all_goals run_tac nativeRow
private theorem dec_554 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 (ns k 554) (ns k 557) (ns k 552) := by
  refine ⟨ns k 554,ns k 555,ns k 556,ns k 558,ns k 557,ns k 552,
    ns_safe k 554 (by decide) (by decide),ns_safe k 555 (by decide) (by decide),
    ns_safe k 556 (by decide) (by decide),ns_safe k 558 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_552 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 6 (ns k 552) (ns k 525) := by
  refine ⟨ns k 527,ns k 528,ns k 529,ns k 540,ns_safe k 527 (by decide) (by decide),
    ns_safe k 528 (by decide) (by decide),ns_safe k 529 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem inc_525 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 525) (ns k 508) := by
  refine ⟨ns k 503,ns k 504,ns k 505,ns k 515,ns_safe k 503 (by decide) (by decide),
    ns_safe k 504 (by decide) (by decide),ns_safe k 505 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem dec_594 (k : Nat) :
    DecRows (M:=callerMachine k) (Safe:=NativeSafe k) 5 (ns k 594) (ns k 499) (ns k 559) := by
  refine ⟨ns k 562,ns k 563,ns k 564,ns k 575,ns k 573,ns k 584,
    ns_safe k 562 (by decide) (by decide),ns_safe k 563 (by decide) (by decide),
    ns_safe k 564 (by decide) (by decide),ns_safe k 575 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem inc_559 (k : Nat) :
    IncRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 (ns k 559) (ns k 557) := by
  refine ⟨ns k 559,ns k 560,ns k 561,ns k 557,ns_safe k 559 (by decide) (by decide),
    ns_safe k 560 (by decide) (by decide),ns_safe k 561 (by decide) (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b; cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def copy_0_6_1 (k : Nat) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 6 (ns k 508) (ns k 499) := by
  refine copyMk (ns k 554) (ns k 557) (ns k 594) (ns k 552) (ns k 525) (ns k 559)
    (ns_safe k 508 (by decide) (by decide)) (ns_safe k 557 (by decide) (by decide)) ?_
    (dec_554 k) (inc_552 k) (inc_525 k) ?_ (dec_594 k) (inc_559 k)
  all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
