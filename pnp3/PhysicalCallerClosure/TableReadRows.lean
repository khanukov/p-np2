import PhysicalCallerClosure.TableRead
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
      (`PhysicalCallerClosure.RestoreSource,["ReturnRows"]),(`PhysicalCallerClosure.AnchorReturn,["AnchorReturnRows"]),
      (`PhysicalCallerClosure.TableRead,["boolTag","TableReadRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing exact table-read type {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong table-read owner"
      logInfo m!"table-read-rows-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def ctor (owner : Name) (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf) "mk"
  let some (.ctorInfo ci):=e.find? n | throwError "Missing exact table-read constructor {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong constructor owner"
  logInfo m!"table-read-rows-constructor|{n}|{ci.type}"
  closeMainGoal `ctor (mkConst n (ci.levelParams.map Level.param))
private abbrev returnMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {entry out : Fin M.stateCount} →
    (eSL eLH : Fin M.stateCount) → Safe entry →
    (∀ b,M.step entry (some b)=(entry,some b,.right)) → M.step entry none=(eSL,none,.stay) →
    CrossRows (Safe:=Safe) .right eSL eLH → CrossRows (Safe:=Safe) .right eLH out →
    ReturnRows (Safe:=Safe) entry out := by run_tac ctor `PhysicalCallerClosure.RestoreSource "ReturnRows"
private abbrev anchorMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {entry out : Fin M.stateCount} →
    (afterAnchor : Fin M.stateCount) → Safe entry →
    (∀ b,M.step entry (some b)=(entry,some b,.right)) → M.step entry none=(afterAnchor,none,.right) →
    ReturnRows (Safe:=Safe) afterAnchor out → AnchorReturnRows (Safe:=Safe) entry out := by
  run_tac ctor `PhysicalCallerClosure.AnchorReturn "AnchorReturnRows"
private abbrev readMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {anchored : Bool} →
    {entry : Fin M.stateCount} → {out : Fin 3 → Fin M.stateCount} →
    (ret : Bool → Fin M.stateCount) → (eSL eLH : Fin M.stateCount) → Safe entry →
    (∀ b,M.step entry (some b)=(ret b,none,.right)) → M.step entry none=(eSL,none,.stay) →
    (∀ b,if anchored then Nonempty (AnchorReturnRows (Safe:=Safe) (ret b) (out (boolTag b)))
      else Nonempty (ReturnRows (Safe:=Safe) (ret b) (out (boolTag b)))) →
    CrossRows (Safe:=Safe) .right eSL eLH → CrossRows (Safe:=Safe) .right eLH (out ⟨2,by decide⟩) →
    TableReadRows (Safe:=Safe) anchored entry out := by run_tac ctor `PhysicalCallerClosure.TableRead "TableReadRows"
section LiteralRows
set_option maxRecDepth 4000
private theorem cross_486 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 486) (ns k 484) := by
  refine ⟨ns k 487,ns_safe k 486 (by decide) (by decide),ns_safe k 487 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_484 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 484) (ns k 481) := by
  refine ⟨ns k 485,ns_safe k 484 (by decide) (by decide),ns_safe k 485 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_406 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 406) (ns k 404) := by
  refine ⟨ns k 407,ns_safe k 406 (by decide) (by decide),ns_safe k 407 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_404 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 404) (ns k 399) := by
  refine ⟨ns k 405,ns_safe k 404 (by decide) (by decide),ns_safe k 405 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_403 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 403) (ns k 399) := by
  refine returnMk (ns k 406) (ns k 404) (ns_safe k 403 (by decide) (by decide)) ?_ ?_ (cross_406 k) (cross_404 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def anchor_402 (k : Nat) : AnchorReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 402) (ns k 399) := by
  refine anchorMk (ns k 403) (ns_safe k 402 (by decide) (by decide)) ?_ ?_ (ret_403 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_447 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 447) (ns k 445) := by
  refine ⟨ns k 448,ns_safe k 447 (by decide) (by decide),ns_safe k 448 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_445 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 445) (ns k 440) := by
  refine ⟨ns k 446,ns_safe k 445 (by decide) (by decide),ns_safe k 446 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_444 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 444) (ns k 440) := by
  refine returnMk (ns k 447) (ns k 445) (ns_safe k 444 (by decide) (by decide)) ?_ ?_ (cross_447 k) (cross_445 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def anchor_443 (k : Nat) : AnchorReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 443) (ns k 440) := by
  refine anchorMk (ns k 444) (ns_safe k 443 (by decide) (by decide)) ?_ ?_ (ret_444 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_11 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 11)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 443 else ns k 402) (ns k 486) (ns k 484) (ns_safe k 11 (by decide) (by decide)) ?_ ?_ ?_ (cross_486 k) (cross_484 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨anchor_402 k⟩
    · exact ⟨anchor_443 k⟩
private theorem cross_955 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 955) (ns k 953) := by
  refine ⟨ns k 956,ns_safe k 955 (by decide) (by decide),ns_safe k 956 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_953 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 953) (ns k 950) := by
  refine ⟨ns k 954,ns_safe k 953 (by decide) (by decide),ns_safe k 954 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_875 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 875) (ns k 873) := by
  refine ⟨ns k 876,ns_safe k 875 (by decide) (by decide),ns_safe k 876 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_873 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 873) (ns k 868) := by
  refine ⟨ns k 874,ns_safe k 873 (by decide) (by decide),ns_safe k 874 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_872 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 872) (ns k 868) := by
  refine returnMk (ns k 875) (ns k 873) (ns_safe k 872 (by decide) (by decide)) ?_ ?_ (cross_875 k) (cross_873 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def anchor_871 (k : Nat) : AnchorReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 871) (ns k 868) := by
  refine anchorMk (ns k 872) (ns_safe k 871 (by decide) (by decide)) ?_ ?_ (ret_872 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_916 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 916) (ns k 914) := by
  refine ⟨ns k 917,ns_safe k 916 (by decide) (by decide),ns_safe k 917 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_914 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 914) (ns k 909) := by
  refine ⟨ns k 915,ns_safe k 914 (by decide) (by decide),ns_safe k 915 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_913 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 913) (ns k 909) := by
  refine returnMk (ns k 916) (ns k 914) (ns_safe k 913 (by decide) (by decide)) ?_ ?_ (cross_916 k) (cross_914 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def anchor_912 (k : Nat) : AnchorReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 912) (ns k 909) := by
  refine anchorMk (ns k 913) (ns_safe k 912 (by decide) (by decide)) ?_ ?_ (ret_913 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_490 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 490)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 912 else ns k 871) (ns k 955) (ns k 953) (ns_safe k 490 (by decide) (by decide)) ?_ ?_ ?_ (cross_955 k) (cross_953 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨anchor_871 k⟩
    · exact ⟨anchor_912 k⟩
private theorem cross_1430 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1430) (ns k 1428) := by
  refine ⟨ns k 1431,ns_safe k 1430 (by decide) (by decide),ns_safe k 1431 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1428 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1428) (ns k 1425) := by
  refine ⟨ns k 1429,ns_safe k 1428 (by decide) (by decide),ns_safe k 1429 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1351 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1351) (ns k 1349) := by
  refine ⟨ns k 1352,ns_safe k 1351 (by decide) (by decide),ns_safe k 1352 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1349 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1349) (ns k 1345) := by
  refine ⟨ns k 1350,ns_safe k 1349 (by decide) (by decide),ns_safe k 1350 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_1348 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1348) (ns k 1345) := by
  refine returnMk (ns k 1351) (ns k 1349) (ns_safe k 1348 (by decide) (by decide)) ?_ ?_ (cross_1351 k) (cross_1349 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1391 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1391) (ns k 1389) := by
  refine ⟨ns k 1392,ns_safe k 1391 (by decide) (by decide),ns_safe k 1392 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1389 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1389) (ns k 1385) := by
  refine ⟨ns k 1390,ns_safe k 1389 (by decide) (by decide),ns_safe k 1390 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_1388 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1388) (ns k 1385) := by
  refine returnMk (ns k 1391) (ns k 1389) (ns_safe k 1388 (by decide) (by decide)) ?_ ?_ (cross_1391 k) (cross_1389 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_975 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 975)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 1388 else ns k 1348) (ns k 1430) (ns k 1428) (ns_safe k 975 (by decide) (by decide)) ?_ ?_ ?_ (cross_1430 k) (cross_1428 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨ret_1348 k⟩
    · exact ⟨ret_1388 k⟩
private def code_1520 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 1520)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 443 else ns k 402) (ns k 486) (ns k 484) (ns_safe k 1520 (by decide) (by decide)) ?_ ?_ ?_ (cross_486 k) (cross_484 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨anchor_402 k⟩
    · exact ⟨anchor_443 k⟩
private def code_2751 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2751)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 443 else ns k 402) (ns k 486) (ns k 484) (ns_safe k 2751 (by decide) (by decide)) ?_ ?_ ?_ (cross_486 k) (cross_484 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨anchor_402 k⟩
    · exact ⟨anchor_443 k⟩
private def code_1757 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 1757)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 912 else ns k 871) (ns k 955) (ns k 953) (ns_safe k 1757 (by decide) (by decide)) ?_ ?_ ?_ (cross_955 k) (cross_953 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨anchor_871 k⟩
    · exact ⟨anchor_912 k⟩
private def code_2883 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2883)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 912 else ns k 871) (ns k 955) (ns k 953) (ns_safe k 2883 (by decide) (by decide)) ?_ ?_ ?_ (cross_955 k) (cross_953 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨anchor_871 k⟩
    · exact ⟨anchor_912 k⟩
private def code_1924 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 1924)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 1388 else ns k 1348) (ns k 1430) (ns k 1428) (ns_safe k 1924 (by decide) (by decide)) ?_ ?_ ?_ (cross_1430 k) (cross_1428 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨ret_1348 k⟩
    · exact ⟨ret_1388 k⟩
private def code_3015 (k : Nat) : TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 3015)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  refine readMk (fun b=>if b then ns k 1388 else ns k 1348) (ns k 1430) (ns k 1428) (ns_safe k 3015 (by decide) (by decide)) ?_ ?_ ?_ (cross_1430 k) (cross_1428 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b
    · exact ⟨ret_1348 k⟩
    · exact ⟨ret_1388 k⟩
end LiteralRows
end PhysicalCallerClosure
