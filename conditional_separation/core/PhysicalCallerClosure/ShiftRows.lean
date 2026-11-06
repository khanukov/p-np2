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
      (`PhysicalCallerClosure.TableSeek,["TableSeekRows"]),(`PhysicalCallerClosure.TableRead,["TableReadRows"]),
      (`PhysicalCallerClosure.ShiftSource,["PlainSeekRows","ShiftRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing exact shift type {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong shift owner"
      logInfo m!"shift-rows-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def ctor (owner : Name) (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf) "mk"
  let some (.ctorInfo ci):=e.find? n | throwError "Missing exact shift constructor {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong constructor owner"
  logInfo m!"shift-rows-constructor|{n}|{ci.type}"
  closeMainGoal `ctor (mkConst n (ci.levelParams.map Level.param))
private abbrev seekMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {entry out : Fin M.stateCount} →
    (eL eS skipAnchor scan : Fin M.stateCount) → CrossRows (Safe:=Safe) .left entry eL →
    CrossRows (Safe:=Safe) .left eL eS → CrossRows (Safe:=Safe) .left eS skipAnchor →
    Safe skipAnchor → Safe scan → M.step skipAnchor none=(scan,none,.left) →
    (∀ b,M.step scan (some b)=(scan,some b,.left)) → M.step scan none=(out,none,.stay) →
    TableSeekRows (Safe:=Safe) entry out := by run_tac ctor `PhysicalCallerClosure.TableSeek "TableSeekRows"
private abbrev shiftMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {anchored b : Bool} →
    {entry : Fin M.stateCount} → {out : Fin 3 → Fin M.stateCount} → (restore read : Fin M.stateCount) →
    (if anchored then Nonempty (TableSeekRows (Safe:=Safe) entry restore) else PlainSeekRows (Safe:=Safe) entry restore) →
    Safe restore → M.step restore none=(read,some b,.right) → TableReadRows (Safe:=Safe) anchored read out →
    ShiftRows (Safe:=Safe) anchored b entry out := by run_tac ctor `PhysicalCallerClosure.ShiftSource "ShiftRows"
private abbrev read_11 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 11)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_11"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_490 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 490)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_490"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_975 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 975)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_975"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_1520 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 1520)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_1520"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_2751 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2751)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_2751"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_1757 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 1757)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_1757"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_2883 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2883)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_2883"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_1924 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 1924)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_1924"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
private abbrev read_3015 : ∀ k : Nat,TableReadRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 3015)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.TableReadRows 0) "PhysicalCallerClosure") "code_3015"
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact read certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.TableReadRows do throwError "Wrong read certificate owner"
    logInfo m!"shift-read-adapter|{n}|{ci.type}"
    closeMainGoal `read (mkConst n (ci.levelParams.map Level.param))
section LiteralRows
set_option maxRecDepth 4000
private theorem cross_1527 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1527) (ns k 1525) := by
  refine ⟨ns k 1528,ns_safe k 1527 (by decide) (by decide),ns_safe k 1528 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1525 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1525) (ns k 1523) := by
  refine ⟨ns k 1526,ns_safe k 1525 (by decide) (by decide),ns_safe k 1526 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1523 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1523) (ns k 1522) := by
  refine ⟨ns k 1524,ns_safe k 1523 (by decide) (by decide),ns_safe k 1524 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1527 (k : Nat) : ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true false (ns k 1527)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  refine shiftMk (ns k 1519) (ns k 1520) ?_ (ns_safe k 1519 (by decide) (by decide)) ?_ (read_1520 k)
  · refine ⟨seekMk (ns k 1525) (ns k 1523) (ns k 1522) (ns k 1521) (cross_1527 k) (cross_1525 k) (cross_1523 k)
      (ns_safe k 1522 (by decide) (by decide)) (ns_safe k 1521 (by decide) (by decide)) ?_ ?_ ?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2758 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2758) (ns k 2756) := by
  refine ⟨ns k 2759,ns_safe k 2758 (by decide) (by decide),ns_safe k 2759 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2756 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2756) (ns k 2754) := by
  refine ⟨ns k 2757,ns_safe k 2756 (by decide) (by decide),ns_safe k 2757 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2754 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2754) (ns k 2753) := by
  refine ⟨ns k 2755,ns_safe k 2754 (by decide) (by decide),ns_safe k 2755 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2758 (k : Nat) : ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true true (ns k 2758)
    (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  refine shiftMk (ns k 2750) (ns k 2751) ?_ (ns_safe k 2750 (by decide) (by decide)) ?_ (read_2751 k)
  · refine ⟨seekMk (ns k 2756) (ns k 2754) (ns k 2753) (ns k 2752) (cross_2758 k) (cross_2756 k) (cross_2754 k)
      (ns_safe k 2753 (by decide) (by decide)) (ns_safe k 2752 (by decide) (by decide)) ?_ ?_ ?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1764 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1764) (ns k 1762) := by
  refine ⟨ns k 1765,ns_safe k 1764 (by decide) (by decide),ns_safe k 1765 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1762 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1762) (ns k 1760) := by
  refine ⟨ns k 1763,ns_safe k 1762 (by decide) (by decide),ns_safe k 1763 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1760 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1760) (ns k 1759) := by
  refine ⟨ns k 1761,ns_safe k 1760 (by decide) (by decide),ns_safe k 1761 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1764 (k : Nat) : ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true false (ns k 1764)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  refine shiftMk (ns k 1756) (ns k 1757) ?_ (ns_safe k 1756 (by decide) (by decide)) ?_ (read_1757 k)
  · refine ⟨seekMk (ns k 1762) (ns k 1760) (ns k 1759) (ns k 1758) (cross_1764 k) (cross_1762 k) (cross_1760 k)
      (ns_safe k 1759 (by decide) (by decide)) (ns_safe k 1758 (by decide) (by decide)) ?_ ?_ ?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2890 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2890) (ns k 2888) := by
  refine ⟨ns k 2891,ns_safe k 2890 (by decide) (by decide),ns_safe k 2891 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2888 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2888) (ns k 2886) := by
  refine ⟨ns k 2889,ns_safe k 2888 (by decide) (by decide),ns_safe k 2889 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2886 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2886) (ns k 2885) := by
  refine ⟨ns k 2887,ns_safe k 2886 (by decide) (by decide),ns_safe k 2887 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2890 (k : Nat) : ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true true (ns k 2890)
    (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  refine shiftMk (ns k 2882) (ns k 2883) ?_ (ns_safe k 2882 (by decide) (by decide)) ?_ (read_2883 k)
  · refine ⟨seekMk (ns k 2888) (ns k 2886) (ns k 2885) (ns k 2884) (cross_2890 k) (cross_2888 k) (cross_2886 k)
      (ns_safe k 2885 (by decide) (by decide)) (ns_safe k 2884 (by decide) (by decide)) ?_ ?_ ?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1929 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1929) (ns k 1927) := by
  refine ⟨ns k 1930,ns_safe k 1929 (by decide) (by decide),ns_safe k 1930 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1927 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1927) (ns k 1925) := by
  refine ⟨ns k 1928,ns_safe k 1927 (by decide) (by decide),ns_safe k 1928 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1925 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1925) (ns k 1923) := by
  refine ⟨ns k 1926,ns_safe k 1925 (by decide) (by decide),ns_safe k 1926 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1929 (k : Nat) : ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) false false (ns k 1929)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  refine shiftMk (ns k 1923) (ns k 1924) ?_ (ns_safe k 1923 (by decide) (by decide)) ?_ (read_1924 k)
  · exact ⟨ns k 1927,ns k 1925,cross_1929 k,cross_1927 k,cross_1925 k⟩
  · run_tac nativeRow
private theorem cross_3020 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 3020) (ns k 3018) := by
  refine ⟨ns k 3021,ns_safe k 3020 (by decide) (by decide),ns_safe k 3021 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_3018 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 3018) (ns k 3016) := by
  refine ⟨ns k 3019,ns_safe k 3018 (by decide) (by decide),ns_safe k 3019 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_3016 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 3016) (ns k 3014) := by
  refine ⟨ns k 3017,ns_safe k 3016 (by decide) (by decide),ns_safe k 3017 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_3020 (k : Nat) : ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) false true (ns k 3020)
    (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  refine shiftMk (ns k 3014) (ns k 3015) ?_ (ns_safe k 3014 (by decide) (by decide)) ?_ (read_3015 k)
  · exact ⟨ns k 3018,ns k 3016,cross_3020 k,cross_3018 k,cross_3016 k⟩
  · run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
