import PhysicalCallerClosure.RestoreSource
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
      (`PhysicalCallerClosure.RestoreSource,["ReturnRows","RestoreOneRows","RestoreTwoRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing exact restoration type {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong restoration owner"
      logInfo m!"restore-rows-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def ctor (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.RestoreSource 0) "PhysicalCallerClosure") leaf) "mk"
  let some (.ctorInfo ci):=e.find? n | throwError "Missing exact restoration constructor {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.RestoreSource do throwError "Wrong constructor owner"
  logInfo m!"restore-rows-constructor|{n}|{ci.type}"
  closeMainGoal `ctor (mkConst n (ci.levelParams.map Level.param))
private abbrev returnMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {entry out : Fin M.stateCount} →
    (eSL eLH : Fin M.stateCount) → Safe entry →
    (∀ b,M.step entry (some b)=(entry,some b,.right)) → M.step entry none=(eSL,none,.stay) →
    CrossRows (Safe:=Safe) .right eSL eLH → CrossRows (Safe:=Safe) .right eLH out →
    ReturnRows (Safe:=Safe) entry out := by run_tac ctor "ReturnRows"
private abbrev oneMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {b : Bool} → {entry out : Fin M.stateCount} →
    (eL eS restore ret : Fin M.stateCount) → CrossRows (Safe:=Safe) .left entry eL →
    CrossRows (Safe:=Safe) .left eL eS → CrossRows (Safe:=Safe) .left eS restore → Safe restore →
    M.step restore none=(ret,some b,.right) → ReturnRows (Safe:=Safe) ret out →
    RestoreOneRows (Safe:=Safe) b entry out := by run_tac ctor "RestoreOneRows"
private abbrev twoMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {a b : Bool} → {entry out : Fin M.stateCount} →
    (eL eS restoreA scan restoreB ret : Fin M.stateCount) → CrossRows (Safe:=Safe) .left entry eL →
    CrossRows (Safe:=Safe) .left eL eS → CrossRows (Safe:=Safe) .left eS restoreA →
    Safe restoreA → Safe scan → Safe restoreB → M.step restoreA none=(scan,some a,.left) →
    (∀ b,M.step scan (some b)=(scan,some b,.left)) → M.step scan none=(restoreB,none,.stay) →
    M.step restoreB none=(ret,some b,.right) → ReturnRows (Safe:=Safe) ret out →
    RestoreTwoRows (Safe:=Safe) a b entry out := by run_tac ctor "RestoreTwoRows"
section LiteralRows
set_option maxRecDepth 4000
private theorem cross_1514 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1514) (ns k 1512) := by
  refine ⟨ns k 1515,ns_safe k 1514 (by decide) (by decide),ns_safe k 1515 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1512 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1512) (ns k 1510) := by
  refine ⟨ns k 1513,ns_safe k 1512 (by decide) (by decide),ns_safe k 1513 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1510 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1510) (ns k 1509) := by
  refine ⟨ns k 1511,ns_safe k 1510 (by decide) (by decide),ns_safe k 1511 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1505 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1505) (ns k 1503) := by
  refine ⟨ns k 1506,ns_safe k 1505 (by decide) (by decide),ns_safe k 1506 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1503 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1503) (ns k 1499) := by
  refine ⟨ns k 1504,ns_safe k 1503 (by decide) (by decide),ns_safe k 1504 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_1502 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1502) (ns k 1499) := by
  refine returnMk (ns k 1505) (ns k 1503) (ns_safe k 1502 (by decide) (by decide)) ?_ ?_ (cross_1505 k) (cross_1503 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1514 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false false (ns k 1514) (ns k 1499) := by
  refine twoMk (ns k 1512) (ns k 1510) (ns k 1509) (ns k 1508) (ns k 1507) (ns k 1502)
    (cross_1514 k) (cross_1512 k) (cross_1510 k) (ns_safe k 1509 (by decide) (by decide))
    (ns_safe k 1508 (by decide) (by decide)) (ns_safe k 1507 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1502 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2085 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2085) (ns k 2083) := by
  refine ⟨ns k 2086,ns_safe k 2085 (by decide) (by decide),ns_safe k 2086 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2083 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2083) (ns k 2081) := by
  refine ⟨ns k 2084,ns_safe k 2083 (by decide) (by decide),ns_safe k 2084 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2081 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2081) (ns k 2080) := by
  refine ⟨ns k 2082,ns_safe k 2081 (by decide) (by decide),ns_safe k 2082 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2085 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false true (ns k 2085) (ns k 1499) := by
  refine twoMk (ns k 2083) (ns k 2081) (ns k 2080) (ns k 2079) (ns k 2078) (ns k 1502)
    (cross_2085 k) (cross_2083 k) (cross_2081 k) (ns_safe k 2080 (by decide) (by decide))
    (ns_safe k 2079 (by decide) (by decide)) (ns_safe k 2078 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1502 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2219 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2219) (ns k 2217) := by
  refine ⟨ns k 2220,ns_safe k 2219 (by decide) (by decide),ns_safe k 2220 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2217 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2217) (ns k 2215) := by
  refine ⟨ns k 2218,ns_safe k 2217 (by decide) (by decide),ns_safe k 2218 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2215 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2215) (ns k 2214) := by
  refine ⟨ns k 2216,ns_safe k 2215 (by decide) (by decide),ns_safe k 2216 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2219 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 2219) (ns k 1499) := by
  refine oneMk (ns k 2217) (ns k 2215) (ns k 2214) (ns k 1502)
    (cross_2219 k) (cross_2217 k) (cross_2215 k) (ns_safe k 2214 (by decide) (by decide)) ?_ (ret_1502 k)
  run_tac nativeRow
private theorem cross_1751 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1751) (ns k 1749) := by
  refine ⟨ns k 1752,ns_safe k 1751 (by decide) (by decide),ns_safe k 1752 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1749 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1749) (ns k 1747) := by
  refine ⟨ns k 1750,ns_safe k 1749 (by decide) (by decide),ns_safe k 1750 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1747 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1747) (ns k 1746) := by
  refine ⟨ns k 1748,ns_safe k 1747 (by decide) (by decide),ns_safe k 1748 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1751 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true false (ns k 1751) (ns k 1499) := by
  refine twoMk (ns k 1749) (ns k 1747) (ns k 1746) (ns k 1745) (ns k 1744) (ns k 1502)
    (cross_1751 k) (cross_1749 k) (cross_1747 k) (ns_safe k 1746 (by decide) (by decide))
    (ns_safe k 1745 (by decide) (by decide)) (ns_safe k 1744 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1502 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2128 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2128) (ns k 2126) := by
  refine ⟨ns k 2129,ns_safe k 2128 (by decide) (by decide),ns_safe k 2129 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2126 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2126) (ns k 2124) := by
  refine ⟨ns k 2127,ns_safe k 2126 (by decide) (by decide),ns_safe k 2127 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2124 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2124) (ns k 2123) := by
  refine ⟨ns k 2125,ns_safe k 2124 (by decide) (by decide),ns_safe k 2125 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2128 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true true (ns k 2128) (ns k 1499) := by
  refine twoMk (ns k 2126) (ns k 2124) (ns k 2123) (ns k 2122) (ns k 2121) (ns k 1502)
    (cross_2128 k) (cross_2126 k) (cross_2124 k) (ns_safe k 2123 (by decide) (by decide))
    (ns_safe k 2122 (by decide) (by decide)) (ns_safe k 2121 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1502 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2374 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2374) (ns k 2372) := by
  refine ⟨ns k 2375,ns_safe k 2374 (by decide) (by decide),ns_safe k 2375 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2372 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2372) (ns k 2370) := by
  refine ⟨ns k 2373,ns_safe k 2372 (by decide) (by decide),ns_safe k 2373 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2370 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2370) (ns k 2369) := by
  refine ⟨ns k 2371,ns_safe k 2370 (by decide) (by decide),ns_safe k 2371 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2374 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2374) (ns k 1499) := by
  refine oneMk (ns k 2372) (ns k 2370) (ns k 2369) (ns k 1502)
    (cross_2374 k) (cross_2372 k) (cross_2370 k) (ns_safe k 2369 (by decide) (by decide)) ?_ (ret_1502 k)
  run_tac nativeRow
private theorem cross_1918 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1918) (ns k 1916) := by
  refine ⟨ns k 1919,ns_safe k 1918 (by decide) (by decide),ns_safe k 1919 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1916 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1916) (ns k 1914) := by
  refine ⟨ns k 1917,ns_safe k 1916 (by decide) (by decide),ns_safe k 1917 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1914 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1914) (ns k 1913) := by
  refine ⟨ns k 1915,ns_safe k 1914 (by decide) (by decide),ns_safe k 1915 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1918 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 1918) (ns k 1499) := by
  refine oneMk (ns k 1916) (ns k 1914) (ns k 1913) (ns k 1502)
    (cross_1918 k) (cross_1916 k) (cross_1914 k) (ns_safe k 1913 (by decide) (by decide)) ?_ (ret_1502 k)
  run_tac nativeRow
private theorem cross_2169 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2169) (ns k 2167) := by
  refine ⟨ns k 2170,ns_safe k 2169 (by decide) (by decide),ns_safe k 2170 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2167 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2167) (ns k 2165) := by
  refine ⟨ns k 2168,ns_safe k 2167 (by decide) (by decide),ns_safe k 2168 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2165 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2165) (ns k 2164) := by
  refine ⟨ns k 2166,ns_safe k 2165 (by decide) (by decide),ns_safe k 2166 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2169 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2169) (ns k 1499) := by
  refine oneMk (ns k 2167) (ns k 2165) (ns k 2164) (ns k 1502)
    (cross_2169 k) (cross_2167 k) (cross_2165 k) (ns_safe k 2164 (by decide) (by decide)) ?_ (ret_1502 k)
  run_tac nativeRow
private theorem cross_1604 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1604) (ns k 1602) := by
  refine ⟨ns k 1605,ns_safe k 1604 (by decide) (by decide),ns_safe k 1605 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1602 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1602) (ns k 1600) := by
  refine ⟨ns k 1603,ns_safe k 1602 (by decide) (by decide),ns_safe k 1603 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1600 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1600) (ns k 1599) := by
  refine ⟨ns k 1601,ns_safe k 1600 (by decide) (by decide),ns_safe k 1601 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1595 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1595) (ns k 1593) := by
  refine ⟨ns k 1596,ns_safe k 1595 (by decide) (by decide),ns_safe k 1596 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1593 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .right (ns k 1593) (ns k 1589) := by
  refine ⟨ns k 1594,ns_safe k 1593 (by decide) (by decide),ns_safe k 1594 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def ret_1592 (k : Nat) : ReturnRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1592) (ns k 1589) := by
  refine returnMk (ns k 1595) (ns k 1593) (ns_safe k 1592 (by decide) (by decide)) ?_ ?_ (cross_1595 k) (cross_1593 k)
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1604 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false false (ns k 1604) (ns k 1589) := by
  refine twoMk (ns k 1602) (ns k 1600) (ns k 1599) (ns k 1598) (ns k 1597) (ns k 1592)
    (cross_1604 k) (cross_1602 k) (cross_1600 k) (ns_safe k 1599 (by decide) (by decide))
    (ns_safe k 1598 (by decide) (by decide)) (ns_safe k 1597 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1592 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2767 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2767) (ns k 2765) := by
  refine ⟨ns k 2768,ns_safe k 2767 (by decide) (by decide),ns_safe k 2768 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2765 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2765) (ns k 2763) := by
  refine ⟨ns k 2766,ns_safe k 2765 (by decide) (by decide),ns_safe k 2766 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2763 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2763) (ns k 2762) := by
  refine ⟨ns k 2764,ns_safe k 2763 (by decide) (by decide),ns_safe k 2764 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2767 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false true (ns k 2767) (ns k 1589) := by
  refine twoMk (ns k 2765) (ns k 2763) (ns k 2762) (ns k 2761) (ns k 2760) (ns k 1592)
    (cross_2767 k) (cross_2765 k) (cross_2763 k) (ns_safe k 2762 (by decide) (by decide))
    (ns_safe k 2761 (by decide) (by decide)) (ns_safe k 2760 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1592 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2229 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2229) (ns k 2227) := by
  refine ⟨ns k 2230,ns_safe k 2229 (by decide) (by decide),ns_safe k 2230 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2227 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2227) (ns k 2225) := by
  refine ⟨ns k 2228,ns_safe k 2227 (by decide) (by decide),ns_safe k 2228 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2225 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2225) (ns k 2224) := by
  refine ⟨ns k 2226,ns_safe k 2225 (by decide) (by decide),ns_safe k 2226 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2229 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 2229) (ns k 1589) := by
  refine oneMk (ns k 2227) (ns k 2225) (ns k 2224) (ns k 1592)
    (cross_2229 k) (cross_2227 k) (cross_2225 k) (ns_safe k 2224 (by decide) (by decide)) ?_ (ret_1592 k)
  run_tac nativeRow
private theorem cross_1773 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1773) (ns k 1771) := by
  refine ⟨ns k 1774,ns_safe k 1773 (by decide) (by decide),ns_safe k 1774 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1771 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1771) (ns k 1769) := by
  refine ⟨ns k 1772,ns_safe k 1771 (by decide) (by decide),ns_safe k 1772 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1769 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1769) (ns k 1768) := by
  refine ⟨ns k 1770,ns_safe k 1769 (by decide) (by decide),ns_safe k 1770 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1773 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true false (ns k 1773) (ns k 1589) := by
  refine twoMk (ns k 1771) (ns k 1769) (ns k 1768) (ns k 1767) (ns k 1766) (ns k 1592)
    (cross_1773 k) (cross_1771 k) (cross_1769 k) (ns_safe k 1768 (by decide) (by decide))
    (ns_safe k 1767 (by decide) (by decide)) (ns_safe k 1766 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1592 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2899 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2899) (ns k 2897) := by
  refine ⟨ns k 2900,ns_safe k 2899 (by decide) (by decide),ns_safe k 2900 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2897 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2897) (ns k 2895) := by
  refine ⟨ns k 2898,ns_safe k 2897 (by decide) (by decide),ns_safe k 2898 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2895 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2895) (ns k 2894) := by
  refine ⟨ns k 2896,ns_safe k 2895 (by decide) (by decide),ns_safe k 2896 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2899 (k : Nat) : RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true true (ns k 2899) (ns k 1589) := by
  refine twoMk (ns k 2897) (ns k 2895) (ns k 2894) (ns k 2893) (ns k 2892) (ns k 1592)
    (cross_2899 k) (cross_2897 k) (cross_2895 k) (ns_safe k 2894 (by decide) (by decide))
    (ns_safe k 2893 (by decide) (by decide)) (ns_safe k 2892 (by decide) (by decide)) ?_ ?_ ?_ ?_ (ret_1592 k)
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  all_goals run_tac nativeRow
private theorem cross_2384 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2384) (ns k 2382) := by
  refine ⟨ns k 2385,ns_safe k 2384 (by decide) (by decide),ns_safe k 2385 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2382 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2382) (ns k 2380) := by
  refine ⟨ns k 2383,ns_safe k 2382 (by decide) (by decide),ns_safe k 2383 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_2380 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 2380) (ns k 2379) := by
  refine ⟨ns k 2381,ns_safe k 2380 (by decide) (by decide),ns_safe k 2381 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2384 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2384) (ns k 1589) := by
  refine oneMk (ns k 2382) (ns k 2380) (ns k 2379) (ns k 1592)
    (cross_2384 k) (cross_2382 k) (cross_2380 k) (ns_safe k 2379 (by decide) (by decide)) ?_ (ret_1592 k)
  run_tac nativeRow
private theorem cross_1936 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1936) (ns k 1934) := by
  refine ⟨ns k 1937,ns_safe k 1936 (by decide) (by decide),ns_safe k 1937 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1934 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1934) (ns k 1932) := by
  refine ⟨ns k 1935,ns_safe k 1934 (by decide) (by decide),ns_safe k 1935 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_1932 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 1932) (ns k 1931) := by
  refine ⟨ns k 1933,ns_safe k 1932 (by decide) (by decide),ns_safe k 1933 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1936 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 1936) (ns k 1589) := by
  refine oneMk (ns k 1934) (ns k 1932) (ns k 1931) (ns k 1592)
    (cross_1936 k) (cross_1934 k) (cross_1932 k) (ns_safe k 1931 (by decide) (by decide)) ?_ (ret_1592 k)
  run_tac nativeRow
private theorem cross_3027 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 3027) (ns k 3025) := by
  refine ⟨ns k 3028,ns_safe k 3027 (by decide) (by decide),ns_safe k 3028 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_3025 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 3025) (ns k 3023) := by
  refine ⟨ns k 3026,ns_safe k 3025 (by decide) (by decide),ns_safe k 3026 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private theorem cross_3023 (k : Nat) : CrossRows (M:=callerMachine k) (Safe:=NativeSafe k) .left (ns k 3023) (ns k 3022) := by
  refine ⟨ns k 3024,ns_safe k 3023 (by decide) (by decide),ns_safe k 3024 (by decide) (by decide),?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_3027 (k : Nat) : RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 3027) (ns k 1589) := by
  refine oneMk (ns k 3025) (ns k 3023) (ns k 3022) (ns k 1592)
    (cross_3027 k) (cross_3025 k) (cross_3023 k) (ns_safe k 3022 (by decide) (by decide)) ?_ (ret_1592 k)
  run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
