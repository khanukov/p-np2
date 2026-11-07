import PhysicalCallerClosure.Metadata
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
  for leaf in ["ns","NativeSafe","nativeRoute","nativeRow","ns_safe","FromHRows","RouteR","RouteL"] do
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Metadata,["BitsRows","MetaRows"]),
      (`PhysicalCallerClosure.Navigation,["ToHRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing exact metadata type {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong metadata owner"
      logInfo m!"metadata-rows-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def ctor (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Metadata 0) "PhysicalCallerClosure") leaf) "mk"
  let some (.ctorInfo ci):=e.find? n | throwError "Missing exact metadata constructor {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Metadata do throwError "Wrong constructor owner"
  logInfo m!"metadata-rows-constructor|{n}|{ci.type}"
  closeMainGoal `ctor (mkConst n (ci.levelParams.map Level.param))
private abbrev bitsMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {bits : Fin 5 → Bool} →
    {entry out : Fin M.stateCount} → (states : Fin 6 → Fin M.stateCount) → (back : Fin M.stateCount) →
    Safe entry → (∀ j,Safe (states j)) → Safe back →
    M.step entry none=(states ⟨0,by decide⟩,none,.right) →
    (∀ j:Fin 5,M.step (states (Fin.castSucc j)) (some (bits j))=(states (Fin.succ j),some (bits j),.right)) →
    M.step (states ⟨5,by decide⟩) none=(back,none,.left) →
    (∀ b,M.step back (some b)=(back,some b,.left)) → M.step back none=(out,none,.stay) →
    BitsRows (Safe:=Safe) bits entry out := by run_tac ctor "BitsRows"
private abbrev metaMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {bits : Fin 5 → Bool} →
    {entry out : Fin M.stateCount} → (first fieldEntry returnEntry homeEntry : Fin M.stateCount) →
    FromHRows (Safe:=Safe) entry first → RouteR M Safe 0 12 first fieldEntry →
    BitsRows (Safe:=Safe) bits fieldEntry returnEntry → RouteL M Safe 12 0 returnEntry homeEntry →
    ToHRows (Safe:=Safe) homeEntry out → MetaRows (Safe:=Safe) bits entry out := by run_tac ctor "MetaRows"
section LiteralRows
set_option maxRecDepth 4000
private theorem from_0 (k : Nat) :
    FromHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2714) (ns k 2712) := by
  refine ⟨ns k 2715,ns k 2716,(ns_safe k 2714 (by decide) (by decide)),(ns_safe k 2715 (by decide) (by decide)),(ns_safe k 2716 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
private theorem outward_0 (k : Nat) :
    RouteR (callerMachine k) (NativeSafe k) 0 12 (ns k 2712) (ns k 1433) := by
  run_tac nativeRoute 14
private def code_0_0_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 2714) (ns k 1435) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 1706) (ns k 1680) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,1908,1739,1708,1678][j.val]!)) (ns k 1679) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 1679 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some false)=(ns k 1908,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1908) (some false)=(ns k 1739,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1739) (some false)=(ns k 1708,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1708) (some false)=(ns k 1678,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 1678) none=(ns k 1679,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1681,ns k 1682,ns k 1683,(ns_safe k 1680 (by decide) (by decide)),(ns_safe k 1681 (by decide) (by decide)),(ns_safe k 1682 (by decide) (by decide)),(ns_safe k 1683 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_0_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 2714) (ns k 1514) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 1737) (ns k 1711) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,1908,1739,1708,1709][j.val]!)) (ns k 1710) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 1710 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some false)=(ns k 1908,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1908) (some false)=(ns k 1739,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1739) (some false)=(ns k 1708,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1708) (some true)=(ns k 1709,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 1709) none=(ns k 1710,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1712,ns k 1713,ns k 1714,(ns_safe k 1711 (by decide) (by decide)),(ns_safe k 1712 (by decide) (by decide)),(ns_safe k 1713 (by decide) (by decide)),(ns_safe k 1714 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_0_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 2714) (ns k 2085) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2115) (ns k 2089) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,2163,2120,2117,2087][j.val]!)) (ns k 2088) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2088 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some true)=(ns k 2163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2163) (some false)=(ns k 2120,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2120) (some false)=(ns k 2117,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2117) (some false)=(ns k 2087,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2087) none=(ns k 2088,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2090,ns k 2091,ns k 2092,(ns_safe k 2089 (by decide) (by decide)),(ns_safe k 2090 (by decide) (by decide)),(ns_safe k 2091 (by decide) (by decide)),(ns_safe k 2092 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_0_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 2714) (ns k 2085) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2115) (ns k 2089) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,2163,2120,2117,2118][j.val]!)) (ns k 2119) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2119 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some true)=(ns k 2163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2163) (some false)=(ns k 2120,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2120) (some false)=(ns k 2117,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2117) (some true)=(ns k 2118,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2118) none=(ns k 2119,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2090,ns k 2091,ns k 2092,(ns_safe k 2089 (by decide) (by decide)),(ns_safe k 2090 (by decide) (by decide)),(ns_safe k 2091 (by decide) (by decide)),(ns_safe k 2092 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_0_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 2714) (ns k 2210) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2331) (ns k 2305) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2666,2519,2364,2333,2303][j.val]!)) (ns k 2304) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2304 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some true)=(ns k 2666,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2666) (some false)=(ns k 2519,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2519) (some false)=(ns k 2364,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2364) (some false)=(ns k 2333,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2333) (some false)=(ns k 2303,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2303) none=(ns k 2304,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2306,ns k 2307,ns k 2308,(ns_safe k 2305 (by decide) (by decide)),(ns_safe k 2306 (by decide) (by decide)),(ns_safe k 2307 (by decide) (by decide)),(ns_safe k 2308 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_0_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 2714) (ns k 2219) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2362) (ns k 2336) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2666,2519,2364,2333,2334][j.val]!)) (ns k 2335) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2335 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some true)=(ns k 2666,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2666) (some false)=(ns k 2519,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2519) (some false)=(ns k 2364,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2364) (some false)=(ns k 2333,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2333) (some true)=(ns k 2334,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2334) none=(ns k 2335,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2337,ns k 2338,ns k 2339,(ns_safe k 2336 (by decide) (by decide)),(ns_safe k 2337 (by decide) (by decide)),(ns_safe k 2338 (by decide) (by decide)),(ns_safe k 2339 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_1_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 2714) (ns k 1740) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 1875) (ns k 1849) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,1908,1739,1877,1847][j.val]!)) (ns k 1848) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 1848 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some false)=(ns k 1908,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1908) (some false)=(ns k 1739,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1739) (some true)=(ns k 1877,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1877) (some false)=(ns k 1847,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 1847) none=(ns k 1848,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1850,ns k 1851,ns k 1852,(ns_safe k 1849 (by decide) (by decide)),(ns_safe k 1850 (by decide) (by decide)),(ns_safe k 1851 (by decide) (by decide)),(ns_safe k 1852 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_1_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 2714) (ns k 1751) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 1906) (ns k 1880) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,1908,1739,1877,1878][j.val]!)) (ns k 1879) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 1879 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some false)=(ns k 1908,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1908) (some false)=(ns k 1739,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1739) (some true)=(ns k 1877,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1877) (some true)=(ns k 1878,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 1878) none=(ns k 1879,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1881,ns k 1882,ns k 1883,(ns_safe k 1880 (by decide) (by decide)),(ns_safe k 1881 (by decide) (by decide)),(ns_safe k 1882 (by decide) (by decide)),(ns_safe k 1883 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_1_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 2714) (ns k 2128) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2158) (ns k 2132) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,2163,2120,2160,2130][j.val]!)) (ns k 2131) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2131 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some true)=(ns k 2163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2163) (some false)=(ns k 2120,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2120) (some true)=(ns k 2160,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2160) (some false)=(ns k 2130,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2130) none=(ns k 2131,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2133,ns k 2134,ns k 2135,(ns_safe k 2132 (by decide) (by decide)),(ns_safe k 2133 (by decide) (by decide)),(ns_safe k 2134 (by decide) (by decide)),(ns_safe k 2135 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_1_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 2714) (ns k 2128) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2158) (ns k 2132) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,2163,2120,2160,2161][j.val]!)) (ns k 2162) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2162 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some true)=(ns k 2163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2163) (some false)=(ns k 2120,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2120) (some true)=(ns k 2160,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2160) (some true)=(ns k 2161,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2161) none=(ns k 2162,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2133,ns k 2134,ns k 2135,(ns_safe k 2132 (by decide) (by decide)),(ns_safe k 2133 (by decide) (by decide)),(ns_safe k 2134 (by decide) (by decide)),(ns_safe k 2135 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_1_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 2714) (ns k 2365) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2486) (ns k 2460) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2666,2519,2364,2488,2458][j.val]!)) (ns k 2459) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2459 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some true)=(ns k 2666,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2666) (some false)=(ns k 2519,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2519) (some false)=(ns k 2364,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2364) (some true)=(ns k 2488,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2488) (some false)=(ns k 2458,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2458) none=(ns k 2459,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2461,ns k 2462,ns k 2463,(ns_safe k 2460 (by decide) (by decide)),(ns_safe k 2461 (by decide) (by decide)),(ns_safe k 2462 (by decide) (by decide)),(ns_safe k 2463 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_1_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 2714) (ns k 2374) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2517) (ns k 2491) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2666,2519,2364,2488,2489][j.val]!)) (ns k 2490) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2490 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some true)=(ns k 2666,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2666) (some false)=(ns k 2519,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2519) (some false)=(ns k 2364,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2364) (some true)=(ns k 2488,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2488) (some true)=(ns k 2489,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2489) none=(ns k 2490,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2492,ns k 2493,ns k 2494,(ns_safe k 2491 (by decide) (by decide)),(ns_safe k 2492 (by decide) (by decide)),(ns_safe k 2493 (by decide) (by decide)),(ns_safe k 2494 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_2_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 2714) (ns k 1909) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2038) (ns k 2012) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,1908,2071,2040,2010][j.val]!)) (ns k 2011) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2011 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some false)=(ns k 1908,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1908) (some true)=(ns k 2071,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2071) (some false)=(ns k 2040,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2040) (some false)=(ns k 2010,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2010) none=(ns k 2011,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2013,ns k 2014,ns k 2015,(ns_safe k 2012 (by decide) (by decide)),(ns_safe k 2013 (by decide) (by decide)),(ns_safe k 2014 (by decide) (by decide)),(ns_safe k 2015 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_2_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 2714) (ns k 1918) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2069) (ns k 2043) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,1908,2071,2040,2041][j.val]!)) (ns k 2042) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2042 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some false)=(ns k 1908,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 1908) (some true)=(ns k 2071,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2071) (some false)=(ns k 2040,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2040) (some true)=(ns k 2041,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2041) none=(ns k 2042,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2044,ns k 2045,ns k 2046,(ns_safe k 2043 (by decide) (by decide)),(ns_safe k 2044 (by decide) (by decide)),(ns_safe k 2045 (by decide) (by decide)),(ns_safe k 2046 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_2_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 2714) (ns k 2169) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2199) (ns k 2173) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,2163,2204,2201,2171][j.val]!)) (ns k 2172) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2172 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some true)=(ns k 2163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2163) (some true)=(ns k 2204,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2204) (some false)=(ns k 2201,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2201) (some false)=(ns k 2171,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2171) none=(ns k 2172,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2174,ns k 2175,ns k 2176,(ns_safe k 2173 (by decide) (by decide)),(ns_safe k 2174 (by decide) (by decide)),(ns_safe k 2175 (by decide) (by decide)),(ns_safe k 2176 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_2_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 2714) (ns k 2169) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2199) (ns k 2173) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2077,2163,2204,2201,2202][j.val]!)) (ns k 2203) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2203 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some false)=(ns k 2077,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2077) (some true)=(ns k 2163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2163) (some true)=(ns k 2204,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2204) (some false)=(ns k 2201,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2201) (some true)=(ns k 2202,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2202) none=(ns k 2203,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2174,ns k 2175,ns k 2176,(ns_safe k 2173 (by decide) (by decide)),(ns_safe k 2174 (by decide) (by decide)),(ns_safe k 2175 (by decide) (by decide)),(ns_safe k 2176 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_2_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 2714) (ns k 2520) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2627) (ns k 2601) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2666,2519,2660,2629,2599][j.val]!)) (ns k 2600) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2600 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some true)=(ns k 2666,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2666) (some false)=(ns k 2519,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2519) (some true)=(ns k 2660,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2660) (some false)=(ns k 2629,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2629) (some false)=(ns k 2599,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2599) none=(ns k 2600,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2602,ns k 2603,ns k 2604,(ns_safe k 2601 (by decide) (by decide)),(ns_safe k 2602 (by decide) (by decide)),(ns_safe k 2603 (by decide) (by decide)),(ns_safe k 2604 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_0_2_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 2714) (ns k 1499) := by
  refine metaMk (ns k 2712) (ns k 1433) (ns k 2658) (ns k 2632) (from_0 k) (outward_0 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[1434,2666,2519,2660,2629,2630][j.val]!)) (ns k 2631) (ns_safe k 1433 (by decide) (by decide)) ?_ (ns_safe k 2631 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1433) none=(ns k 1434,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 1434) (some true)=(ns k 2666,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2666) (some false)=(ns k 2519,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2519) (some true)=(ns k 2660,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2660) (some false)=(ns k 2629,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2629) (some true)=(ns k 2630,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2630) none=(ns k 2631,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2633,ns k 2634,ns k 2635,(ns_safe k 2632 (by decide) (by decide)),(ns_safe k 2633 (by decide) (by decide)),(ns_safe k 2634 (by decide) (by decide)),(ns_safe k 2635 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
