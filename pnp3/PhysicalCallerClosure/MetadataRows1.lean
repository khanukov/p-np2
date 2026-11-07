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
private theorem from_1 (k : Nat) :
    FromHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3211) (ns k 3209) := by
  refine ⟨ns k 3212,ns k 3213,(ns_safe k 3211 (by decide) (by decide)),(ns_safe k 3212 (by decide) (by decide)),(ns_safe k 3213 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
private theorem outward_1 (k : Nat) :
    RouteR (callerMachine k) (NativeSafe k) 0 12 (ns k 3209) (ns k 2717) := by
  run_tac nativeRoute 14
private def code_1_0_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 3211) (ns k 1514) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 1737) (ns k 1711) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,2730,2724,2721,2719][j.val]!)) (ns k 2720) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2720 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some false)=(ns k 2730,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2730) (some false)=(ns k 2724,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2724) (some false)=(ns k 2721,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2721) (some false)=(ns k 2719,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2719) none=(ns k 2720,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1712,ns k 1713,ns k 1714,(ns_safe k 1711 (by decide) (by decide)),(ns_safe k 1712 (by decide) (by decide)),(ns_safe k 1713 (by decide) (by decide)),(ns_safe k 1714 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_0_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 3211) (ns k 1514) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 1737) (ns k 1711) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,2730,2724,2721,2722][j.val]!)) (ns k 2723) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2723 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some false)=(ns k 2730,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2730) (some false)=(ns k 2724,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2724) (some false)=(ns k 2721,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2721) (some true)=(ns k 2722,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2722) none=(ns k 2723,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1712,ns k 1713,ns k 1714,(ns_safe k 1711 (by decide) (by decide)),(ns_safe k 1712 (by decide) (by decide)),(ns_safe k 1713 (by decide) (by decide)),(ns_safe k 1714 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_0_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 3211) (ns k 2743) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2869) (ns k 2843) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,3006,2874,2871,2841][j.val]!)) (ns k 2842) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2842 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some true)=(ns k 3006,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3006) (some false)=(ns k 2874,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2874) (some false)=(ns k 2871,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2871) (some false)=(ns k 2841,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2841) none=(ns k 2842,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2844,ns k 2845,ns k 2846,(ns_safe k 2843 (by decide) (by decide)),(ns_safe k 2844 (by decide) (by decide)),(ns_safe k 2845 (by decide) (by decide)),(ns_safe k 2846 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_0_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 3211) (ns k 2085) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2115) (ns k 2089) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,3006,2874,2871,2872][j.val]!)) (ns k 2873) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2873 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some true)=(ns k 3006,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3006) (some false)=(ns k 2874,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2874) (some false)=(ns k 2871,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2871) (some true)=(ns k 2872,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2872) none=(ns k 2873,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2090,ns k 2091,ns k 2092,(ns_safe k 2089 (by decide) (by decide)),(ns_safe k 2090 (by decide) (by decide)),(ns_safe k 2091 (by decide) (by decide)),(ns_safe k 2092 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_0_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 3211) (ns k 2219) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2362) (ns k 2336) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,3163,3151,3145,3142,3140][j.val]!)) (ns k 3141) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3141 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some true)=(ns k 3163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3163) (some false)=(ns k 3151,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3151) (some false)=(ns k 3145,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3145) (some false)=(ns k 3142,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3142) (some false)=(ns k 3140,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3140) none=(ns k 3141,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2337,ns k 2338,ns k 2339,(ns_safe k 2336 (by decide) (by decide)),(ns_safe k 2337 (by decide) (by decide)),(ns_safe k 2338 (by decide) (by decide)),(ns_safe k 2339 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_0_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 3211) (ns k 2219) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2362) (ns k 2336) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,3163,3151,3145,3142,3143][j.val]!)) (ns k 3144) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3144 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some true)=(ns k 3163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3163) (some false)=(ns k 3151,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3151) (some false)=(ns k 3145,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3145) (some false)=(ns k 3142,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3142) (some true)=(ns k 3143,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3143) none=(ns k 3144,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2337,ns k 2338,ns k 2339,(ns_safe k 2336 (by decide) (by decide)),(ns_safe k 2337 (by decide) (by decide)),(ns_safe k 2338 (by decide) (by decide)),(ns_safe k 2339 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_1_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 3211) (ns k 1751) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 1906) (ns k 1880) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,2730,2724,2727,2725][j.val]!)) (ns k 2726) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2726 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some false)=(ns k 2730,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2730) (some false)=(ns k 2724,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2724) (some true)=(ns k 2727,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2727) (some false)=(ns k 2725,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2725) none=(ns k 2726,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1881,ns k 1882,ns k 1883,(ns_safe k 1880 (by decide) (by decide)),(ns_safe k 1881 (by decide) (by decide)),(ns_safe k 1882 (by decide) (by decide)),(ns_safe k 1883 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_1_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 3211) (ns k 1751) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 1906) (ns k 1880) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,2730,2724,2727,2728][j.val]!)) (ns k 2729) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2729 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some false)=(ns k 2730,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2730) (some false)=(ns k 2724,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2724) (some true)=(ns k 2727,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2727) (some true)=(ns k 2728,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2728) none=(ns k 2729,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1881,ns k 1882,ns k 1883,(ns_safe k 1880 (by decide) (by decide)),(ns_safe k 1881 (by decide) (by decide)),(ns_safe k 1882 (by decide) (by decide)),(ns_safe k 1883 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_1_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 3211) (ns k 2875) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 3001) (ns k 2975) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,3006,2874,3003,2973][j.val]!)) (ns k 2974) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2974 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some true)=(ns k 3006,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3006) (some false)=(ns k 2874,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2874) (some true)=(ns k 3003,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3003) (some false)=(ns k 2973,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2973) none=(ns k 2974,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2976,ns k 2977,ns k 2978,(ns_safe k 2975 (by decide) (by decide)),(ns_safe k 2976 (by decide) (by decide)),(ns_safe k 2977 (by decide) (by decide)),(ns_safe k 2978 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_1_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 3211) (ns k 2128) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2158) (ns k 2132) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,3006,2874,3003,3004][j.val]!)) (ns k 3005) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3005 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some true)=(ns k 3006,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3006) (some false)=(ns k 2874,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2874) (some true)=(ns k 3003,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3003) (some true)=(ns k 3004,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3004) none=(ns k 3005,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2133,ns k 2134,ns k 2135,(ns_safe k 2132 (by decide) (by decide)),(ns_safe k 2133 (by decide) (by decide)),(ns_safe k 2134 (by decide) (by decide)),(ns_safe k 2135 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_1_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 3211) (ns k 2374) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2517) (ns k 2491) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,3163,3151,3145,3148,3146][j.val]!)) (ns k 3147) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3147 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some true)=(ns k 3163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3163) (some false)=(ns k 3151,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3151) (some false)=(ns k 3145,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3145) (some true)=(ns k 3148,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3148) (some false)=(ns k 3146,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3146) none=(ns k 3147,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2492,ns k 2493,ns k 2494,(ns_safe k 2491 (by decide) (by decide)),(ns_safe k 2492 (by decide) (by decide)),(ns_safe k 2493 (by decide) (by decide)),(ns_safe k 2494 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_1_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 3211) (ns k 2374) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2517) (ns k 2491) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,3163,3151,3145,3148,3149][j.val]!)) (ns k 3150) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3150 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some true)=(ns k 3163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3163) (some false)=(ns k 3151,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3151) (some false)=(ns k 3145,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3145) (some true)=(ns k 3148,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3148) (some true)=(ns k 3149,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3149) none=(ns k 3150,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2492,ns k 2493,ns k 2494,(ns_safe k 2491 (by decide) (by decide)),(ns_safe k 2492 (by decide) (by decide)),(ns_safe k 2493 (by decide) (by decide)),(ns_safe k 2494 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_2_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 3211) (ns k 1918) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2069) (ns k 2043) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,2730,2736,2733,2731][j.val]!)) (ns k 2732) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2732 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some false)=(ns k 2730,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2730) (some true)=(ns k 2736,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2736) (some false)=(ns k 2733,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2733) (some false)=(ns k 2731,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2731) none=(ns k 2732,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2044,ns k 2045,ns k 2046,(ns_safe k 2043 (by decide) (by decide)),(ns_safe k 2044 (by decide) (by decide)),(ns_safe k 2045 (by decide) (by decide)),(ns_safe k 2046 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_2_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 3211) (ns k 1918) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2069) (ns k 2043) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,2730,2736,2733,2734][j.val]!)) (ns k 2735) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 2735 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some false)=(ns k 2730,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2730) (some true)=(ns k 2736,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2736) (some false)=(ns k 2733,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2733) (some true)=(ns k 2734,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 2734) none=(ns k 2735,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2044,ns k 2045,ns k 2046,(ns_safe k 2043 (by decide) (by decide)),(ns_safe k 2044 (by decide) (by decide)),(ns_safe k 2045 (by decide) (by decide)),(ns_safe k 2046 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_2_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 3211) (ns k 3007) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 3129) (ns k 3103) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,3006,3134,3131,3101][j.val]!)) (ns k 3102) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3102 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some true)=(ns k 3006,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3006) (some true)=(ns k 3134,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3134) (some false)=(ns k 3131,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3131) (some false)=(ns k 3101,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3101) none=(ns k 3102,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 3104,ns k 3105,ns k 3106,(ns_safe k 3103 (by decide) (by decide)),(ns_safe k 3104 (by decide) (by decide)),(ns_safe k 3105 (by decide) (by decide)),(ns_safe k 3106 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_2_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 3211) (ns k 2169) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2199) (ns k 2173) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,2742,3006,3134,3131,3132][j.val]!)) (ns k 3133) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3133 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some false)=(ns k 2742,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 2742) (some true)=(ns k 3006,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3006) (some true)=(ns k 3134,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3134) (some false)=(ns k 3131,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3131) (some true)=(ns k 3132,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3132) none=(ns k 3133,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2174,ns k 2175,ns k 2176,(ns_safe k 2173 (by decide) (by decide)),(ns_safe k 2174 (by decide) (by decide)),(ns_safe k 2175 (by decide) (by decide)),(ns_safe k 2176 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_2_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 3211) (ns k 1499) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2658) (ns k 2632) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,3163,3151,3157,3154,3152][j.val]!)) (ns k 3153) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3153 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some true)=(ns k 3163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3163) (some false)=(ns k 3151,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3151) (some true)=(ns k 3157,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3157) (some false)=(ns k 3154,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3154) (some false)=(ns k 3152,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3152) none=(ns k 3153,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2633,ns k 2634,ns k 2635,(ns_safe k 2632 (by decide) (by decide)),(ns_safe k 2633 (by decide) (by decide)),(ns_safe k 2634 (by decide) (by decide)),(ns_safe k 2635 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1_2_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 3211) (ns k 1499) := by
  refine metaMk (ns k 3209) (ns k 2717) (ns k 2658) (ns k 2632) (from_1 k) (outward_1 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[2718,3163,3151,3157,3154,3155][j.val]!)) (ns k 3156) (ns_safe k 2717 (by decide) (by decide)) ?_ (ns_safe k 3156 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2717) none=(ns k 2718,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 2718) (some true)=(ns k 3163,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3163) (some false)=(ns k 3151,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3151) (some true)=(ns k 3157,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3157) (some false)=(ns k 3154,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3154) (some true)=(ns k 3155,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3155) none=(ns k 3156,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2633,ns k 2634,ns k 2635,(ns_safe k 2632 (by decide) (by decide)),(ns_safe k 2633 (by decide) (by decide)),(ns_safe k 2634 (by decide) (by decide)),(ns_safe k 2635 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
