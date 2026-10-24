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
private theorem from_2 (k : Nat) :
    FromHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3334) (ns k 3332) := by
  refine ⟨ns k 3335,ns k 3336,(ns_safe k 3334 (by decide) (by decide)),(ns_safe k 3335 (by decide) (by decide)),(ns_safe k 3336 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
  all_goals run_tac nativeRow
private theorem outward_2 (k : Nat) :
    RouteR (callerMachine k) (NativeSafe k) 0 12 (ns k 3332) (ns k 3214) := by
  run_tac nativeRoute 14
private def code_2_0_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 3334) (ns k 1514) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 1737) (ns k 1711) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3227,3221,3218,3216][j.val]!)) (ns k 3217) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3217 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some false)=(ns k 3227,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3227) (some false)=(ns k 3221,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3221) (some false)=(ns k 3218,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3218) (some false)=(ns k 3216,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3216) none=(ns k 3217,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1712,ns k 1713,ns k 1714,(ns_safe k 1711 (by decide) (by decide)),(ns_safe k 1712 (by decide) (by decide)),(ns_safe k 1713 (by decide) (by decide)),(ns_safe k 1714 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_0_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 3334) (ns k 1514) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 1737) (ns k 1711) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3227,3221,3218,3219][j.val]!)) (ns k 3220) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3220 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some false)=(ns k 3227,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3227) (some false)=(ns k 3221,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3221) (some false)=(ns k 3218,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3218) (some true)=(ns k 3219,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3219) none=(ns k 3220,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1712,ns k 1713,ns k 1714,(ns_safe k 1711 (by decide) (by decide)),(ns_safe k 1712 (by decide) (by decide)),(ns_safe k 1713 (by decide) (by decide)),(ns_safe k 1714 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_0_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 3334) (ns k 2085) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2115) (ns k 2089) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3251,3245,3242,3240][j.val]!)) (ns k 3241) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3241 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some true)=(ns k 3251,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3251) (some false)=(ns k 3245,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3245) (some false)=(ns k 3242,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3242) (some false)=(ns k 3240,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3240) none=(ns k 3241,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2090,ns k 2091,ns k 2092,(ns_safe k 2089 (by decide) (by decide)),(ns_safe k 2090 (by decide) (by decide)),(ns_safe k 2091 (by decide) (by decide)),(ns_safe k 2092 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_0_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 3334) (ns k 2085) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2115) (ns k 2089) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3251,3245,3242,3243][j.val]!)) (ns k 3244) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3244 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some true)=(ns k 3251,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3251) (some false)=(ns k 3245,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3245) (some false)=(ns k 3242,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3242) (some true)=(ns k 3243,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3243) none=(ns k 3244,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2090,ns k 2091,ns k 2092,(ns_safe k 2089 (by decide) (by decide)),(ns_safe k 2090 (by decide) (by decide)),(ns_safe k 2091 (by decide) (by decide)),(ns_safe k 2092 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_0_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 3334) (ns k 2219) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2362) (ns k 2336) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3286,3274,3268,3265,3263][j.val]!)) (ns k 3264) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3264 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some true)=(ns k 3286,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3286) (some false)=(ns k 3274,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3274) (some false)=(ns k 3268,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3268) (some false)=(ns k 3265,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3265) (some false)=(ns k 3263,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3263) none=(ns k 3264,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2337,ns k 2338,ns k 2339,(ns_safe k 2336 (by decide) (by decide)),(ns_safe k 2337 (by decide) (by decide)),(ns_safe k 2338 (by decide) (by decide)),(ns_safe k 2339 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_0_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 3334) (ns k 2219) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2362) (ns k 2336) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3286,3274,3268,3265,3266][j.val]!)) (ns k 3267) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3267 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some true)=(ns k 3286,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3286) (some false)=(ns k 3274,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3274) (some false)=(ns k 3268,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3268) (some false)=(ns k 3265,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3265) (some true)=(ns k 3266,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3266) none=(ns k 3267,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2337,ns k 2338,ns k 2339,(ns_safe k 2336 (by decide) (by decide)),(ns_safe k 2337 (by decide) (by decide)),(ns_safe k 2338 (by decide) (by decide)),(ns_safe k 2339 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_1_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 3334) (ns k 1751) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 1906) (ns k 1880) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3227,3221,3224,3222][j.val]!)) (ns k 3223) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3223 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some false)=(ns k 3227,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3227) (some false)=(ns k 3221,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3221) (some true)=(ns k 3224,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3224) (some false)=(ns k 3222,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3222) none=(ns k 3223,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1881,ns k 1882,ns k 1883,(ns_safe k 1880 (by decide) (by decide)),(ns_safe k 1881 (by decide) (by decide)),(ns_safe k 1882 (by decide) (by decide)),(ns_safe k 1883 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_1_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 3334) (ns k 1751) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 1906) (ns k 1880) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3227,3221,3224,3225][j.val]!)) (ns k 3226) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3226 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some false)=(ns k 3227,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3227) (some false)=(ns k 3221,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3221) (some true)=(ns k 3224,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3224) (some true)=(ns k 3225,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3225) none=(ns k 3226,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1881,ns k 1882,ns k 1883,(ns_safe k 1880 (by decide) (by decide)),(ns_safe k 1881 (by decide) (by decide)),(ns_safe k 1882 (by decide) (by decide)),(ns_safe k 1883 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_1_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 3334) (ns k 2128) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2158) (ns k 2132) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3251,3245,3248,3246][j.val]!)) (ns k 3247) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3247 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some true)=(ns k 3251,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3251) (some false)=(ns k 3245,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3245) (some true)=(ns k 3248,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3248) (some false)=(ns k 3246,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3246) none=(ns k 3247,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2133,ns k 2134,ns k 2135,(ns_safe k 2132 (by decide) (by decide)),(ns_safe k 2133 (by decide) (by decide)),(ns_safe k 2134 (by decide) (by decide)),(ns_safe k 2135 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_1_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 3334) (ns k 2128) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2158) (ns k 2132) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3251,3245,3248,3249][j.val]!)) (ns k 3250) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3250 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some true)=(ns k 3251,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3251) (some false)=(ns k 3245,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3245) (some true)=(ns k 3248,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3248) (some true)=(ns k 3249,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3249) none=(ns k 3250,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2133,ns k 2134,ns k 2135,(ns_safe k 2132 (by decide) (by decide)),(ns_safe k 2133 (by decide) (by decide)),(ns_safe k 2134 (by decide) (by decide)),(ns_safe k 2135 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_1_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 3334) (ns k 2374) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2517) (ns k 2491) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3286,3274,3268,3271,3269][j.val]!)) (ns k 3270) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3270 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some true)=(ns k 3286,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3286) (some false)=(ns k 3274,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3274) (some false)=(ns k 3268,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3268) (some true)=(ns k 3271,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3271) (some false)=(ns k 3269,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3269) none=(ns k 3270,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2492,ns k 2493,ns k 2494,(ns_safe k 2491 (by decide) (by decide)),(ns_safe k 2492 (by decide) (by decide)),(ns_safe k 2493 (by decide) (by decide)),(ns_safe k 2494 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_1_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 3334) (ns k 2374) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2517) (ns k 2491) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3286,3274,3268,3271,3272][j.val]!)) (ns k 3273) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3273 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some true)=(ns k 3286,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3286) (some false)=(ns k 3274,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3274) (some false)=(ns k 3268,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3268) (some true)=(ns k 3271,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3271) (some true)=(ns k 3272,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3272) none=(ns k 3273,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2492,ns k 2493,ns k 2494,(ns_safe k 2491 (by decide) (by decide)),(ns_safe k 2492 (by decide) (by decide)),(ns_safe k 2493 (by decide) (by decide)),(ns_safe k 2494 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_2_0_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 3334) (ns k 1918) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2069) (ns k 2043) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3227,3233,3230,3228][j.val]!)) (ns k 3229) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3229 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some false)=(ns k 3227,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3227) (some true)=(ns k 3233,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3233) (some false)=(ns k 3230,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3230) (some false)=(ns k 3228,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3228) none=(ns k 3229,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2044,ns k 2045,ns k 2046,(ns_safe k 2043 (by decide) (by decide)),(ns_safe k 2044 (by decide) (by decide)),(ns_safe k 2045 (by decide) (by decide)),(ns_safe k 2046 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_2_0_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 3334) (ns k 1918) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2069) (ns k 2043) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3227,3233,3230,3231][j.val]!)) (ns k 3232) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3232 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some false)=(ns k 3227,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3227) (some true)=(ns k 3233,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3233) (some false)=(ns k 3230,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3230) (some true)=(ns k 3231,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3231) none=(ns k 3232,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2044,ns k 2045,ns k 2046,(ns_safe k 2043 (by decide) (by decide)),(ns_safe k 2044 (by decide) (by decide)),(ns_safe k 2045 (by decide) (by decide)),(ns_safe k 2046 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_2_1_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 3334) (ns k 2169) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2199) (ns k 2173) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3251,3257,3254,3252][j.val]!)) (ns k 3253) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3253 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some true)=(ns k 3251,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3251) (some true)=(ns k 3257,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3257) (some false)=(ns k 3254,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3254) (some false)=(ns k 3252,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3252) none=(ns k 3253,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2174,ns k 2175,ns k 2176,(ns_safe k 2173 (by decide) (by decide)),(ns_safe k 2174 (by decide) (by decide)),(ns_safe k 2175 (by decide) (by decide)),(ns_safe k 2176 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_2_1_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 3334) (ns k 2169) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2199) (ns k 2173) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3239,3251,3257,3254,3255][j.val]!)) (ns k 3256) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3256 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some false)=(ns k 3239,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3239) (some true)=(ns k 3251,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3251) (some true)=(ns k 3257,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3257) (some false)=(ns k 3254,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3254) (some true)=(ns k 3255,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3255) none=(ns k 3256,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2174,ns k 2175,ns k 2176,(ns_safe k 2173 (by decide) (by decide)),(ns_safe k 2174 (by decide) (by decide)),(ns_safe k 2175 (by decide) (by decide)),(ns_safe k 2176 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_2_2_0 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 3334) (ns k 1499) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2658) (ns k 2632) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3286,3274,3280,3277,3275][j.val]!)) (ns k 3276) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3276 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some true)=(ns k 3286,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3286) (some false)=(ns k 3274,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3274) (some true)=(ns k 3280,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3280) (some false)=(ns k 3277,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3277) (some false)=(ns k 3275,some false,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3275) none=(ns k 3276,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2633,ns k 2634,ns k 2635,(ns_safe k 2632 (by decide) (by decide)),(ns_safe k 2633 (by decide) (by decide)),(ns_safe k 2634 (by decide) (by decide)),(ns_safe k 2635 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2_2_2_1 (k : Nat) :
    MetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 3334) (ns k 1499) := by
  refine metaMk (ns k 3332) (ns k 3214) (ns k 2658) (ns k 2632) (from_2 k) (outward_2 k) ?_ ?_ ?_
  · refine bitsMk (fun j:Fin 6=>ns k (#[3215,3286,3274,3280,3277,3278][j.val]!)) (ns k 3279) (ns_safe k 3214 (by decide) (by decide)) ?_ (ns_safe k 3279 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3214) none=(ns k 3215,none,.right)
      run_tac nativeRow
    · intro j
      fin_cases j
      · change (callerMachine k).step (ns k 3215) (some true)=(ns k 3286,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3286) (some false)=(ns k 3274,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3274) (some true)=(ns k 3280,some true,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3280) (some false)=(ns k 3277,some false,.right)
        run_tac nativeRow
      · change (callerMachine k).step (ns k 3277) (some true)=(ns k 3278,some true,.right)
        run_tac nativeRow
    · change (callerMachine k).step (ns k 3278) none=(ns k 3279,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2633,ns k 2634,ns k 2635,(ns_safe k 2632 (by decide) (by decide)),(ns_safe k 2633 (by decide) (by decide)),(ns_safe k 2634 (by decide) (by decide)),(ns_safe k 2635 (by decide) (by decide)),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
