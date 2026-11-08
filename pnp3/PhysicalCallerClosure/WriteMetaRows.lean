import PhysicalCallerClosure.WriteMeta
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
  for (owner,leaves) in [(`PhysicalCallerClosure.WriteBits,["WriteRows"]),
      (`PhysicalCallerClosure.WriteMeta,["WriteMetaRows"]),(`PhysicalCallerClosure.Navigation,["ToHRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing exact writer type {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong writer owner"
      logInfo m!"writer-rows-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def ctor (owner : Name) (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf) "mk"
  let some (.ctorInfo ci):=e.find? n | throwError "Missing exact writer constructor {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong constructor owner"
  logInfo m!"writer-rows-constructor|{n}|{ci.type}"
  closeMainGoal `ctor (mkConst n (ci.levelParams.map Level.param))
private abbrev writeMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {bits : Fin 5 → Bool} →
    {entry out : Fin M.stateCount} → (states : Fin 6 → Fin M.stateCount) → (back : Fin M.stateCount) →
    Safe entry → (∀ j,Safe (states j)) → Safe back →
    M.step entry none=(states ⟨0,by decide⟩,none,.right) →
    (∀ (j:Fin 5) b,M.step (states (Fin.castSucc j)) b=(states (Fin.succ j),some (bits j),.right)) →
    M.step (states ⟨5,by decide⟩) none=(back,none,.left) →
    (∀ b,M.step back (some b)=(back,some b,.left)) → M.step back none=(out,none,.stay) →
    WriteRows (Safe:=Safe) bits entry out := by run_tac ctor `PhysicalCallerClosure.WriteBits "WriteRows"
private abbrev metaMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} → {bits : Fin 5 → Bool} →
    {entry out : Fin M.stateCount} → (first fieldEntry returnEntry homeEntry : Fin M.stateCount) →
    FromHRows (Safe:=Safe) entry first → RouteR M Safe 0 12 first fieldEntry →
    WriteRows (Safe:=Safe) bits fieldEntry returnEntry → RouteL M Safe 12 0 returnEntry homeEntry →
    ToHRows (Safe:=Safe) homeEntry out → WriteMetaRows (Safe:=Safe) bits entry out := by
  run_tac ctor `PhysicalCallerClosure.WriteMeta "WriteMetaRows"
section LiteralRows
set_option maxRecDepth 4000
private def code_343 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 399) (ns k 336) := by
  refine metaMk (ns k 397) (ns k 343) (ns k 373) (ns k 339) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 400,ns k 401,ns_safe k 399 (by decide) (by decide),ns_safe k 400 (by decide) (by decide),ns_safe k 401 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[344,345,346,347,348,349][j.val]!)) (ns k 350) (ns_safe k 343 (by decide) (by decide)) ?_ (ns_safe k 350 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 343) none=(ns k 344,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 344) b=(ns k 345,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 345) b=(ns k 346,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 346) b=(ns k 347,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 347) b=(ns k 348,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 348) b=(ns k 349,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 349) none=(ns k 350,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 340,ns k 341,ns k 342,ns_safe k 339 (by decide) (by decide),ns_safe k 340 (by decide) (by decide),ns_safe k 341 (by decide) (by decide),ns_safe k 342 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_408 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 440) (ns k 336) := by
  refine metaMk (ns k 438) (ns k 408) (ns k 373) (ns k 339) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 441,ns k 442,ns_safe k 440 (by decide) (by decide),ns_safe k 441 (by decide) (by decide),ns_safe k 442 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[409,410,411,412,413,414][j.val]!)) (ns k 415) (ns_safe k 408 (by decide) (by decide)) ?_ (ns_safe k 415 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 408) none=(ns k 409,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 409) b=(ns k 410,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 410) b=(ns k 411,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 411) b=(ns k 412,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 412) b=(ns k 413,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 413) b=(ns k 414,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 414) none=(ns k 415,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 340,ns k 341,ns k 342,ns_safe k 339 (by decide) (by decide),ns_safe k 340 (by decide) (by decide),ns_safe k 341 (by decide) (by decide),ns_safe k 342 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_449 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 481) (ns k 336) := by
  refine metaMk (ns k 479) (ns k 449) (ns k 373) (ns k 339) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 482,ns k 483,ns_safe k 481 (by decide) (by decide),ns_safe k 482 (by decide) (by decide),ns_safe k 483 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[450,451,452,453,454,455][j.val]!)) (ns k 456) (ns_safe k 449 (by decide) (by decide)) ?_ (ns_safe k 456 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 449) none=(ns k 450,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 450) b=(ns k 451,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 451) b=(ns k 452,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 452) b=(ns k 453,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 453) b=(ns k 454,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 454) b=(ns k 455,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 455) none=(ns k 456,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 340,ns k 341,ns k 342,ns_safe k 339 (by decide) (by decide),ns_safe k 340 (by decide) (by decide),ns_safe k 341 (by decide) (by decide),ns_safe k 342 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_812 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 868) (ns k 805) := by
  refine metaMk (ns k 866) (ns k 812) (ns k 842) (ns k 808) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 869,ns k 870,ns_safe k 868 (by decide) (by decide),ns_safe k 869 (by decide) (by decide),ns_safe k 870 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[813,814,815,816,817,818][j.val]!)) (ns k 819) (ns_safe k 812 (by decide) (by decide)) ?_ (ns_safe k 819 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 812) none=(ns k 813,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 813) b=(ns k 814,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 814) b=(ns k 815,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 815) b=(ns k 816,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 816) b=(ns k 817,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 817) b=(ns k 818,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 818) none=(ns k 819,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 809,ns k 810,ns k 811,ns_safe k 808 (by decide) (by decide),ns_safe k 809 (by decide) (by decide),ns_safe k 810 (by decide) (by decide),ns_safe k 811 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_877 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 909) (ns k 805) := by
  refine metaMk (ns k 907) (ns k 877) (ns k 842) (ns k 808) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 910,ns k 911,ns_safe k 909 (by decide) (by decide),ns_safe k 910 (by decide) (by decide),ns_safe k 911 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[878,879,880,881,882,883][j.val]!)) (ns k 884) (ns_safe k 877 (by decide) (by decide)) ?_ (ns_safe k 884 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 877) none=(ns k 878,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 878) b=(ns k 879,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 879) b=(ns k 880,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 880) b=(ns k 881,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 881) b=(ns k 882,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 882) b=(ns k 883,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 883) none=(ns k 884,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 809,ns k 810,ns k 811,ns_safe k 808 (by decide) (by decide),ns_safe k 809 (by decide) (by decide),ns_safe k 810 (by decide) (by decide),ns_safe k 811 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_918 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 950) (ns k 805) := by
  refine metaMk (ns k 948) (ns k 918) (ns k 842) (ns k 808) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 951,ns k 952,ns_safe k 950 (by decide) (by decide),ns_safe k 951 (by decide) (by decide),ns_safe k 952 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[919,920,921,922,923,924][j.val]!)) (ns k 925) (ns_safe k 918 (by decide) (by decide)) ?_ (ns_safe k 925 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 918) none=(ns k 919,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 919) b=(ns k 920,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 920) b=(ns k 921,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 921) b=(ns k 922,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 922) b=(ns k 923,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 923) b=(ns k 924,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 924) none=(ns k 925,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 809,ns k 810,ns k 811,ns_safe k 808 (by decide) (by decide),ns_safe k 809 (by decide) (by decide),ns_safe k 810 (by decide) (by decide),ns_safe k 811 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1289 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 1345) (ns k 1282) := by
  refine metaMk (ns k 1343) (ns k 1289) (ns k 1319) (ns k 1285) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 1346,ns k 1347,ns_safe k 1345 (by decide) (by decide),ns_safe k 1346 (by decide) (by decide),ns_safe k 1347 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1290,1291,1292,1293,1294,1295][j.val]!)) (ns k 1296) (ns_safe k 1289 (by decide) (by decide)) ?_ (ns_safe k 1296 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1289) none=(ns k 1290,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1290) b=(ns k 1291,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1291) b=(ns k 1292,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1292) b=(ns k 1293,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1293) b=(ns k 1294,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1294) b=(ns k 1295,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1295) none=(ns k 1296,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1286,ns k 1287,ns k 1288,ns_safe k 1285 (by decide) (by decide),ns_safe k 1286 (by decide) (by decide),ns_safe k 1287 (by decide) (by decide),ns_safe k 1288 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1353 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 1385) (ns k 1282) := by
  refine metaMk (ns k 1383) (ns k 1353) (ns k 1319) (ns k 1285) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 1386,ns k 1387,ns_safe k 1385 (by decide) (by decide),ns_safe k 1386 (by decide) (by decide),ns_safe k 1387 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1354,1355,1356,1357,1358,1359][j.val]!)) (ns k 1360) (ns_safe k 1353 (by decide) (by decide)) ?_ (ns_safe k 1360 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1353) none=(ns k 1354,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1354) b=(ns k 1355,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1355) b=(ns k 1356,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1356) b=(ns k 1357,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1357) b=(ns k 1358,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1358) b=(ns k 1359,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1359) none=(ns k 1360,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1286,ns k 1287,ns k 1288,ns_safe k 1285 (by decide) (by decide),ns_safe k 1286 (by decide) (by decide),ns_safe k 1287 (by decide) (by decide),ns_safe k 1288 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1393 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 1425) (ns k 1282) := by
  refine metaMk (ns k 1423) (ns k 1393) (ns k 1319) (ns k 1285) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 1426,ns k 1427,ns_safe k 1425 (by decide) (by decide),ns_safe k 1426 (by decide) (by decide),ns_safe k 1427 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1394,1395,1396,1397,1398,1399][j.val]!)) (ns k 1400) (ns_safe k 1393 (by decide) (by decide)) ?_ (ns_safe k 1400 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1393) none=(ns k 1394,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1394) b=(ns k 1395,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1395) b=(ns k 1396,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1396) b=(ns k 1397,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1397) b=(ns k 1398,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1398) b=(ns k 1399,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1399) none=(ns k 1400,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1286,ns k 1287,ns k 1288,ns_safe k 1285 (by decide) (by decide),ns_safe k 1286 (by decide) (by decide),ns_safe k 1287 (by decide) (by decide),ns_safe k 1288 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1443 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 1499) ((callerMachine k).reject) := by
  refine metaMk (ns k 1497) (ns k 1443) (ns k 1473) (ns k 1439) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 1500,ns k 1501,ns_safe k 1499 (by decide) (by decide),ns_safe k 1500 (by decide) (by decide),ns_safe k 1501 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1444,1445,1446,1447,1448,1449][j.val]!)) (ns k 1450) (ns_safe k 1443 (by decide) (by decide)) ?_ (ns_safe k 1450 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1443) none=(ns k 1444,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1444) b=(ns k 1445,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1445) b=(ns k 1446,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1446) b=(ns k 1447,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1447) b=(ns k 1448,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1448) b=(ns k 1449,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1449) none=(ns k 1450,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1440,ns k 1441,ns k 1442,ns_safe k 1439 (by decide) (by decide),ns_safe k 1440 (by decide) (by decide),ns_safe k 1441 (by decide) (by decide),ns_safe k 1442 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1533 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 1589) (ns k 1432) := by
  refine metaMk (ns k 1587) (ns k 1533) (ns k 1563) (ns k 1529) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 1590,ns k 1591,ns_safe k 1589 (by decide) (by decide),ns_safe k 1590 (by decide) (by decide),ns_safe k 1591 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1534,1535,1536,1537,1538,1539][j.val]!)) (ns k 1540) (ns_safe k 1533 (by decide) (by decide)) ?_ (ns_safe k 1540 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1533) none=(ns k 1534,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1534) b=(ns k 1535,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1535) b=(ns k 1536,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1536) b=(ns k 1537,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1537) b=(ns k 1538,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1538) b=(ns k 1539,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1539) none=(ns k 1540,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1530,ns k 1531,ns k 1532,ns_safe k 1529 (by decide) (by decide),ns_safe k 1530 (by decide) (by decide),ns_safe k 1531 (by decide) (by decide),ns_safe k 1532 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1619 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 1675) (ns k 1611) := by
  refine metaMk (ns k 1673) (ns k 1619) (ns k 1649) (ns k 1615) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 1676,ns k 1677,ns_safe k 1675 (by decide) (by decide),ns_safe k 1676 (by decide) (by decide),ns_safe k 1677 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1620,1621,1622,1623,1624,1625][j.val]!)) (ns k 1626) (ns_safe k 1619 (by decide) (by decide)) ?_ (ns_safe k 1626 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1619) none=(ns k 1620,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1620) b=(ns k 1621,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1621) b=(ns k 1622,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1622) b=(ns k 1623,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1623) b=(ns k 1624,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1624) b=(ns k 1625,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1625) none=(ns k 1626,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1616,ns k 1617,ns k 1618,ns_safe k 1615 (by decide) (by decide),ns_safe k 1616 (by decide) (by decide),ns_safe k 1617 (by decide) (by decide),ns_safe k 1618 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1788 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 1844) (ns k 1780) := by
  refine metaMk (ns k 1842) (ns k 1788) (ns k 1818) (ns k 1784) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 1845,ns k 1846,ns_safe k 1844 (by decide) (by decide),ns_safe k 1845 (by decide) (by decide),ns_safe k 1846 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1789,1790,1791,1792,1793,1794][j.val]!)) (ns k 1795) (ns_safe k 1788 (by decide) (by decide)) ?_ (ns_safe k 1795 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1788) none=(ns k 1789,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1789) b=(ns k 1790,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1790) b=(ns k 1791,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1791) b=(ns k 1792,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1792) b=(ns k 1793,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1793) b=(ns k 1794,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1794) none=(ns k 1795,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1785,ns k 1786,ns k 1787,ns_safe k 1784 (by decide) (by decide),ns_safe k 1785 (by decide) (by decide),ns_safe k 1786 (by decide) (by decide),ns_safe k 1787 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_1951 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 2007) (ns k 1943) := by
  refine metaMk (ns k 2005) (ns k 1951) (ns k 1981) (ns k 1947) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 2008,ns k 2009,ns_safe k 2007 (by decide) (by decide),ns_safe k 2008 (by decide) (by decide),ns_safe k 2009 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[1952,1953,1954,1955,1956,1957][j.val]!)) (ns k 1958) (ns_safe k 1951 (by decide) (by decide)) ?_ (ns_safe k 1958 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 1951) none=(ns k 1952,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 1952) b=(ns k 1953,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1953) b=(ns k 1954,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1954) b=(ns k 1955,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1955) b=(ns k 1956,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 1956) b=(ns k 1957,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 1957) none=(ns k 1958,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 1948,ns k 1949,ns k 1950,ns_safe k 1947 (by decide) (by decide),ns_safe k 1948 (by decide) (by decide),ns_safe k 1949 (by decide) (by decide),ns_safe k 1950 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2244 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 2300) (ns k 2236) := by
  refine metaMk (ns k 2298) (ns k 2244) (ns k 2274) (ns k 2240) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 2301,ns k 2302,ns_safe k 2300 (by decide) (by decide),ns_safe k 2301 (by decide) (by decide),ns_safe k 2302 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[2245,2246,2247,2248,2249,2250][j.val]!)) (ns k 2251) (ns_safe k 2244 (by decide) (by decide)) ?_ (ns_safe k 2251 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2244) none=(ns k 2245,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 2245) b=(ns k 2246,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2246) b=(ns k 2247,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2247) b=(ns k 2248,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2248) b=(ns k 2249,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2249) b=(ns k 2250,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 2250) none=(ns k 2251,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2241,ns k 2242,ns k 2243,ns_safe k 2240 (by decide) (by decide),ns_safe k 2241 (by decide) (by decide),ns_safe k 2242 (by decide) (by decide),ns_safe k 2243 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2399 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 2455) (ns k 2391) := by
  refine metaMk (ns k 2453) (ns k 2399) (ns k 2429) (ns k 2395) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 2456,ns k 2457,ns_safe k 2455 (by decide) (by decide),ns_safe k 2456 (by decide) (by decide),ns_safe k 2457 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[2400,2401,2402,2403,2404,2405][j.val]!)) (ns k 2406) (ns_safe k 2399 (by decide) (by decide)) ?_ (ns_safe k 2406 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2399) none=(ns k 2400,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 2400) b=(ns k 2401,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2401) b=(ns k 2402,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2402) b=(ns k 2403,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2403) b=(ns k 2404,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2404) b=(ns k 2405,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 2405) none=(ns k 2406,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2396,ns k 2397,ns k 2398,ns_safe k 2395 (by decide) (by decide),ns_safe k 2396 (by decide) (by decide),ns_safe k 2397 (by decide) (by decide),ns_safe k 2398 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2540 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 2596) (ns k 2532) := by
  refine metaMk (ns k 2594) (ns k 2540) (ns k 2570) (ns k 2536) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 2597,ns k 2598,ns_safe k 2596 (by decide) (by decide),ns_safe k 2597 (by decide) (by decide),ns_safe k 2598 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[2541,2542,2543,2544,2545,2546][j.val]!)) (ns k 2547) (ns_safe k 2540 (by decide) (by decide)) ?_ (ns_safe k 2547 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2540) none=(ns k 2541,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 2541) b=(ns k 2542,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2542) b=(ns k 2543,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2543) b=(ns k 2544,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2544) b=(ns k 2545,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2545) b=(ns k 2546,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 2546) none=(ns k 2547,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2537,ns k 2538,ns k 2539,ns_safe k 2536 (by decide) (by decide),ns_safe k 2537 (by decide) (by decide),ns_safe k 2538 (by decide) (by decide),ns_safe k 2539 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2782 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 2838) (ns k 2774) := by
  refine metaMk (ns k 2836) (ns k 2782) (ns k 2812) (ns k 2778) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 2839,ns k 2840,ns_safe k 2838 (by decide) (by decide),ns_safe k 2839 (by decide) (by decide),ns_safe k 2840 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[2783,2784,2785,2786,2787,2788][j.val]!)) (ns k 2789) (ns_safe k 2782 (by decide) (by decide)) ?_ (ns_safe k 2789 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2782) none=(ns k 2783,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 2783) b=(ns k 2784,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2784) b=(ns k 2785,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2785) b=(ns k 2786,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2786) b=(ns k 2787,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2787) b=(ns k 2788,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 2788) none=(ns k 2789,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2779,ns k 2780,ns k 2781,ns_safe k 2778 (by decide) (by decide),ns_safe k 2779 (by decide) (by decide),ns_safe k 2780 (by decide) (by decide),ns_safe k 2781 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_2914 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 2970) (ns k 2906) := by
  refine metaMk (ns k 2968) (ns k 2914) (ns k 2944) (ns k 2910) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 2971,ns k 2972,ns_safe k 2970 (by decide) (by decide),ns_safe k 2971 (by decide) (by decide),ns_safe k 2972 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[2915,2916,2917,2918,2919,2920][j.val]!)) (ns k 2921) (ns_safe k 2914 (by decide) (by decide)) ?_ (ns_safe k 2921 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 2914) none=(ns k 2915,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 2915) b=(ns k 2916,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2916) b=(ns k 2917,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2917) b=(ns k 2918,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2918) b=(ns k 2919,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 2919) b=(ns k 2920,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 2920) none=(ns k 2921,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 2911,ns k 2912,ns k 2913,ns_safe k 2910 (by decide) (by decide),ns_safe k 2911 (by decide) (by decide),ns_safe k 2912 (by decide) (by decide),ns_safe k 2913 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
private def code_3042 (k : Nat) :
    WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 3098) (ns k 3034) := by
  refine metaMk (ns k 3096) (ns k 3042) (ns k 3072) (ns k 3038) ?_ ?_ ?_ ?_ ?_
  · refine ⟨ns k 3099,ns k 3100,ns_safe k 3098 (by decide) (by decide),ns_safe k 3099 (by decide) (by decide),ns_safe k 3100 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
  · run_tac nativeRoute 14
  · refine writeMk (fun j:Fin 6=>ns k (#[3043,3044,3045,3046,3047,3048][j.val]!)) (ns k 3049) (ns_safe k 3042 (by decide) (by decide)) ?_ (ns_safe k 3049 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_
    · intro j;fin_cases j <;> exact ns_safe k _ (by decide) (by decide)
    · change (callerMachine k).step (ns k 3042) none=(ns k 3043,none,.right)
      run_tac nativeRow
    · intro j b
      fin_cases j
      · change (callerMachine k).step (ns k 3043) b=(ns k 3044,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 3044) b=(ns k 3045,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 3045) b=(ns k 3046,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 3046) b=(ns k 3047,some false,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
      · change (callerMachine k).step (ns k 3047) b=(ns k 3048,some true,.right)
        cases b with
        | none => run_tac nativeRow
        | some b => cases b <;> run_tac nativeRow
    · change (callerMachine k).step (ns k 3048) none=(ns k 3049,none,.left)
      run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
    · run_tac nativeRow
  · run_tac nativeRoute 14
  · refine ⟨ns k 3039,ns k 3040,ns k 3041,ns_safe k 3038 (by decide) (by decide),ns_safe k 3039 (by decide) (by decide),ns_safe k 3040 (by decide) (by decide),ns_safe k 3041 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
    all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
