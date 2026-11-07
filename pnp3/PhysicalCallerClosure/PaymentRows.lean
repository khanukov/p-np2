import PhysicalCallerClosure.Payment
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
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Payment 0) "PhysicalCallerClosure") "PayRows"
  let some (.inductInfo ci):=e.find? n | throwError "Missing exact PayRows type"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Payment do throwError "Wrong payment owner"
  logInfo m!"payment-rows-type|{n}|{ci.type}"
  modifyScope fun st=>{st with openDecls:=.explicit `PayRows n::st.openDecls}
private abbrev payMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} →
    {entry normal last : Fin M.stateCount} → (scan back peek erase ret single home : Fin M.stateCount) →
    Safe entry → Safe scan → Safe back → Safe peek → Safe erase → Safe ret → Safe single → Safe home →
    M.step entry none=(scan,none,.right) → M.step scan (some true)=(scan,some true,.right) →
    (∀ b,b≠some true → M.step scan b=(back,b,.left)) →
    M.step back (some true)=(peek,some true,.left) → M.step peek (some true)=(erase,some true,.right) →
    M.step peek none=(single,none,.right) → M.step erase (some true)=(ret,none,.left) →
    M.step ret (some true)=(ret,some true,.left) → M.step ret none=(normal,none,.stay) →
    M.step single (some true)=(home,some true,.left) → M.step home none=(last,none,.stay) →
    PayRows (Safe:=Safe) entry normal last := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Payment 0) "PhysicalCallerClosure") "PayRows") "mk"
    let some (.ctorInfo ci):=e.find? n | throwError "Missing exact payment constructor"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Payment do throwError "Wrong payment constructor owner"
    logInfo m!"payment-rows-constructor|{n}|{ci.type}"
    closeMainGoal `payMk (mkConst n (ci.levelParams.map Level.param))
section LiteralRows
set_option maxRecDepth 4000
private def code_0_0 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1435) (ns k 1606) (ns k 1675) := by
  refine payMk (ns k 1436) (ns k 1437) (ns k 1438) (ns k 1516) (ns k 1518) (ns k 1517) (ns k 1610)
    (ns_safe k 1435 (by decide) (by decide)) (ns_safe k 1436 (by decide) (by decide)) (ns_safe k 1437 (by decide) (by decide)) (ns_safe k 1438 (by decide) (by decide)) (ns_safe k 1516 (by decide) (by decide)) (ns_safe k 1518 (by decide) (by decide)) (ns_safe k 1517 (by decide) (by decide)) (ns_safe k 1610 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_0_1 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2743) (ns k 2769) (ns k 2838) := by
  refine payMk (ns k 2744) (ns k 2745) (ns k 2746) (ns k 2747) (ns k 2749) (ns k 2748) (ns k 2773)
    (ns_safe k 2743 (by decide) (by decide)) (ns_safe k 2744 (by decide) (by decide)) (ns_safe k 2745 (by decide) (by decide)) (ns_safe k 2746 (by decide) (by decide)) (ns_safe k 2747 (by decide) (by decide)) (ns_safe k 2749 (by decide) (by decide)) (ns_safe k 2748 (by decide) (by decide)) (ns_safe k 2773 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_0_2 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2210) (ns k 2231) (ns k 2300) := by
  refine payMk (ns k 2211) (ns k 2212) (ns k 2213) (ns k 2221) (ns k 2223) (ns k 2222) (ns k 2235)
    (ns_safe k 2210 (by decide) (by decide)) (ns_safe k 2211 (by decide) (by decide)) (ns_safe k 2212 (by decide) (by decide)) (ns_safe k 2213 (by decide) (by decide)) (ns_safe k 2221 (by decide) (by decide)) (ns_safe k 2223 (by decide) (by decide)) (ns_safe k 2222 (by decide) (by decide)) (ns_safe k 2235 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_1_0 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1740) (ns k 1775) (ns k 1844) := by
  refine payMk (ns k 1741) (ns k 1742) (ns k 1743) (ns k 1753) (ns k 1755) (ns k 1754) (ns k 1779)
    (ns_safe k 1740 (by decide) (by decide)) (ns_safe k 1741 (by decide) (by decide)) (ns_safe k 1742 (by decide) (by decide)) (ns_safe k 1743 (by decide) (by decide)) (ns_safe k 1753 (by decide) (by decide)) (ns_safe k 1755 (by decide) (by decide)) (ns_safe k 1754 (by decide) (by decide)) (ns_safe k 1779 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_1_1 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2875) (ns k 2901) (ns k 2970) := by
  refine payMk (ns k 2876) (ns k 2877) (ns k 2878) (ns k 2879) (ns k 2881) (ns k 2880) (ns k 2905)
    (ns_safe k 2875 (by decide) (by decide)) (ns_safe k 2876 (by decide) (by decide)) (ns_safe k 2877 (by decide) (by decide)) (ns_safe k 2878 (by decide) (by decide)) (ns_safe k 2879 (by decide) (by decide)) (ns_safe k 2881 (by decide) (by decide)) (ns_safe k 2880 (by decide) (by decide)) (ns_safe k 2905 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_1_2 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2365) (ns k 2386) (ns k 2455) := by
  refine payMk (ns k 2366) (ns k 2367) (ns k 2368) (ns k 2376) (ns k 2378) (ns k 2377) (ns k 2390)
    (ns_safe k 2365 (by decide) (by decide)) (ns_safe k 2366 (by decide) (by decide)) (ns_safe k 2367 (by decide) (by decide)) (ns_safe k 2368 (by decide) (by decide)) (ns_safe k 2376 (by decide) (by decide)) (ns_safe k 2378 (by decide) (by decide)) (ns_safe k 2377 (by decide) (by decide)) (ns_safe k 2390 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_2_0 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1909) (ns k 1938) (ns k 2007) := by
  refine payMk (ns k 1910) (ns k 1911) (ns k 1912) (ns k 1920) (ns k 1922) (ns k 1921) (ns k 1942)
    (ns_safe k 1909 (by decide) (by decide)) (ns_safe k 1910 (by decide) (by decide)) (ns_safe k 1911 (by decide) (by decide)) (ns_safe k 1912 (by decide) (by decide)) (ns_safe k 1920 (by decide) (by decide)) (ns_safe k 1922 (by decide) (by decide)) (ns_safe k 1921 (by decide) (by decide)) (ns_safe k 1942 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_2_1 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3007) (ns k 3029) (ns k 3098) := by
  refine payMk (ns k 3008) (ns k 3009) (ns k 3010) (ns k 3011) (ns k 3013) (ns k 3012) (ns k 3033)
    (ns_safe k 3007 (by decide) (by decide)) (ns_safe k 3008 (by decide) (by decide)) (ns_safe k 3009 (by decide) (by decide)) (ns_safe k 3010 (by decide) (by decide)) (ns_safe k 3011 (by decide) (by decide)) (ns_safe k 3013 (by decide) (by decide)) (ns_safe k 3012 (by decide) (by decide)) (ns_safe k 3033 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
private def code_2_2 (k : Nat) :
    PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2520) (ns k 2527) (ns k 2596) := by
  refine payMk (ns k 2521) (ns k 2522) (ns k 2523) (ns k 2524) (ns k 2526) (ns k 2525) (ns k 2531)
    (ns_safe k 2520 (by decide) (by decide)) (ns_safe k 2521 (by decide) (by decide)) (ns_safe k 2522 (by decide) (by decide)) (ns_safe k 2523 (by decide) (by decide)) (ns_safe k 2524 (by decide) (by decide)) (ns_safe k 2526 (by decide) (by decide)) (ns_safe k 2525 (by decide) (by decide)) (ns_safe k 2531 (by decide) (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b hb
    cases b with
    | none => run_tac nativeRow
    | some b => cases b with
      | false => run_tac nativeRow
      | true => exact (hb rfl).elim
  all_goals run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
