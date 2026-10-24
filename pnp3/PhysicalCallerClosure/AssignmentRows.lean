import PhysicalCallerClosure.Assignment
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
  for leaf in ["CarryRows","IncrementRows"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Assignment 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact counter certificate type {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Assignment do throwError "Wrong counter certificate owner"
    logInfo m!"assignment-rows-type|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev incMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} →
    {entry normal overflow : Fin M.stateCount} → (carry back over : Fin M.stateCount) →
    Safe entry → Safe back → Safe over → CarryRows (Safe:=Safe) carry back →
    M.step entry none=(carry,none,.left) → M.step carry none=(over,none,.right) →
    M.step back none=(normal,none,.stay) → (∀ x,M.step over (some x)=(over,some x,.right)) →
    M.step over none=(overflow,none,.stay) → IncrementRows (Safe:=Safe) entry normal overflow := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Assignment 0) "PhysicalCallerClosure") "IncrementRows") "mk"
    let some (.ctorInfo ci):=e.find? n | throwError "Missing exact IncrementRows constructor"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Assignment do throwError "Wrong constructor owner"
    logInfo m!"assignment-rows-constructor|{n}|{ci.type}"
    closeMainGoal `incMk (mkConst n (ci.levelParams.map Level.param))
section LiteralRows
set_option maxRecDepth 4000
private def code_1606 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1606) (ns k 1527) (ns k 1604) := by
  refine incMk (ns k 1607) (ns k 1608) (ns k 1609) (ns_safe k 1606 (by decide) (by decide)) (ns_safe k 1608 (by decide) (by decide)) (ns_safe k 1609 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 1607 (by decide) (by decide)),(ns_safe k 1608 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1611 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1611) (ns k 1514) (ns k 1604) := by
  refine incMk (ns k 1612) (ns k 1613) (ns k 1614) (ns_safe k 1611 (by decide) (by decide)) (ns_safe k 1613 (by decide) (by decide)) (ns_safe k 1614 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 1612 (by decide) (by decide)),(ns_safe k 1613 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1775 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1775) (ns k 1764) (ns k 1773) := by
  refine incMk (ns k 1776) (ns k 1777) (ns k 1778) (ns_safe k 1775 (by decide) (by decide)) (ns_safe k 1777 (by decide) (by decide)) (ns_safe k 1778 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 1776 (by decide) (by decide)),(ns_safe k 1777 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1780 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1780) (ns k 1751) (ns k 1773) := by
  refine incMk (ns k 1781) (ns k 1782) (ns k 1783) (ns_safe k 1780 (by decide) (by decide)) (ns_safe k 1782 (by decide) (by decide)) (ns_safe k 1783 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 1781 (by decide) (by decide)),(ns_safe k 1782 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1938 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1938) (ns k 1929) (ns k 1936) := by
  refine incMk (ns k 1939) (ns k 1940) (ns k 1941) (ns_safe k 1938 (by decide) (by decide)) (ns_safe k 1940 (by decide) (by decide)) (ns_safe k 1941 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 1939 (by decide) (by decide)),(ns_safe k 1940 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_1943 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1943) (ns k 1918) (ns k 1936) := by
  refine incMk (ns k 1944) (ns k 1945) (ns k 1946) (ns_safe k 1943 (by decide) (by decide)) (ns_safe k 1945 (by decide) (by decide)) (ns_safe k 1946 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 1944 (by decide) (by decide)),(ns_safe k 1945 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2231 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2231) (ns k 481) (ns k 2229) := by
  refine incMk (ns k 2232) (ns k 2233) (ns k 2234) (ns_safe k 2231 (by decide) (by decide)) (ns_safe k 2233 (by decide) (by decide)) (ns_safe k 2234 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2232 (by decide) (by decide)),(ns_safe k 2233 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2236 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2236) (ns k 2219) (ns k 2229) := by
  refine incMk (ns k 2237) (ns k 2238) (ns k 2239) (ns_safe k 2236 (by decide) (by decide)) (ns_safe k 2238 (by decide) (by decide)) (ns_safe k 2239 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2237 (by decide) (by decide)),(ns_safe k 2238 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2386 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2386) (ns k 950) (ns k 2384) := by
  refine incMk (ns k 2387) (ns k 2388) (ns k 2389) (ns_safe k 2386 (by decide) (by decide)) (ns_safe k 2388 (by decide) (by decide)) (ns_safe k 2389 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2387 (by decide) (by decide)),(ns_safe k 2388 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2391 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2391) (ns k 2374) (ns k 2384) := by
  refine incMk (ns k 2392) (ns k 2393) (ns k 2394) (ns_safe k 2391 (by decide) (by decide)) (ns_safe k 2393 (by decide) (by decide)) (ns_safe k 2394 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2392 (by decide) (by decide)),(ns_safe k 2393 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2527 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2527) (ns k 1425) (ns k 1589) := by
  refine incMk (ns k 2528) (ns k 2529) (ns k 2530) (ns_safe k 2527 (by decide) (by decide)) (ns_safe k 2529 (by decide) (by decide)) (ns_safe k 2530 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2528 (by decide) (by decide)),(ns_safe k 2529 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2532 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2532) (ns k 1499) (ns k 1589) := by
  refine incMk (ns k 2533) (ns k 2534) (ns k 2535) (ns_safe k 2532 (by decide) (by decide)) (ns_safe k 2534 (by decide) (by decide)) (ns_safe k 2535 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2533 (by decide) (by decide)),(ns_safe k 2534 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2769 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2769) (ns k 2758) (ns k 2767) := by
  refine incMk (ns k 2770) (ns k 2771) (ns k 2772) (ns_safe k 2769 (by decide) (by decide)) (ns_safe k 2771 (by decide) (by decide)) (ns_safe k 2772 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2770 (by decide) (by decide)),(ns_safe k 2771 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2774 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2774) (ns k 2085) (ns k 2767) := by
  refine incMk (ns k 2775) (ns k 2776) (ns k 2777) (ns_safe k 2774 (by decide) (by decide)) (ns_safe k 2776 (by decide) (by decide)) (ns_safe k 2777 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2775 (by decide) (by decide)),(ns_safe k 2776 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2901 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2901) (ns k 2890) (ns k 2899) := by
  refine incMk (ns k 2902) (ns k 2903) (ns k 2904) (ns_safe k 2901 (by decide) (by decide)) (ns_safe k 2903 (by decide) (by decide)) (ns_safe k 2904 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2902 (by decide) (by decide)),(ns_safe k 2903 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_2906 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2906) (ns k 2128) (ns k 2899) := by
  refine incMk (ns k 2907) (ns k 2908) (ns k 2909) (ns_safe k 2906 (by decide) (by decide)) (ns_safe k 2908 (by decide) (by decide)) (ns_safe k 2909 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 2907 (by decide) (by decide)),(ns_safe k 2908 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_3029 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3029) (ns k 3020) (ns k 3027) := by
  refine incMk (ns k 3030) (ns k 3031) (ns k 3032) (ns_safe k 3029 (by decide) (by decide)) (ns_safe k 3031 (by decide) (by decide)) (ns_safe k 3032 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 3030 (by decide) (by decide)),(ns_safe k 3031 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
private def code_3034 (k : Nat) :
    IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3034) (ns k 2169) (ns k 3027) := by
  refine incMk (ns k 3035) (ns k 3036) (ns k 3037) (ns_safe k 3034 (by decide) (by decide)) (ns_safe k 3036 (by decide) (by decide)) (ns_safe k 3037 (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨(ns_safe k 3035 (by decide) (by decide)),(ns_safe k 3036 (by decide) (by decide)),?_,?_,?_⟩
    · run_tac nativeRow
    · run_tac nativeRow
    · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> run_tac nativeRow
  · run_tac nativeRow
end LiteralRows
end PhysicalCallerClosure
