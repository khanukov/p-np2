import NormalFinalClosure.CounterSupport2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def selectCounter (owner : Name) (leaf kind : String) : TacticM Unit := do
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure")
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact split counter API"
  let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
  unless actual==kind do throwError "Wrong split counter kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing split counter owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong split counter owner"
  logInfo m!"split-native-certificate|{n}|{kind}|{ci.type}"
  closeMainGoal `selectCounter (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["ClearRows","DecRows","IncRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing actual counter type"
      let some i:=e.getModuleIdxFor? n | throwError "Missing actual counter type owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong actual counter type owner"
      logInfo m!"split-native-type|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev nativeRow : TacticM Unit := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nativeRow" "definition"
private abbrev nativeRoute : Nat → TacticM Unit := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nativeRoute" "definition"
private theorem nsSafe : ∀ k i,Safe2 k (ns2 k i) := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nsSafe" "theorem"

private theorem decCode_54 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2002) (ns2 k 2074) (ns2 k 2024) := by
  refine ⟨ns2 k 2008,ns2 k 2009,ns2 k 2010,ns2 k 2011,ns2 k 2012,ns2 k 2018,nsSafe k 2008,nsSafe k 2009,nsSafe k 2010,nsSafe k 2011,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_55 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2024) (ns2 k 2047) := by
  refine ⟨ns2 k 2034,ns2 k 2035,ns2 k 2036,ns2 k 2037,nsSafe k 2034,nsSafe k 2035,nsSafe k 2036,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_56 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2047) (ns2 k 2002) := by
  refine ⟨ns2 k 2059,ns2 k 2060,ns2 k 2061,ns2 k 2062,nsSafe k 2059,nsSafe k 2060,nsSafe k 2061,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_57 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2074) (ns2 k 2129) (ns2 k 2114) := by
  refine ⟨ns2 k 2086,ns2 k 2087,ns2 k 2088,ns2 k 2089,ns2 k 2090,ns2 k 2102,nsSafe k 2086,nsSafe k 2087,nsSafe k 2088,nsSafe k 2089,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_58 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2114) (ns2 k 2074) := by
  refine ⟨ns2 k 2120,ns2 k 2121,ns2 k 2122,ns2 k 2123,nsSafe k 2120,nsSafe k 2121,nsSafe k 2122,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_59 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2129) (ns2 k 2312) (ns2 k 2163) := by
  refine ⟨ns2 k 2139,ns2 k 2140,ns2 k 2141,ns2 k 2142,ns2 k 2143,ns2 k 2153,nsSafe k 2139,nsSafe k 2140,nsSafe k 2141,nsSafe k 2142,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_60 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2163) (ns2 k 2280) (ns2 k 2233) := by
  refine ⟨ns2 k 2185,ns2 k 2186,ns2 k 2187,ns2 k 2188,ns2 k 2189,ns2 k 2211,nsSafe k 2185,nsSafe k 2186,nsSafe k 2187,nsSafe k 2188,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_61 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2434) (ns2 k 2703) (ns2 k 2474) := by
  refine ⟨ns2 k 2446,ns2 k 2447,ns2 k 2448,ns2 k 2449,ns2 k 2450,ns2 k 2462,nsSafe k 2446,nsSafe k 2447,nsSafe k 2448,nsSafe k 2449,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_62 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2475) (ns2 k 2619) (ns2 k 2545) := by
  refine ⟨ns2 k 2497,ns2 k 2498,ns2 k 2499,ns2 k 2500,ns2 k 2501,ns2 k 2523,nsSafe k 2497,nsSafe k 2498,nsSafe k 2499,nsSafe k 2500,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_63 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 2545) (ns2 k 4036) (ns2 k 2573) := by
  refine ⟨ns2 k 2553,ns2 k 2554,ns2 k 2555,ns2 k 2556,ns2 k 2557,ns2 k 2565,nsSafe k 2553,nsSafe k 2554,nsSafe k 2555,nsSafe k 2556,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_64 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2573) (ns2 k 2596) := by
  refine ⟨ns2 k 2583,ns2 k 2584,ns2 k 2585,ns2 k 2586,nsSafe k 2583,nsSafe k 2584,nsSafe k 2585,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_65 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2596) (ns2 k 2475) := by
  refine ⟨ns2 k 2606,ns2 k 2607,ns2 k 2608,ns2 k 2609,nsSafe k 2606,nsSafe k 2607,nsSafe k 2608,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_66 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2620) (ns2 k 2701) (ns2 k 2654) := by
  refine ⟨ns2 k 2630,ns2 k 2631,ns2 k 2632,ns2 k 2633,ns2 k 2634,ns2 k 2644,nsSafe k 2630,nsSafe k 2631,nsSafe k 2632,nsSafe k 2633,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_67 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2654) (ns2 k 2620) := by
  refine ⟨ns2 k 2676,ns2 k 2677,ns2 k 2678,ns2 k 2679,nsSafe k 2676,nsSafe k 2677,nsSafe k 2678,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_68 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2704) (ns2 k 2776) (ns2 k 2726) := by
  refine ⟨ns2 k 2710,ns2 k 2711,ns2 k 2712,ns2 k 2713,ns2 k 2714,ns2 k 2720,nsSafe k 2710,nsSafe k 2711,nsSafe k 2712,nsSafe k 2713,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_69 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2726) (ns2 k 2749) := by
  refine ⟨ns2 k 2736,ns2 k 2737,ns2 k 2738,ns2 k 2739,nsSafe k 2736,nsSafe k 2737,nsSafe k 2738,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_70 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2749) (ns2 k 2704) := by
  refine ⟨ns2 k 2761,ns2 k 2762,ns2 k 2763,ns2 k 2764,nsSafe k 2761,nsSafe k 2762,nsSafe k 2763,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_71 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2776) (ns2 k 2831) (ns2 k 2816) := by
  refine ⟨ns2 k 2788,ns2 k 2789,ns2 k 2790,ns2 k 2791,ns2 k 2792,ns2 k 2804,nsSafe k 2788,nsSafe k 2789,nsSafe k 2790,nsSafe k 2791,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_72 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2816) (ns2 k 2776) := by
  refine ⟨ns2 k 2822,ns2 k 2823,ns2 k 2824,ns2 k 2825,nsSafe k 2822,nsSafe k 2823,nsSafe k 2824,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_73 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2831) (ns2 k 3030) (ns2 k 2865) := by
  refine ⟨ns2 k 2841,ns2 k 2842,ns2 k 2843,ns2 k 2844,ns2 k 2845,ns2 k 2855,nsSafe k 2841,nsSafe k 2842,nsSafe k 2843,nsSafe k 2844,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_74 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2865) (ns2 k 2982) (ns2 k 2935) := by
  refine ⟨ns2 k 2887,ns2 k 2888,ns2 k 2889,ns2 k 2890,ns2 k 2891,ns2 k 2913,nsSafe k 2887,nsSafe k 2888,nsSafe k 2889,nsSafe k 2890,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b ne;cases b with
    | none=>run_tac nativeRow
    | some b=>cases b with
      | false=>run_tac nativeRow
      | true=>exact (ne rfl).elim
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_75 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3139) (ns2 k 3159) := by
  refine ⟨ns2 k 3147,ns2 k 3148,ns2 k 3149,nsSafe k 3147,nsSafe k 3148,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_76 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3159) (ns2 k 3183) := by
  refine ⟨ns2 k 3169,ns2 k 3170,ns2 k 3171,nsSafe k 3169,nsSafe k 3170,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_77 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3183) (ns2 k 3211) := by
  refine ⟨ns2 k 3195,ns2 k 3196,ns2 k 3197,nsSafe k 3195,nsSafe k 3196,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_78 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3211) (ns2 k 3259) := by
  refine ⟨ns2 k 3233,ns2 k 3234,ns2 k 3235,nsSafe k 3233,nsSafe k 3234,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_79 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3259) (ns2 k 3303) := by
  refine ⟨ns2 k 3279,ns2 k 3280,ns2 k 3281,nsSafe k 3279,nsSafe k 3280,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_80 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3325) (ns2 k 3345) := by
  refine ⟨ns2 k 3333,ns2 k 3334,ns2 k 3335,nsSafe k 3333,nsSafe k 3334,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
end NormalFinalClosure
