import NormalFinalClosure.CounterRows1
import NormalFinalClosure.CounterRows2
import NormalFinalClosure.CounterRows3
import NormalFinalClosure.CounterRows4
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

private theorem clearCode_0 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 4) (ns2 k 24) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "clearCode_0" "theorem"
private theorem clearCode_1 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 24) (ns2 k 48) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "clearCode_1" "theorem"
private theorem clearCode_2 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 48) (ns2 k 76) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "clearCode_2" "theorem"
private theorem clearCode_3 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 76) (ns2 k 124) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "clearCode_3" "theorem"
private theorem decCode_4 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 125) (ns2 k 189) (ns2 k 147) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_4" "theorem"
private theorem incCode_5 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 147) (ns2 k 166) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_5" "theorem"
private theorem incCode_6 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 166) (ns2 k 125) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_6" "theorem"
private theorem decCode_7 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 189) (ns2 k 238) (ns2 k 223) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_7" "theorem"
private theorem incCode_8 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 223) (ns2 k 189) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_8" "theorem"
private theorem decCode_9 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 238) (ns2 k 445) (ns2 k 266) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_9" "theorem"
private theorem incCode_10 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 266) (ns2 k 285) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_10" "theorem"
private theorem incCode_11 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 285) (ns2 k 312) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_11" "theorem"
private theorem decCode_12 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 312) (ns2 k 391) (ns2 k 340) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_12" "theorem"
private theorem decCode_13 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 340) (ns2 k 391) (ns2 k 368) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_13" "theorem"
private theorem incCode_14 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 368) (ns2 k 312) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_14" "theorem"
private theorem decCode_15 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 392) (ns2 k 238) (ns2 k 426) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_15" "theorem"
private theorem incCode_16 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 426) (ns2 k 392) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_16" "theorem"
private theorem clearCode_17 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 true (ns2 k 445) (ns2 k 571) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "clearCode_17" "theorem"
private theorem decCode_18 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 465) (ns2 k 622) (ns2 k 493) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_18" "theorem"
private theorem decCode_19 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 518) (ns2 k 736) (ns2 k 546) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_19" "theorem"
private theorem decCode_20 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 571) (ns2 k 0) (ns2 k 599) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_20" "theorem"
private theorem decCode_21 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 623) (ns2 k 687) (ns2 k 645) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_21" "theorem"
private theorem incCode_22 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 645) (ns2 k 664) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_22" "theorem"
private theorem incCode_23 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 664) (ns2 k 623) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_23" "theorem"
private theorem decCode_24 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 687) (ns2 k 850) (ns2 k 721) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_24" "theorem"
private theorem incCode_25 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 721) (ns2 k 687) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "incCode_25" "theorem"
private theorem decCode_26 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 737) (ns2 k 801) (ns2 k 759) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows1 "decCode_26" "theorem"
private theorem incCode_27 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 759) (ns2 k 778) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_27" "theorem"
private theorem incCode_28 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 778) (ns2 k 737) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_28" "theorem"
private theorem decCode_29 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 801) (ns2 k 1628) (ns2 k 835) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_29" "theorem"
private theorem incCode_30 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 835) (ns2 k 801) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_30" "theorem"
private theorem decCode_31 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 850) (ns2 k 1149) (ns2 k 890) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_31" "theorem"
private theorem decCode_32 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 891) (ns2 k 1035) (ns2 k 961) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_32" "theorem"
private theorem decCode_33 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 961) (ns2 k 3664) (ns2 k 989) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_33" "theorem"
private theorem incCode_34 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 989) (ns2 k 1012) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_34" "theorem"
private theorem incCode_35 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1012) (ns2 k 891) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_35" "theorem"
private theorem decCode_36 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1036) (ns2 k 1117) (ns2 k 1070) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_36" "theorem"
private theorem incCode_37 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1070) (ns2 k 1036) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_37" "theorem"
private theorem decCode_38 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 1150) (ns2 k 1222) (ns2 k 1172) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_38" "theorem"
private theorem incCode_39 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1172) (ns2 k 1195) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_39" "theorem"
private theorem incCode_40 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 1195) (ns2 k 1150) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_40" "theorem"
private theorem decCode_41 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 1222) (ns2 k 1277) (ns2 k 1262) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_41" "theorem"
private theorem incCode_42 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 1262) (ns2 k 1222) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_42" "theorem"
private theorem decCode_43 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1277) (ns2 k 1506) (ns2 k 1311) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_43" "theorem"
private theorem decCode_44 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1311) (ns2 k 1428) (ns2 k 1381) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_44" "theorem"
private theorem decCode_45 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 1628) (ns2 k 2001) (ns2 k 1668) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_45" "theorem"
private theorem decCode_46 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1669) (ns2 k 1813) (ns2 k 1739) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_46" "theorem"
private theorem decCode_47 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 1739) (ns2 k 3850) (ns2 k 1767) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_47" "theorem"
private theorem incCode_48 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1767) (ns2 k 1790) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_48" "theorem"
private theorem incCode_49 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1790) (ns2 k 1669) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_49" "theorem"
private theorem decCode_50 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1814) (ns2 k 1895) (ns2 k 1848) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_50" "theorem"
private theorem incCode_51 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1848) (ns2 k 1814) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_51" "theorem"
private theorem decCode_52 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 1895) (ns2 k 3850) (ns2 k 1923) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "decCode_52" "theorem"
private theorem incCode_53 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1923) (ns2 k 1970) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows2 "incCode_53" "theorem"
private theorem decCode_54 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2002) (ns2 k 2074) (ns2 k 2024) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_54" "theorem"
private theorem incCode_55 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2024) (ns2 k 2047) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_55" "theorem"
private theorem incCode_56 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2047) (ns2 k 2002) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_56" "theorem"
private theorem decCode_57 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2074) (ns2 k 2129) (ns2 k 2114) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_57" "theorem"
private theorem incCode_58 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2114) (ns2 k 2074) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_58" "theorem"
private theorem decCode_59 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2129) (ns2 k 2312) (ns2 k 2163) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_59" "theorem"
private theorem decCode_60 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2163) (ns2 k 2280) (ns2 k 2233) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_60" "theorem"
private theorem decCode_61 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2434) (ns2 k 2703) (ns2 k 2474) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_61" "theorem"
private theorem decCode_62 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2475) (ns2 k 2619) (ns2 k 2545) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_62" "theorem"
private theorem decCode_63 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 2545) (ns2 k 4036) (ns2 k 2573) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_63" "theorem"
private theorem incCode_64 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2573) (ns2 k 2596) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_64" "theorem"
private theorem incCode_65 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2596) (ns2 k 2475) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_65" "theorem"
private theorem decCode_66 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2620) (ns2 k 2701) (ns2 k 2654) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_66" "theorem"
private theorem incCode_67 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2654) (ns2 k 2620) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_67" "theorem"
private theorem decCode_68 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2704) (ns2 k 2776) (ns2 k 2726) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_68" "theorem"
private theorem incCode_69 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2726) (ns2 k 2749) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_69" "theorem"
private theorem incCode_70 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2749) (ns2 k 2704) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_70" "theorem"
private theorem decCode_71 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 2776) (ns2 k 2831) (ns2 k 2816) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_71" "theorem"
private theorem incCode_72 : ∀ (k : Nat), IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 2816) (ns2 k 2776) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "incCode_72" "theorem"
private theorem decCode_73 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 2831) (ns2 k 3030) (ns2 k 2865) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_73" "theorem"
private theorem decCode_74 : ∀ (k : Nat), DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 2865) (ns2 k 2982) (ns2 k 2935) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "decCode_74" "theorem"
private theorem clearCode_75 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3139) (ns2 k 3159) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "clearCode_75" "theorem"
private theorem clearCode_76 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3159) (ns2 k 3183) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "clearCode_76" "theorem"
private theorem clearCode_77 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3183) (ns2 k 3211) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "clearCode_77" "theorem"
private theorem clearCode_78 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3211) (ns2 k 3259) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "clearCode_78" "theorem"
private theorem clearCode_79 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3259) (ns2 k 3303) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "clearCode_79" "theorem"
private theorem clearCode_80 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3325) (ns2 k 3345) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows3 "clearCode_80" "theorem"
private theorem clearCode_81 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3345) (ns2 k 3369) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_81" "theorem"
private theorem clearCode_82 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3369) (ns2 k 3397) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_82" "theorem"
private theorem clearCode_83 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3397) (ns2 k 3445) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_83" "theorem"
private theorem clearCode_84 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3445) (ns2 k 3489) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_84" "theorem"
private theorem clearCode_85 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3495) (ns2 k 3515) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_85" "theorem"
private theorem clearCode_86 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3515) (ns2 k 3539) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_86" "theorem"
private theorem clearCode_87 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3539) (ns2 k 3567) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_87" "theorem"
private theorem clearCode_88 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3567) (ns2 k 3615) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_88" "theorem"
private theorem clearCode_89 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3615) (ns2 k 3659) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_89" "theorem"
private theorem clearCode_90 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3681) (ns2 k 3701) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_90" "theorem"
private theorem clearCode_91 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3701) (ns2 k 3725) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_91" "theorem"
private theorem clearCode_92 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3725) (ns2 k 3753) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_92" "theorem"
private theorem clearCode_93 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3753) (ns2 k 3801) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_93" "theorem"
private theorem clearCode_94 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3801) (ns2 k 3845) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_94" "theorem"
private theorem clearCode_95 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3867) (ns2 k 3887) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_95" "theorem"
private theorem clearCode_96 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3887) (ns2 k 3911) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_96" "theorem"
private theorem clearCode_97 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3911) (ns2 k 3939) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_97" "theorem"
private theorem clearCode_98 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3939) (ns2 k 3987) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_98" "theorem"
private theorem clearCode_99 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3987) (ns2 k 4031) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_99" "theorem"
private theorem clearCode_100 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 4037) (ns2 k 4057) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_100" "theorem"
private theorem clearCode_101 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 4057) (ns2 k 4081) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_101" "theorem"
private theorem clearCode_102 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 4081) (ns2 k 4109) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_102" "theorem"
private theorem clearCode_103 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 4109) (ns2 k 4157) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_103" "theorem"
private theorem clearCode_104 : ∀ (k : Nat), ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 4157) (ns2 k 4201) := by
  run_tac selectCounter `NormalFinalClosure.CounterRows4 "clearCode_104" "theorem"
end NormalFinalClosure
