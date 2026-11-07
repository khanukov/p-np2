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

private theorem incCode_27 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 759) (ns2 k 778) := by
  refine ⟨ns2 k 767,ns2 k 768,ns2 k 769,ns2 k 770,nsSafe k 767,nsSafe k 768,nsSafe k 769,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_28 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 778) (ns2 k 737) := by
  refine ⟨ns2 k 788,ns2 k 789,ns2 k 790,ns2 k 791,nsSafe k 788,nsSafe k 789,nsSafe k 790,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_29 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 801) (ns2 k 1628) (ns2 k 835) := by
  refine ⟨ns2 k 811,ns2 k 812,ns2 k 813,ns2 k 814,ns2 k 815,ns2 k 825,nsSafe k 811,nsSafe k 812,nsSafe k 813,nsSafe k 814,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_30 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 835) (ns2 k 801) := by
  refine ⟨ns2 k 841,ns2 k 842,ns2 k 843,ns2 k 844,nsSafe k 841,nsSafe k 842,nsSafe k 843,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_31 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 850) (ns2 k 1149) (ns2 k 890) := by
  refine ⟨ns2 k 862,ns2 k 863,ns2 k 864,ns2 k 865,ns2 k 866,ns2 k 878,nsSafe k 862,nsSafe k 863,nsSafe k 864,nsSafe k 865,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem decCode_32 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 891) (ns2 k 1035) (ns2 k 961) := by
  refine ⟨ns2 k 913,ns2 k 914,ns2 k 915,ns2 k 916,ns2 k 917,ns2 k 939,nsSafe k 913,nsSafe k 914,nsSafe k 915,nsSafe k 916,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem decCode_33 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 961) (ns2 k 3664) (ns2 k 989) := by
  refine ⟨ns2 k 969,ns2 k 970,ns2 k 971,ns2 k 972,ns2 k 973,ns2 k 981,nsSafe k 969,nsSafe k 970,nsSafe k 971,nsSafe k 972,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_34 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 989) (ns2 k 1012) := by
  refine ⟨ns2 k 999,ns2 k 1000,ns2 k 1001,ns2 k 1002,nsSafe k 999,nsSafe k 1000,nsSafe k 1001,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_35 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1012) (ns2 k 891) := by
  refine ⟨ns2 k 1022,ns2 k 1023,ns2 k 1024,ns2 k 1025,nsSafe k 1022,nsSafe k 1023,nsSafe k 1024,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_36 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1036) (ns2 k 1117) (ns2 k 1070) := by
  refine ⟨ns2 k 1046,ns2 k 1047,ns2 k 1048,ns2 k 1049,ns2 k 1050,ns2 k 1060,nsSafe k 1046,nsSafe k 1047,nsSafe k 1048,nsSafe k 1049,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_37 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1070) (ns2 k 1036) := by
  refine ⟨ns2 k 1092,ns2 k 1093,ns2 k 1094,ns2 k 1095,nsSafe k 1092,nsSafe k 1093,nsSafe k 1094,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_38 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 1150) (ns2 k 1222) (ns2 k 1172) := by
  refine ⟨ns2 k 1156,ns2 k 1157,ns2 k 1158,ns2 k 1159,ns2 k 1160,ns2 k 1166,nsSafe k 1156,nsSafe k 1157,nsSafe k 1158,nsSafe k 1159,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_39 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1172) (ns2 k 1195) := by
  refine ⟨ns2 k 1182,ns2 k 1183,ns2 k 1184,ns2 k 1185,nsSafe k 1182,nsSafe k 1183,nsSafe k 1184,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_40 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 1195) (ns2 k 1150) := by
  refine ⟨ns2 k 1207,ns2 k 1208,ns2 k 1209,ns2 k 1210,nsSafe k 1207,nsSafe k 1208,nsSafe k 1209,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_41 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 1222) (ns2 k 1277) (ns2 k 1262) := by
  refine ⟨ns2 k 1234,ns2 k 1235,ns2 k 1236,ns2 k 1237,ns2 k 1238,ns2 k 1250,nsSafe k 1234,nsSafe k 1235,nsSafe k 1236,nsSafe k 1237,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_42 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 3 (ns2 k 1262) (ns2 k 1222) := by
  refine ⟨ns2 k 1268,ns2 k 1269,ns2 k 1270,ns2 k 1271,nsSafe k 1268,nsSafe k 1269,nsSafe k 1270,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_43 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1277) (ns2 k 1506) (ns2 k 1311) := by
  refine ⟨ns2 k 1287,ns2 k 1288,ns2 k 1289,ns2 k 1290,ns2 k 1291,ns2 k 1301,nsSafe k 1287,nsSafe k 1288,nsSafe k 1289,nsSafe k 1290,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem decCode_44 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1311) (ns2 k 1428) (ns2 k 1381) := by
  refine ⟨ns2 k 1333,ns2 k 1334,ns2 k 1335,ns2 k 1336,ns2 k 1337,ns2 k 1359,nsSafe k 1333,nsSafe k 1334,nsSafe k 1335,nsSafe k 1336,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem decCode_45 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 6 (ns2 k 1628) (ns2 k 2001) (ns2 k 1668) := by
  refine ⟨ns2 k 1640,ns2 k 1641,ns2 k 1642,ns2 k 1643,ns2 k 1644,ns2 k 1656,nsSafe k 1640,nsSafe k 1641,nsSafe k 1642,nsSafe k 1643,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem decCode_46 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1669) (ns2 k 1813) (ns2 k 1739) := by
  refine ⟨ns2 k 1691,ns2 k 1692,ns2 k 1693,ns2 k 1694,ns2 k 1695,ns2 k 1717,nsSafe k 1691,nsSafe k 1692,nsSafe k 1693,nsSafe k 1694,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem decCode_47 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 1739) (ns2 k 3850) (ns2 k 1767) := by
  refine ⟨ns2 k 1747,ns2 k 1748,ns2 k 1749,ns2 k 1750,ns2 k 1751,ns2 k 1759,nsSafe k 1747,nsSafe k 1748,nsSafe k 1749,nsSafe k 1750,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_48 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1767) (ns2 k 1790) := by
  refine ⟨ns2 k 1777,ns2 k 1778,ns2 k 1779,ns2 k 1780,nsSafe k 1777,nsSafe k 1778,nsSafe k 1779,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem incCode_49 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1790) (ns2 k 1669) := by
  refine ⟨ns2 k 1800,ns2 k 1801,ns2 k 1802,ns2 k 1803,nsSafe k 1800,nsSafe k 1801,nsSafe k 1802,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_50 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 5 (ns2 k 1814) (ns2 k 1895) (ns2 k 1848) := by
  refine ⟨ns2 k 1824,ns2 k 1825,ns2 k 1826,ns2 k 1827,ns2 k 1828,ns2 k 1838,nsSafe k 1824,nsSafe k 1825,nsSafe k 1826,nsSafe k 1827,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_51 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1848) (ns2 k 1814) := by
  refine ⟨ns2 k 1870,ns2 k 1871,ns2 k 1872,ns2 k 1873,nsSafe k 1870,nsSafe k 1871,nsSafe k 1872,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem decCode_52 (k : Nat) : DecRows (M:=machine2 k) (Safe:=Safe2 k) 4 (ns2 k 1895) (ns2 k 3850) (ns2 k 1923) := by
  refine ⟨ns2 k 1903,ns2 k 1904,ns2 k 1905,ns2 k 1906,ns2 k 1907,ns2 k 1915,nsSafe k 1903,nsSafe k 1904,nsSafe k 1905,nsSafe k 1906,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
private theorem incCode_53 (k : Nat) : IncRows (M:=machine2 k) (Safe:=Safe2 k) 11 (ns2 k 1923) (ns2 k 1970) := by
  refine ⟨ns2 k 1945,ns2 k 1946,ns2 k 1947,ns2 k 1948,nsSafe k 1945,nsSafe k 1946,nsSafe k 1947,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
end NormalFinalClosure
