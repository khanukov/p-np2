import NormalFinalClosure.CounterSupport2
import NormalFinalClosure.Navigation2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["FromHRows"]),
    (`NormalFinalClosure.Navigation2,`NormalFinalClosure,["HToSRows","SToHRows","DToHRows"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact navigation certificate API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing navigation certificate owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong navigation certificate owner"
      let kind:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
      unless kind != "other" do throwError "Wrong navigation certificate kind"
      logInfo m!"literal-navigation-certificate-interface|{name}|{kind}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem s_to_h_1137 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1137) (ns2 k 1140) := by
  refine ⟨ns2 k 1138,ns2 k 1139,ns2_safe k 1137,ns2_safe k 1138,ns2_safe k 1139,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1140 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1140) (ns2 k 1628) := by
  refine ⟨ns2 k 1141,ns2 k 1142,ns2_safe k 1140,ns2_safe k 1141,ns2_safe k 1142,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_1143 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1143) (ns2 k 1146) := by
  refine ⟨ns2 k 1144,ns2 k 1145,ns2_safe k 1143,ns2_safe k 1144,ns2_safe k 1145,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1146 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1146) (ns2 k 2434) := by
  refine ⟨ns2 k 1147,ns2 k 1148,ns2_safe k 1146,ns2_safe k 1147,ns2_safe k 1148,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_1475 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 1475) (ns2 k 1479) := by
  refine ⟨ns2 k 1476,ns2 k 1477,ns2 k 1478,ns2_safe k 1475,ns2_safe k 1476,ns2_safe k 1477,ns2_safe k 1478,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_1479 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 1479) (ns2 k 1482) := by
  refine ⟨ns2 k 1480,ns2 k 1481,ns2_safe k 1479,ns2_safe k 1480,ns2_safe k 1481,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_1487 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1487) (ns2 k 1490) := by
  refine ⟨ns2 k 1488,ns2 k 1489,ns2_safe k 1487,ns2_safe k 1488,ns2_safe k 1489,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1490 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1490) (ns2 k 1277) := by
  refine ⟨ns2 k 1491,ns2 k 1492,ns2_safe k 1490,ns2_safe k 1491,ns2_safe k 1492,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_1494 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1494) (ns2 k 1497) := by
  refine ⟨ns2 k 1495,ns2 k 1496,ns2_safe k 1494,ns2_safe k 1495,ns2_safe k 1496,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1497 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1497) (ns2 k 2129) := by
  refine ⟨ns2 k 1498,ns2 k 1499,ns2_safe k 1497,ns2_safe k 1498,ns2_safe k 1499,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_1500 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1500) (ns2 k 1503) := by
  refine ⟨ns2 k 1501,ns2 k 1502,ns2_safe k 1500,ns2_safe k 1501,ns2_safe k 1502,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1503 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1503) (ns2 k 2831) := by
  refine ⟨ns2 k 1504,ns2 k 1505,ns2_safe k 1503,ns2_safe k 1504,ns2_safe k 1505,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_1597 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 1597) (ns2 k 1601) := by
  refine ⟨ns2 k 1598,ns2 k 1599,ns2 k 1600,ns2_safe k 1597,ns2_safe k 1598,ns2_safe k 1599,ns2_safe k 1600,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_1601 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 1601) (ns2 k 1604) := by
  refine ⟨ns2 k 1602,ns2 k 1603,ns2_safe k 1601,ns2_safe k 1602,ns2_safe k 1603,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_1609 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1609) (ns2 k 1612) := by
  refine ⟨ns2 k 1610,ns2 k 1611,ns2_safe k 1609,ns2_safe k 1610,ns2_safe k 1611,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1612 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1612) (ns2 k 1506) := by
  refine ⟨ns2 k 1613,ns2 k 1614,ns2_safe k 1612,ns2_safe k 1613,ns2_safe k 1614,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_1616 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1616) (ns2 k 1619) := by
  refine ⟨ns2 k 1617,ns2 k 1618,ns2_safe k 1616,ns2_safe k 1617,ns2_safe k 1618,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1619 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1619) (ns2 k 2312) := by
  refine ⟨ns2 k 1620,ns2 k 1621,ns2_safe k 1619,ns2_safe k 1620,ns2_safe k 1621,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_1622 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1622) (ns2 k 1625) := by
  refine ⟨ns2 k 1623,ns2 k 1624,ns2_safe k 1622,ns2_safe k 1623,ns2_safe k 1624,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1625 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1625) (ns2 k 3030) := by
  refine ⟨ns2 k 1626,ns2 k 1627,ns2_safe k 1625,ns2_safe k 1626,ns2_safe k 1627,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_1970 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 1970) (ns2 k 1974) := by
  refine ⟨ns2 k 1971,ns2 k 1972,ns2 k 1973,ns2_safe k 1970,ns2_safe k 1971,ns2_safe k 1972,ns2_safe k 1973,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_1974 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 1974) (ns2 k 1977) := by
  refine ⟨ns2 k 1975,ns2 k 1976,ns2_safe k 1974,ns2_safe k 1975,ns2_safe k 1976,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_1982 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1982) (ns2 k 1985) := by
  refine ⟨ns2 k 1983,ns2 k 1984,ns2_safe k 1982,ns2_safe k 1983,ns2_safe k 1984,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
end NormalFinalClosure
