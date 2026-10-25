import CappedWorkspace.Target
namespace CappedWorkspace
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
/-- Proof-side transcription of q98..q200 exported instruction codes; never executes an input. -/
def instructions : List Nat := [
  893, 364, 367, 902, 896, 367, 910, 905, 908, 918, 921, 924, 1055, 935, 924, 937, 932, 935,
  947, 950, 953, 947, 959, 953, 965, 968, 971, 973, 968, 971, 983, 986, 989, 993, 986, 989,
  1000, 993, 996, 1008, 1011, 1014, 1018, 1011, 1014, 1026, 1029, 1032, 361, 1038, 367, 1035, 364, 1050,
  910, 364, 1050, 1063, 1058, 1061, 1073, 1076, 1079, 1073, 1085, 1079, 1090, 1093, 1096, 1100, 1103, 1106,
  1206, 364, 1109, 1117, 1112, 1115, 1127, 1130, 1133, 1135, 1130, 1133, 1145, 1148, 1151, 1153, 1148, 1151,
  1164, 364, 367, 1171, 1164, 1167, 1179, 1182, 1185, 1189, 1182, 1185, 1197, 1200, 1203, 1106, 1200, 1203,
  1216, 1209, 1212, 1226, 1229, 1232, 1368, 364, 1235, 1243, 1238, 1241, 1253, 1256, 1259, 1261, 1256, 1259,
  1271, 1274, 1277, 1279, 1274, 1277, 1289, 1292, 1295, 1297, 1292, 1295, 1308, 364, 367, 1315, 1308, 1311,
  1323, 1326, 1329, 1333, 1326, 1329, 1341, 1344, 1347, 1351, 1344, 1347, 1359, 1362, 1365, 1232, 1362, 1365,
  1378, 1371, 1374, 1388, 1391, 1394, 1566, 364, 1397, 1405, 1400, 1403, 1415, 1418, 1421, 1423, 1418, 1421,
  1433, 1436, 1439, 1441, 1436, 1439, 1451, 1454, 1457, 1459, 1454, 1457, 1469, 1472, 1475, 1477, 1472, 1475,
  1488, 364, 367, 1495, 1488, 1491, 1503, 1506, 1509, 1513, 1506, 1509, 1521, 1524, 1527, 1531, 1524, 1527,
  1539, 1542, 1545, 1549, 1542, 1545, 1557, 1560, 1563, 1394, 1560, 1563, 1576, 1569, 1572, 1586, 1589, 1592,
  1800, 364, 1595, 1603, 1598, 1601, 1613, 1616, 1619, 1621, 1616, 1619, 1631, 1634, 1637, 1639, 1634, 1637,
  1649, 1652, 1655, 1657, 1652, 1655, 1667, 1670, 1673, 1675, 1670, 1673, 1685, 1688, 1691, 1693, 1688, 1691,
  1704, 364, 367, 1711, 1704, 1707, 1719, 1722, 1725, 1729, 1722, 1725, 1737, 1740, 1743, 1747, 1740, 1743,
  1755, 1758, 1761, 1765, 1758, 1761, 1773, 1776, 1779, 1783, 1776, 1779, 1791, 1794, 1797, 1592, 1794, 1797,
  1810, 1803, 1806 ]
private abbrev codes (k : Nat) : Array Nat := by
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.program"
    let id := mkIdent n.get!.1; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident))
private abbrev before (k : Nat) : List Nat := by
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before"
    let id := mkIdent n.get!.1; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private theorem lookup (k i : Nat) (hi : i < 309) :
    (codes k)[102+i]?=instructions[i]? := by
  have length : (before k).length=795 := by
    unfold before
    run_tac do
      let n := ((← getEnv).constants.toList.find? fun (n,_) =>
        n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before").get!.1
      let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.length_append]))
      let names := (← getEnv).constants.toList.map Prod.fst
      for j in List.range 12 do
        if !(← getGoals).isEmpty then
          let n := (names.find? fun n => n.toString.startsWith "_private.Cursor.Machine." &&
            n.toString.endsWith (".Cursor.before"++toString j)).get!
          let cid := mkIdent n; let kv := mkIdent `k
          let len := if j=11 then 3 else 72
          evalTactic (← `(tactic| have hl : ($cid:ident $kv:ident 0).length=$(quote len) := rfl))
          evalTactic (← `(tactic| rw [hl]))
      if !(← getGoals).isEmpty then evalTactic (← `(tactic| rfl))
  have split : (before k).drop 102=instructions++(before k).drop 411 := by
    unfold before
    run_tac do
      let n := ((← getEnv).constants.toList.find? fun (n,_) =>
        n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before").get!.1
      let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
    rfl
  have len : instructions.length=309 := rfl
  unfold codes
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.program"
    let id := mkIdent n.get!.1
    evalTactic (← `(tactic| simp only [$id:ident]))
  simp only [List.getElem?_toArray,List.append_assoc]
  change (before k++_)[102+i]?=instructions[i]?
  rw [List.getElem?_append,if_pos (by omega)]
  rw [← List.getElem?_drop,split,List.getElem?_append,if_pos (by simpa only [len] using hi)]
private theorem small_mod (k i : Nat) (h : i  ≤  201) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private theorem decode_row (k i code : Nat) (b : Option Bool)
    (lo : 64 ≤ i) (hi : i < 201) (h65 : i ≠ 65) (h66 : i ≠ 66) (h67 : i ≠ 67)
    (got : (codes k)[3*(i-64)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  simp only [UniformTM.step,Cursor.machine,Cursor.q,small_mod k i (by omega),
    small_mod k 39 (by omega),small_mod k 40 (by omega),Fin.mk.injEq,
    show i ≠ 39 by omega,show i ≠ 40 by omega,↓reduceIte]
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.decode"
    let id := mkIdent n.get!.1
    evalTactic (← `(tactic| simp only [$id:ident]))
  simp only [show i ≠ 57 by omega,show i ≠ 58 by omega,show ¬i < 64 by omega,h65,h66,h67,↓reduceIte]
  cases b with
  | none =>
    dsimp only [codes] at got
    dsimp only
    rw [got]
    rfl
  | some b =>
    cases b <;> dsimp only [codes] at got <;> dsimp only <;> rw [got] <;> rfl

/-- Every setup instruction is pinned to the unchanged Cursor.step, with fixed k. -/
theorem setup_row (k i code : Nat) (b : Option Bool) (lo : 98 ≤ i) (hi : i < 201)
    (got : instructions[3*(i-98)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply decode_row k i code b (by omega) hi (by omega) (by omega) (by omega)
  cases b with
  | none =>
    change (codes k)[3*(i-64)]?=some code
    rw [show 3*(i-64)=102+3*(i-98) by omega,lookup k (3*(i-98)) (by omega)]
    exact got
  | some b =>
    cases b
    · change (codes k)[3*(i-64)+1]?=some code
      rw [show 3*(i-64)+1=102+(3*(i-98)+1) by omega,lookup k (3*(i-98)+1) (by omega)]
      exact got
    · change (codes k)[3*(i-64)+2]?=some code
      rw [show 3*(i-64)+2=102+(3*(i-98)+2) by omega,lookup k (3*(i-98)+2) (by omega)]
      exact got
end CappedWorkspace
