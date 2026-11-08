import FullIngressClosure.Counters
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [
      ("Rows","native_row","nativeRow"),("Rows","extra_safe","extraSafe"),
      ("Paths","Safe","Safe"),("Paths","RouteR","RouteR"),("Paths","RouteL","RouteL"),
      ("Paths","RouteR.nil","rrNil"),("Paths","RouteR.next","rrNext"),
      ("Paths","RouteL.nil","rlNil"),("Paths","RouteL.next","rlNext"),
      ("Counters","Increment","Increment"),("Counters","Increment.mk","incMk"),
      ("Counters","Decrement","Decrement"),("Counters","Decrement.mk","decMk")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.FullIngressClosure."++mod++".") && n.toString.endsWith (".FullIngressClosure."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique concrete certificate term {mod}/{key}: {found.map Prod.fst}"
private def st (k i : Nat) : Fin (BodyIngress.machine k).stateCount :=
  if h:i<2035 then BodyIngress.extra k ⟨i,h⟩
  else if h:i<2038 then BodyIngress.body k (SerializedBody.entry ⟨i-2035,by omega⟩)
  else (BodyIngress.machine k).reject
private theorem safeNative (k e : Nat) (bound : e < 2035) : Safe k (st k e) := by
  dsimp only [st]
  rw [dif_pos bound]
  exact extraSafe k ⟨e,bound⟩
private theorem st_small (k i : Nat) (bound : i < 2035) :
    st k i=BodyIngress.extra k ⟨i,bound⟩ := by
  dsimp only [st]
  rw [dif_pos bound]
private def dec770 (k : Nat) : Decrement k (st k 770) (st k 774) (st k 826) := by
  refine decMk (st k 771) (st k 772) (st k 773)
    (safeNative k 770 (by decide)) (safeNative k 771 (by decide))
    (safeNative k 772 (by decide)) (safeNative k 773 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 770 (by decide),nativeRow]; rfl
  · rw [st_small k 771 (by decide),nativeRow]; rfl
  · rw [st_small k 771 (by decide),nativeRow]; rfl
  · rw [st_small k 771 (by decide),nativeRow]; rfl
  · rw [st_small k 772 (by decide),nativeRow]; rfl
  · rw [st_small k 772 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 773 (by decide),nativeRow]; rfl)
  · rw [st_small k 773 (by decide),nativeRow]; rfl
private def dec848 (k : Nat) : Decrement k (st k 848) (st k 852) (st k 900) := by
  refine decMk (st k 849) (st k 850) (st k 851)
    (safeNative k 848 (by decide)) (safeNative k 849 (by decide))
    (safeNative k 850 (by decide)) (safeNative k 851 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 848 (by decide),nativeRow]; rfl
  · rw [st_small k 849 (by decide),nativeRow]; rfl
  · rw [st_small k 849 (by decide),nativeRow]; rfl
  · rw [st_small k 849 (by decide),nativeRow]; rfl
  · rw [st_small k 850 (by decide),nativeRow]; rfl
  · rw [st_small k 850 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 851 (by decide),nativeRow]; rfl)
  · rw [st_small k 851 (by decide),nativeRow]; rfl
private def dec926 (k : Nat) : Decrement k (st k 926) (st k 930) (st k 962) := by
  refine decMk (st k 927) (st k 928) (st k 929)
    (safeNative k 926 (by decide)) (safeNative k 927 (by decide))
    (safeNative k 928 (by decide)) (safeNative k 929 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 926 (by decide),nativeRow]; rfl
  · rw [st_small k 927 (by decide),nativeRow]; rfl
  · rw [st_small k 927 (by decide),nativeRow]; rfl
  · rw [st_small k 927 (by decide),nativeRow]; rfl
  · rw [st_small k 928 (by decide),nativeRow]; rfl
  · rw [st_small k 928 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 929 (by decide),nativeRow]; rfl)
  · rw [st_small k 929 (by decide),nativeRow]; rfl
private def dec968 (k : Nat) : Decrement k (st k 968) (st k 972) (st k 984) := by
  refine decMk (st k 969) (st k 970) (st k 971)
    (safeNative k 968 (by decide)) (safeNative k 969 (by decide))
    (safeNative k 970 (by decide)) (safeNative k 971 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 968 (by decide),nativeRow]; rfl
  · rw [st_small k 969 (by decide),nativeRow]; rfl
  · rw [st_small k 969 (by decide),nativeRow]; rfl
  · rw [st_small k 969 (by decide),nativeRow]; rfl
  · rw [st_small k 970 (by decide),nativeRow]; rfl
  · rw [st_small k 970 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 971 (by decide),nativeRow]; rfl)
  · rw [st_small k 971 (by decide),nativeRow]; rfl
private def dec988 (k : Nat) : Decrement k (st k 988) (st k 992) (st k 1032) := by
  refine decMk (st k 989) (st k 990) (st k 991)
    (safeNative k 988 (by decide)) (safeNative k 989 (by decide))
    (safeNative k 990 (by decide)) (safeNative k 991 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 988 (by decide),nativeRow]; rfl
  · rw [st_small k 989 (by decide),nativeRow]; rfl
  · rw [st_small k 989 (by decide),nativeRow]; rfl
  · rw [st_small k 989 (by decide),nativeRow]; rfl
  · rw [st_small k 990 (by decide),nativeRow]; rfl
  · rw [st_small k 990 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 991 (by decide),nativeRow]; rfl)
  · rw [st_small k 991 (by decide),nativeRow]; rfl
private def dec1048 (k : Nat) : Decrement k (st k 1048) (st k 1052) (st k 1088) := by
  refine decMk (st k 1049) (st k 1050) (st k 1051)
    (safeNative k 1048 (by decide)) (safeNative k 1049 (by decide))
    (safeNative k 1050 (by decide)) (safeNative k 1051 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1048 (by decide),nativeRow]; rfl
  · rw [st_small k 1049 (by decide),nativeRow]; rfl
  · rw [st_small k 1049 (by decide),nativeRow]; rfl
  · rw [st_small k 1049 (by decide),nativeRow]; rfl
  · rw [st_small k 1050 (by decide),nativeRow]; rfl
  · rw [st_small k 1050 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1051 (by decide),nativeRow]; rfl)
  · rw [st_small k 1051 (by decide),nativeRow]; rfl
private def dec1104 (k : Nat) : Decrement k (st k 1104) (st k 1108) (st k 1148) := by
  refine decMk (st k 1105) (st k 1106) (st k 1107)
    (safeNative k 1104 (by decide)) (safeNative k 1105 (by decide))
    (safeNative k 1106 (by decide)) (safeNative k 1107 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1104 (by decide),nativeRow]; rfl
  · rw [st_small k 1105 (by decide),nativeRow]; rfl
  · rw [st_small k 1105 (by decide),nativeRow]; rfl
  · rw [st_small k 1105 (by decide),nativeRow]; rfl
  · rw [st_small k 1106 (by decide),nativeRow]; rfl
  · rw [st_small k 1106 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1107 (by decide),nativeRow]; rfl)
  · rw [st_small k 1107 (by decide),nativeRow]; rfl
private def dec1152 (k : Nat) : Decrement k (st k 1152) (st k 1156) (st k 1168) := by
  refine decMk (st k 1153) (st k 1154) (st k 1155)
    (safeNative k 1152 (by decide)) (safeNative k 1153 (by decide))
    (safeNative k 1154 (by decide)) (safeNative k 1155 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1152 (by decide),nativeRow]; rfl
  · rw [st_small k 1153 (by decide),nativeRow]; rfl
  · rw [st_small k 1153 (by decide),nativeRow]; rfl
  · rw [st_small k 1153 (by decide),nativeRow]; rfl
  · rw [st_small k 1154 (by decide),nativeRow]; rfl
  · rw [st_small k 1154 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1155 (by decide),nativeRow]; rfl)
  · rw [st_small k 1155 (by decide),nativeRow]; rfl
private def dec1326 (k : Nat) : Decrement k (st k 1326) (st k 1330) (st k 1358) := by
  refine decMk (st k 1327) (st k 1328) (st k 1329)
    (safeNative k 1326 (by decide)) (safeNative k 1327 (by decide))
    (safeNative k 1328 (by decide)) (safeNative k 1329 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1326 (by decide),nativeRow]; rfl
  · rw [st_small k 1327 (by decide),nativeRow]; rfl
  · rw [st_small k 1327 (by decide),nativeRow]; rfl
  · rw [st_small k 1327 (by decide),nativeRow]; rfl
  · rw [st_small k 1328 (by decide),nativeRow]; rfl
  · rw [st_small k 1328 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1329 (by decide),nativeRow]; rfl)
  · rw [st_small k 1329 (by decide),nativeRow]; rfl
private def dec1362 (k : Nat) : Decrement k (st k 1362) (st k 1366) (st k 1378) := by
  refine decMk (st k 1363) (st k 1364) (st k 1365)
    (safeNative k 1362 (by decide)) (safeNative k 1363 (by decide))
    (safeNative k 1364 (by decide)) (safeNative k 1365 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1362 (by decide),nativeRow]; rfl
  · rw [st_small k 1363 (by decide),nativeRow]; rfl
  · rw [st_small k 1363 (by decide),nativeRow]; rfl
  · rw [st_small k 1363 (by decide),nativeRow]; rfl
  · rw [st_small k 1364 (by decide),nativeRow]; rfl
  · rw [st_small k 1364 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1365 (by decide),nativeRow]; rfl)
  · rw [st_small k 1365 (by decide),nativeRow]; rfl
private def dec1389 (k : Nat) : Decrement k (st k 1389) (st k 1393) (st k 1423) := by
  refine decMk (st k 1390) (st k 1391) (st k 1392)
    (safeNative k 1389 (by decide)) (safeNative k 1390 (by decide))
    (safeNative k 1391 (by decide)) (safeNative k 1392 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1389 (by decide),nativeRow]; rfl
  · rw [st_small k 1390 (by decide),nativeRow]; rfl
  · rw [st_small k 1390 (by decide),nativeRow]; rfl
  · rw [st_small k 1390 (by decide),nativeRow]; rfl
  · rw [st_small k 1391 (by decide),nativeRow]; rfl
  · rw [st_small k 1391 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1392 (by decide),nativeRow]; rfl)
  · rw [st_small k 1392 (by decide),nativeRow]; rfl
private def dec1425 (k : Nat) : Decrement k (st k 1425) (st k 1429) (st k 1459) := by
  refine decMk (st k 1426) (st k 1427) (st k 1428)
    (safeNative k 1425 (by decide)) (safeNative k 1426 (by decide))
    (safeNative k 1427 (by decide)) (safeNative k 1428 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1425 (by decide),nativeRow]; rfl
  · rw [st_small k 1426 (by decide),nativeRow]; rfl
  · rw [st_small k 1426 (by decide),nativeRow]; rfl
  · rw [st_small k 1426 (by decide),nativeRow]; rfl
  · rw [st_small k 1427 (by decide),nativeRow]; rfl
  · rw [st_small k 1427 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1428 (by decide),nativeRow]; rfl)
  · rw [st_small k 1428 (by decide),nativeRow]; rfl
private def dec1461 (k : Nat) : Decrement k (st k 1461) (st k 1465) (st k 1494) := by
  refine decMk (st k 1462) (st k 1463) (st k 1464)
    (safeNative k 1461 (by decide)) (safeNative k 1462 (by decide))
    (safeNative k 1463 (by decide)) (safeNative k 1464 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1461 (by decide),nativeRow]; rfl
  · rw [st_small k 1462 (by decide),nativeRow]; rfl
  · rw [st_small k 1462 (by decide),nativeRow]; rfl
  · rw [st_small k 1462 (by decide),nativeRow]; rfl
  · rw [st_small k 1463 (by decide),nativeRow]; rfl
  · rw [st_small k 1463 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1464 (by decide),nativeRow]; rfl)
  · rw [st_small k 1464 (by decide),nativeRow]; rfl
private def dec1547 (k : Nat) : Decrement k (st k 1547) (st k 1551) (st k 1583) := by
  refine decMk (st k 1548) (st k 1549) (st k 1550)
    (safeNative k 1547 (by decide)) (safeNative k 1548 (by decide))
    (safeNative k 1549 (by decide)) (safeNative k 1550 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1547 (by decide),nativeRow]; rfl
  · rw [st_small k 1548 (by decide),nativeRow]; rfl
  · rw [st_small k 1548 (by decide),nativeRow]; rfl
  · rw [st_small k 1548 (by decide),nativeRow]; rfl
  · rw [st_small k 1549 (by decide),nativeRow]; rfl
  · rw [st_small k 1549 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1550 (by decide),nativeRow]; rfl)
  · rw [st_small k 1550 (by decide),nativeRow]; rfl
private def dec1555 (k : Nat) : Decrement k (st k 1555) (st k 1559) (st k 2038) := by
  refine decMk (st k 1556) (st k 1557) (st k 1558)
    (safeNative k 1555 (by decide)) (safeNative k 1556 (by decide))
    (safeNative k 1557 (by decide)) (safeNative k 1558 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1555 (by decide),nativeRow]; rfl
  · rw [st_small k 1556 (by decide),nativeRow]; rfl
  · rw [st_small k 1556 (by decide),nativeRow]; rfl
  · rw [st_small k 1556 (by decide),nativeRow]; rfl
  · rw [st_small k 1557 (by decide),nativeRow]; rfl
  · rw [st_small k 1557 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1558 (by decide),nativeRow]; rfl)
  · rw [st_small k 1558 (by decide),nativeRow]; rfl
private def dec1587 (k : Nat) : Decrement k (st k 1587) (st k 1591) (st k 1623) := by
  refine decMk (st k 1588) (st k 1589) (st k 1590)
    (safeNative k 1587 (by decide)) (safeNative k 1588 (by decide))
    (safeNative k 1589 (by decide)) (safeNative k 1590 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1587 (by decide),nativeRow]; rfl
  · rw [st_small k 1588 (by decide),nativeRow]; rfl
  · rw [st_small k 1588 (by decide),nativeRow]; rfl
  · rw [st_small k 1588 (by decide),nativeRow]; rfl
  · rw [st_small k 1589 (by decide),nativeRow]; rfl
  · rw [st_small k 1589 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1590 (by decide),nativeRow]; rfl)
  · rw [st_small k 1590 (by decide),nativeRow]; rfl
private def dec1595 (k : Nat) : Decrement k (st k 1595) (st k 1599) (st k 2038) := by
  refine decMk (st k 1596) (st k 1597) (st k 1598)
    (safeNative k 1595 (by decide)) (safeNative k 1596 (by decide))
    (safeNative k 1597 (by decide)) (safeNative k 1598 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1595 (by decide),nativeRow]; rfl
  · rw [st_small k 1596 (by decide),nativeRow]; rfl
  · rw [st_small k 1596 (by decide),nativeRow]; rfl
  · rw [st_small k 1596 (by decide),nativeRow]; rfl
  · rw [st_small k 1597 (by decide),nativeRow]; rfl
  · rw [st_small k 1597 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1598 (by decide),nativeRow]; rfl)
  · rw [st_small k 1598 (by decide),nativeRow]; rfl
private def dec1675 (k : Nat) : Decrement k (st k 1675) (st k 1679) (st k 1715) := by
  refine decMk (st k 1676) (st k 1677) (st k 1678)
    (safeNative k 1675 (by decide)) (safeNative k 1676 (by decide))
    (safeNative k 1677 (by decide)) (safeNative k 1678 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1675 (by decide),nativeRow]; rfl
  · rw [st_small k 1676 (by decide),nativeRow]; rfl
  · rw [st_small k 1676 (by decide),nativeRow]; rfl
  · rw [st_small k 1676 (by decide),nativeRow]; rfl
  · rw [st_small k 1677 (by decide),nativeRow]; rfl
  · rw [st_small k 1677 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1678 (by decide),nativeRow]; rfl)
  · rw [st_small k 1678 (by decide),nativeRow]; rfl
private def dec1687 (k : Nat) : Decrement k (st k 1687) (st k 1691) (st k 2038) := by
  refine decMk (st k 1688) (st k 1689) (st k 1690)
    (safeNative k 1687 (by decide)) (safeNative k 1688 (by decide))
    (safeNative k 1689 (by decide)) (safeNative k 1690 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1687 (by decide),nativeRow]; rfl
  · rw [st_small k 1688 (by decide),nativeRow]; rfl
  · rw [st_small k 1688 (by decide),nativeRow]; rfl
  · rw [st_small k 1688 (by decide),nativeRow]; rfl
  · rw [st_small k 1689 (by decide),nativeRow]; rfl
  · rw [st_small k 1689 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1690 (by decide),nativeRow]; rfl)
  · rw [st_small k 1690 (by decide),nativeRow]; rfl
private def dec1737 (k : Nat) : Decrement k (st k 1737) (st k 1741) (st k 1777) := by
  refine decMk (st k 1738) (st k 1739) (st k 1740)
    (safeNative k 1737 (by decide)) (safeNative k 1738 (by decide))
    (safeNative k 1739 (by decide)) (safeNative k 1740 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1737 (by decide),nativeRow]; rfl
  · rw [st_small k 1738 (by decide),nativeRow]; rfl
  · rw [st_small k 1738 (by decide),nativeRow]; rfl
  · rw [st_small k 1738 (by decide),nativeRow]; rfl
  · rw [st_small k 1739 (by decide),nativeRow]; rfl
  · rw [st_small k 1739 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1740 (by decide),nativeRow]; rfl)
  · rw [st_small k 1740 (by decide),nativeRow]; rfl
private def dec1749 (k : Nat) : Decrement k (st k 1749) (st k 1753) (st k 2038) := by
  refine decMk (st k 1750) (st k 1751) (st k 1752)
    (safeNative k 1749 (by decide)) (safeNative k 1750 (by decide))
    (safeNative k 1751 (by decide)) (safeNative k 1752 (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1749 (by decide),nativeRow]; rfl
  · rw [st_small k 1750 (by decide),nativeRow]; rfl
  · rw [st_small k 1750 (by decide),nativeRow]; rfl
  · rw [st_small k 1750 (by decide),nativeRow]; rfl
  · rw [st_small k 1751 (by decide),nativeRow]; rfl
  · rw [st_small k 1751 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1752 (by decide),nativeRow]; rfl)
  · rw [st_small k 1752 (by decide),nativeRow]; rfl
private def inc786 (k : Nat) : Increment k (st k 786) (st k 790) := by
  refine incMk (st k 787) (st k 788) (safeNative k 786 (by decide))
    (safeNative k 787 (by decide)) (safeNative k 788 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 786 (by decide),nativeRow]; rfl
  · rw [st_small k 787 (by decide),nativeRow]; rfl
  · rw [st_small k 787 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 788 (by decide),nativeRow]; rfl)
  · rw [st_small k 788 (by decide),nativeRow]; rfl
private def inc800 (k : Nat) : Increment k (st k 800) (st k 804) := by
  refine incMk (st k 801) (st k 802) (safeNative k 800 (by decide))
    (safeNative k 801 (by decide)) (safeNative k 802 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 800 (by decide),nativeRow]; rfl
  · rw [st_small k 801 (by decide),nativeRow]; rfl
  · rw [st_small k 801 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 802 (by decide),nativeRow]; rfl)
  · rw [st_small k 802 (by decide),nativeRow]; rfl
private def inc874 (k : Nat) : Increment k (st k 874) (st k 878) := by
  refine incMk (st k 875) (st k 876) (safeNative k 874 (by decide))
    (safeNative k 875 (by decide)) (safeNative k 876 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 874 (by decide),nativeRow]; rfl
  · rw [st_small k 875 (by decide),nativeRow]; rfl
  · rw [st_small k 875 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 876 (by decide),nativeRow]; rfl)
  · rw [st_small k 876 (by decide),nativeRow]; rfl
private def inc944 (k : Nat) : Increment k (st k 944) (st k 948) := by
  refine incMk (st k 945) (st k 946) (safeNative k 944 (by decide))
    (safeNative k 945 (by decide)) (safeNative k 946 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 944 (by decide),nativeRow]; rfl
  · rw [st_small k 945 (by decide),nativeRow]; rfl
  · rw [st_small k 945 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 946 (by decide),nativeRow]; rfl)
  · rw [st_small k 946 (by decide),nativeRow]; rfl
private def inc976 (k : Nat) : Increment k (st k 976) (st k 980) := by
  refine incMk (st k 977) (st k 978) (safeNative k 976 (by decide))
    (safeNative k 977 (by decide)) (safeNative k 978 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 976 (by decide),nativeRow]; rfl
  · rw [st_small k 977 (by decide),nativeRow]; rfl
  · rw [st_small k 977 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 978 (by decide),nativeRow]; rfl)
  · rw [st_small k 978 (by decide),nativeRow]; rfl
private def inc994 (k : Nat) : Increment k (st k 994) (st k 998) := by
  refine incMk (st k 995) (st k 996) (safeNative k 994 (by decide))
    (safeNative k 995 (by decide)) (safeNative k 996 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 994 (by decide),nativeRow]; rfl
  · rw [st_small k 995 (by decide),nativeRow]; rfl
  · rw [st_small k 995 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 996 (by decide),nativeRow]; rfl)
  · rw [st_small k 996 (by decide),nativeRow]; rfl
private def inc1012 (k : Nat) : Increment k (st k 1012) (st k 1016) := by
  refine incMk (st k 1013) (st k 1014) (safeNative k 1012 (by decide))
    (safeNative k 1013 (by decide)) (safeNative k 1014 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1012 (by decide),nativeRow]; rfl
  · rw [st_small k 1013 (by decide),nativeRow]; rfl
  · rw [st_small k 1013 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1014 (by decide),nativeRow]; rfl)
  · rw [st_small k 1014 (by decide),nativeRow]; rfl
private def inc1068 (k : Nat) : Increment k (st k 1068) (st k 1072) := by
  refine incMk (st k 1069) (st k 1070) (safeNative k 1068 (by decide))
    (safeNative k 1069 (by decide)) (safeNative k 1070 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1068 (by decide),nativeRow]; rfl
  · rw [st_small k 1069 (by decide),nativeRow]; rfl
  · rw [st_small k 1069 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1070 (by decide),nativeRow]; rfl)
  · rw [st_small k 1070 (by decide),nativeRow]; rfl
private def inc1124 (k : Nat) : Increment k (st k 1124) (st k 1128) := by
  refine incMk (st k 1125) (st k 1126) (safeNative k 1124 (by decide))
    (safeNative k 1125 (by decide)) (safeNative k 1126 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1124 (by decide),nativeRow]; rfl
  · rw [st_small k 1125 (by decide),nativeRow]; rfl
  · rw [st_small k 1125 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1126 (by decide),nativeRow]; rfl)
  · rw [st_small k 1126 (by decide),nativeRow]; rfl
private def inc1140 (k : Nat) : Increment k (st k 1140) (st k 1144) := by
  refine incMk (st k 1141) (st k 1142) (safeNative k 1140 (by decide))
    (safeNative k 1141 (by decide)) (safeNative k 1142 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1140 (by decide),nativeRow]; rfl
  · rw [st_small k 1141 (by decide),nativeRow]; rfl
  · rw [st_small k 1141 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1142 (by decide),nativeRow]; rfl)
  · rw [st_small k 1142 (by decide),nativeRow]; rfl
private def inc1160 (k : Nat) : Increment k (st k 1160) (st k 1164) := by
  refine incMk (st k 1161) (st k 1162) (safeNative k 1160 (by decide))
    (safeNative k 1161 (by decide)) (safeNative k 1162 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1160 (by decide),nativeRow]; rfl
  · rw [st_small k 1161 (by decide),nativeRow]; rfl
  · rw [st_small k 1161 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1162 (by decide),nativeRow]; rfl)
  · rw [st_small k 1162 (by decide),nativeRow]; rfl
private def inc1202 (k : Nat) : Increment k (st k 1202) (st k 1206) := by
  refine incMk (st k 1203) (st k 1204) (safeNative k 1202 (by decide))
    (safeNative k 1203 (by decide)) (safeNative k 1204 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1202 (by decide),nativeRow]; rfl
  · rw [st_small k 1203 (by decide),nativeRow]; rfl
  · rw [st_small k 1203 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1204 (by decide),nativeRow]; rfl)
  · rw [st_small k 1204 (by decide),nativeRow]; rfl
private def inc1223 (k : Nat) : Increment k (st k 1223) (st k 1227) := by
  refine incMk (st k 1224) (st k 1225) (safeNative k 1223 (by decide))
    (safeNative k 1224 (by decide)) (safeNative k 1225 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1223 (by decide),nativeRow]; rfl
  · rw [st_small k 1224 (by decide),nativeRow]; rfl
  · rw [st_small k 1224 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1225 (by decide),nativeRow]; rfl)
  · rw [st_small k 1225 (by decide),nativeRow]; rfl
private def inc1274 (k : Nat) : Increment k (st k 1274) (st k 1278) := by
  refine incMk (st k 1275) (st k 1276) (safeNative k 1274 (by decide))
    (safeNative k 1275 (by decide)) (safeNative k 1276 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1274 (by decide),nativeRow]; rfl
  · rw [st_small k 1275 (by decide),nativeRow]; rfl
  · rw [st_small k 1275 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1276 (by decide),nativeRow]; rfl)
  · rw [st_small k 1276 (by decide),nativeRow]; rfl
private def inc1305 (k : Nat) : Increment k (st k 1305) (st k 1309) := by
  refine incMk (st k 1306) (st k 1307) (safeNative k 1305 (by decide))
    (safeNative k 1306 (by decide)) (safeNative k 1307 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1305 (by decide),nativeRow]; rfl
  · rw [st_small k 1306 (by decide),nativeRow]; rfl
  · rw [st_small k 1306 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1307 (by decide),nativeRow]; rfl)
  · rw [st_small k 1307 (by decide),nativeRow]; rfl
private def inc1336 (k : Nat) : Increment k (st k 1336) (st k 1340) := by
  refine incMk (st k 1337) (st k 1338) (safeNative k 1336 (by decide))
    (safeNative k 1337 (by decide)) (safeNative k 1338 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1336 (by decide),nativeRow]; rfl
  · rw [st_small k 1337 (by decide),nativeRow]; rfl
  · rw [st_small k 1337 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1338 (by decide),nativeRow]; rfl)
  · rw [st_small k 1338 (by decide),nativeRow]; rfl
private def inc1350 (k : Nat) : Increment k (st k 1350) (st k 1354) := by
  refine incMk (st k 1351) (st k 1352) (safeNative k 1350 (by decide))
    (safeNative k 1351 (by decide)) (safeNative k 1352 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1350 (by decide),nativeRow]; rfl
  · rw [st_small k 1351 (by decide),nativeRow]; rfl
  · rw [st_small k 1351 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1352 (by decide),nativeRow]; rfl)
  · rw [st_small k 1352 (by decide),nativeRow]; rfl
private def inc1370 (k : Nat) : Increment k (st k 1370) (st k 1374) := by
  refine incMk (st k 1371) (st k 1372) (safeNative k 1370 (by decide))
    (safeNative k 1371 (by decide)) (safeNative k 1372 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [st_small k 1370 (by decide),nativeRow]; rfl
  · rw [st_small k 1371 (by decide),nativeRow]; rfl
  · rw [st_small k 1371 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [st_small k 1372 (by decide),nativeRow]; rfl)
  · rw [st_small k 1372 (by decide),nativeRow]; rfl
end FullIngressClosure
