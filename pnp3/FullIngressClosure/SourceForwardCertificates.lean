import FullIngressClosure.SourceForwardRound
import FullIngressClosure.SourceCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("FullIngressClosure.SourceForwardRound","FullIngressClosure","ForwardCode","ForwardCode"),
      ("FullIngressClosure.SourceForwardRound","FullIngressClosure","ForwardCode.mk","forwardMk"),
      ("FullIngressClosure.SourceEOF","FullIngressClosure","EOFCode","EOFCode"),
      ("FullIngressClosure.SourceEOF","FullIngressClosure","EOFCode.mk","eofMk"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","hole1559","hole1559"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","hole1599","hole1599"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","hole1691","hole1691"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","hole1753","hole1753"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","sourceReturn1627","sourceReturn1627"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","sourceReturn1651","sourceReturn1651"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","sourceReturn1799","sourceReturn1799"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","sourceReturn1827","sourceReturn1827"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","regReturn1856","regReturn1856"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1547","dec1547"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1555","dec1555"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1587","dec1587"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1595","dec1595"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1675","dec1675"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1687","dec1687"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1737","dec1737"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1749","dec1749"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel","Travel"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.right","trRight"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.left","trLeft"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.stay","trStay"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.nil","rrNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.next","rrNext"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.nil","rlNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.next","rlNext"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique forward source literal certificate {mod}/{key}: {found.map Prod.fst}"
private def eofCode (k : Nat) : EOFCode k (st k 1855) (st k 1977) := by
  exact eofMk (st k 1856) (safeNative k 1855 (by decide))
    (by rw [stSmall k 1855 (by decide),nativeRow]; rfl) (regReturn1856 k)
private def forward9_0 (k : Nat) : ForwardCode k 9 false
    (st k 1547) (st k 1547) (st k 1587) (st k 1583) (st k 1855) (st k 1977) := by
  exact forwardMk (st k 1551) (st k 1555) (st k 1559) (st k 2038)
    (st k 1581) (st k 1582) (st k 1627) (st k 1651)
    (dec1547 k) (trLeft (rlNext (safeNative k 1551 (by decide)) (safeNative k 1552 (by decide))
      (by rw [stSmall k 1551 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1552 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1552 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1553 (by decide)) (safeNative k 1554 (by decide))
      (by rw [stSmall k 1553 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1554 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1554 (by decide),nativeRow]; rfl) (rlNil 7 (st k 1555))))) (dec1555 k) (hole1559 k)
    (safeNative k 1581 (by decide)) (safeNative k 1582 (by decide))
    (by rw [stSmall k 1581 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1582 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1582 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1582 (by decide),nativeRow]; rfl)
    (sourceReturn1627 k) (sourceReturn1651 k) (eofCode k)
private def zero9_0 (k : Nat) : Travel k 9 11 (st k 1583) (st k 1675) :=
  (trRight (rrNext (safeNative k 1583 (by decide)) (safeNative k 1584 (by decide))
      (by rw [stSmall k 1583 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1584 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1584 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1585 (by decide)) (safeNative k 1586 (by decide))
      (by rw [stSmall k 1585 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1586 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1586 (by decide),nativeRow]; rfl) (rrNil 11 (st k 1675)))))
private def forward9_1 (k : Nat) : ForwardCode k 9 true
    (st k 1587) (st k 1547) (st k 1587) (st k 1623) (st k 1855) (st k 1977) := by
  exact forwardMk (st k 1591) (st k 1595) (st k 1599) (st k 2038)
    (st k 1621) (st k 1622) (st k 1627) (st k 1651)
    (dec1587 k) (trLeft (rlNext (safeNative k 1591 (by decide)) (safeNative k 1592 (by decide))
      (by rw [stSmall k 1591 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1592 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1592 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1593 (by decide)) (safeNative k 1594 (by decide))
      (by rw [stSmall k 1593 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1594 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1594 (by decide),nativeRow]; rfl) (rlNil 7 (st k 1595))))) (dec1595 k) (hole1599 k)
    (safeNative k 1621 (by decide)) (safeNative k 1622 (by decide))
    (by rw [stSmall k 1621 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1622 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1622 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1622 (by decide),nativeRow]; rfl)
    (sourceReturn1627 k) (sourceReturn1651 k) (eofCode k)
private def zero9_1 (k : Nat) : Travel k 9 11 (st k 1623) (st k 1737) :=
  (trRight (rrNext (safeNative k 1623 (by decide)) (safeNative k 1624 (by decide))
      (by rw [stSmall k 1623 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1624 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1624 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1625 (by decide)) (safeNative k 1626 (by decide))
      (by rw [stSmall k 1625 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1626 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1626 (by decide),nativeRow]; rfl) (rrNil 11 (st k 1737)))))
private def forward11_0 (k : Nat) : ForwardCode k 11 false
    (st k 1675) (st k 1675) (st k 1737) (st k 1715) (st k 1855) (st k 1977) := by
  exact forwardMk (st k 1679) (st k 1687) (st k 1691) (st k 2038)
    (st k 1713) (st k 1714) (st k 1799) (st k 1827)
    (dec1675 k) (trLeft (rlNext (safeNative k 1679 (by decide)) (safeNative k 1680 (by decide))
      (by rw [stSmall k 1679 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1680 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1680 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1681 (by decide)) (safeNative k 1682 (by decide))
      (by rw [stSmall k 1681 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1682 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1682 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1683 (by decide)) (safeNative k 1684 (by decide))
      (by rw [stSmall k 1683 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1684 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1684 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1685 (by decide)) (safeNative k 1686 (by decide))
      (by rw [stSmall k 1685 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1686 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1686 (by decide),nativeRow]; rfl) (rlNil 7 (st k 1687))))))) (dec1687 k) (hole1691 k)
    (safeNative k 1713 (by decide)) (safeNative k 1714 (by decide))
    (by rw [stSmall k 1713 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1714 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1714 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1714 (by decide),nativeRow]; rfl)
    (sourceReturn1799 k) (sourceReturn1827 k) (eofCode k)
private def zero11_0 (k : Nat) : Travel k 11 0 (st k 1715) (st k 1861) :=
  (trLeft (rlNext (safeNative k 1715 (by decide)) (safeNative k 1716 (by decide))
      (by rw [stSmall k 1715 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1716 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1716 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1717 (by decide)) (safeNative k 1718 (by decide))
      (by rw [stSmall k 1717 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1718 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1718 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1719 (by decide)) (safeNative k 1720 (by decide))
      (by rw [stSmall k 1719 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1720 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1720 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1721 (by decide)) (safeNative k 1722 (by decide))
      (by rw [stSmall k 1721 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1722 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1722 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1723 (by decide)) (safeNative k 1724 (by decide))
      (by rw [stSmall k 1723 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1724 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1724 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1725 (by decide)) (safeNative k 1726 (by decide))
      (by rw [stSmall k 1725 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1726 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1726 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1727 (by decide)) (safeNative k 1728 (by decide))
      (by rw [stSmall k 1727 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1728 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1728 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1729 (by decide)) (safeNative k 1730 (by decide))
      (by rw [stSmall k 1729 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1730 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1730 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1731 (by decide)) (safeNative k 1732 (by decide))
      (by rw [stSmall k 1731 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1732 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1732 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1733 (by decide)) (safeNative k 1734 (by decide))
      (by rw [stSmall k 1733 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1734 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1734 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1735 (by decide)) (safeNative k 1736 (by decide))
      (by rw [stSmall k 1735 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1736 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1736 (by decide),nativeRow]; rfl) (rlNil 0 (st k 1861))))))))))))))
private def forward11_1 (k : Nat) : ForwardCode k 11 true
    (st k 1737) (st k 1675) (st k 1737) (st k 1777) (st k 1855) (st k 1977) := by
  exact forwardMk (st k 1741) (st k 1749) (st k 1753) (st k 2038)
    (st k 1775) (st k 1776) (st k 1799) (st k 1827)
    (dec1737 k) (trLeft (rlNext (safeNative k 1741 (by decide)) (safeNative k 1742 (by decide))
      (by rw [stSmall k 1741 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1742 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1742 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1743 (by decide)) (safeNative k 1744 (by decide))
      (by rw [stSmall k 1743 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1744 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1744 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1745 (by decide)) (safeNative k 1746 (by decide))
      (by rw [stSmall k 1745 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1746 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1746 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1747 (by decide)) (safeNative k 1748 (by decide))
      (by rw [stSmall k 1747 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1748 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1748 (by decide),nativeRow]; rfl) (rlNil 7 (st k 1749))))))) (dec1749 k) (hole1753 k)
    (safeNative k 1775 (by decide)) (safeNative k 1776 (by decide))
    (by rw [stSmall k 1775 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1776 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1776 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1776 (by decide),nativeRow]; rfl)
    (sourceReturn1799 k) (sourceReturn1827 k) (eofCode k)
private def zero11_1 (k : Nat) : Travel k 11 0 (st k 1777) (st k 1919) :=
  (trLeft (rlNext (safeNative k 1777 (by decide)) (safeNative k 1778 (by decide))
      (by rw [stSmall k 1777 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1778 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1778 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1779 (by decide)) (safeNative k 1780 (by decide))
      (by rw [stSmall k 1779 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1780 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1780 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1781 (by decide)) (safeNative k 1782 (by decide))
      (by rw [stSmall k 1781 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1782 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1782 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1783 (by decide)) (safeNative k 1784 (by decide))
      (by rw [stSmall k 1783 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1784 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1784 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1785 (by decide)) (safeNative k 1786 (by decide))
      (by rw [stSmall k 1785 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1786 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1786 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1787 (by decide)) (safeNative k 1788 (by decide))
      (by rw [stSmall k 1787 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1788 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1788 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1789 (by decide)) (safeNative k 1790 (by decide))
      (by rw [stSmall k 1789 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1790 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1790 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1791 (by decide)) (safeNative k 1792 (by decide))
      (by rw [stSmall k 1791 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1792 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1792 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1793 (by decide)) (safeNative k 1794 (by decide))
      (by rw [stSmall k 1793 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1794 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1794 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1795 (by decide)) (safeNative k 1796 (by decide))
      (by rw [stSmall k 1795 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1796 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1796 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1797 (by decide)) (safeNative k 1798 (by decide))
      (by rw [stSmall k 1797 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1798 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1798 (by decide),nativeRow]; rfl) (rlNil 0 (st k 1919))))))))))))))
end FullIngressClosure
