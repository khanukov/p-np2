import FullIngressClosure.FinishStage
import FullIngressClosure.SourceCertificates
import FullIngressClosure.PaintCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("FullIngressClosure.FinishStage","FullIngressClosure","FinishStageCode","FinishStageCode"),
      ("FullIngressClosure.FinishStage","FullIngressClosure","FinishStageCode.mk","finishStageMk"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.right","trRight"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.left","trLeft"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.stay","trStay"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.nil","rrNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.next","rrNext"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.nil","rlNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.next","rlNext"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1879","paint1879"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1886","paint1886"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1891","paint1891"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1937","paint1937"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1944","paint1944"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1949","paint1949"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint1995","paint1995"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint2002","paint2002"),
      ("FullIngressClosure.PaintCertificates","FullIngressClosure","paint2007","paint2007"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","toH1894","toH1894"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","toH1952","toH1952"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","toH2010","toH2010") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique literal final BODY-entry certificate {mod}/{key}: {found.map Prod.fst}"
private def finish0 (k : Nat) : FinishStageCode k ⟨0,by decide⟩ (st k 1861) := by
  exact finishStageMk (st k 1879) (st k 1882) (st k 1886) (st k 1889)
    (st k 1891) (st k 1894) (st k 1918)
    (trRight (rrNext (safeNative k 1861 (by decide)) (safeNative k 1862 (by decide))
      (by rw [stSmall k 1861 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1862 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1862 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1863 (by decide)) (safeNative k 1864 (by decide))
      (by rw [stSmall k 1863 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1864 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1864 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1865 (by decide)) (safeNative k 1866 (by decide))
      (by rw [stSmall k 1865 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1866 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1866 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1867 (by decide)) (safeNative k 1868 (by decide))
      (by rw [stSmall k 1867 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1868 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1868 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1869 (by decide)) (safeNative k 1870 (by decide))
      (by rw [stSmall k 1869 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1870 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1870 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1871 (by decide)) (safeNative k 1872 (by decide))
      (by rw [stSmall k 1871 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1872 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1872 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1873 (by decide)) (safeNative k 1874 (by decide))
      (by rw [stSmall k 1873 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1874 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1874 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1875 (by decide)) (safeNative k 1876 (by decide))
      (by rw [stSmall k 1875 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1876 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1876 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1877 (by decide)) (safeNative k 1878 (by decide))
      (by rw [stSmall k 1877 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1878 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1878 (by decide),nativeRow]; rfl) (rrNil 9 (st k 1879)))))))))))) (paint1879 k) (trRight (rrNext (safeNative k 1882 (by decide)) (safeNative k 1883 (by decide))
      (by rw [stSmall k 1882 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1883 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1883 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1884 (by decide)) (safeNative k 1885 (by decide))
      (by rw [stSmall k 1884 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1885 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1885 (by decide),nativeRow]; rfl) (rrNil 11 (st k 1886))))) (paint1886 k) (trLeft (rlNext (safeNative k 1889 (by decide)) (safeNative k 1890 (by decide))
      (by rw [stSmall k 1889 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1890 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1890 (by decide),nativeRow]; rfl) (rlNil 10 (st k 1891)))) (paint1891 k)
    (toH1894 k) (safeNative k 1918 (by decide))
    (by rw [stSmall k 1918 (by decide),nativeRow]; rfl)
private def finish1 (k : Nat) : FinishStageCode k ⟨1,by decide⟩ (st k 1919) := by
  exact finishStageMk (st k 1937) (st k 1940) (st k 1944) (st k 1947)
    (st k 1949) (st k 1952) (st k 1976)
    (trRight (rrNext (safeNative k 1919 (by decide)) (safeNative k 1920 (by decide))
      (by rw [stSmall k 1919 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1920 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1920 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1921 (by decide)) (safeNative k 1922 (by decide))
      (by rw [stSmall k 1921 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1922 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1922 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1923 (by decide)) (safeNative k 1924 (by decide))
      (by rw [stSmall k 1923 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1924 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1924 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1925 (by decide)) (safeNative k 1926 (by decide))
      (by rw [stSmall k 1925 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1926 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1926 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1927 (by decide)) (safeNative k 1928 (by decide))
      (by rw [stSmall k 1927 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1928 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1928 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1929 (by decide)) (safeNative k 1930 (by decide))
      (by rw [stSmall k 1929 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1930 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1930 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1931 (by decide)) (safeNative k 1932 (by decide))
      (by rw [stSmall k 1931 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1932 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1932 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1933 (by decide)) (safeNative k 1934 (by decide))
      (by rw [stSmall k 1933 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1934 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1934 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1935 (by decide)) (safeNative k 1936 (by decide))
      (by rw [stSmall k 1935 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1936 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1936 (by decide),nativeRow]; rfl) (rrNil 9 (st k 1937)))))))))))) (paint1937 k) (trRight (rrNext (safeNative k 1940 (by decide)) (safeNative k 1941 (by decide))
      (by rw [stSmall k 1940 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1941 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1941 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1942 (by decide)) (safeNative k 1943 (by decide))
      (by rw [stSmall k 1942 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1943 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1943 (by decide),nativeRow]; rfl) (rrNil 11 (st k 1944))))) (paint1944 k) (trLeft (rlNext (safeNative k 1947 (by decide)) (safeNative k 1948 (by decide))
      (by rw [stSmall k 1947 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1948 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1948 (by decide),nativeRow]; rfl) (rlNil 10 (st k 1949)))) (paint1949 k)
    (toH1952 k) (safeNative k 1976 (by decide))
    (by rw [stSmall k 1976 (by decide),nativeRow]; rfl)
private def finish2 (k : Nat) : FinishStageCode k ⟨2,by decide⟩ (st k 1977) := by
  exact finishStageMk (st k 1995) (st k 1998) (st k 2002) (st k 2005)
    (st k 2007) (st k 2010) (st k 2034)
    (trRight (rrNext (safeNative k 1977 (by decide)) (safeNative k 1978 (by decide))
      (by rw [stSmall k 1977 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1978 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1978 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1979 (by decide)) (safeNative k 1980 (by decide))
      (by rw [stSmall k 1979 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1980 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1980 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1981 (by decide)) (safeNative k 1982 (by decide))
      (by rw [stSmall k 1981 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1982 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1982 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1983 (by decide)) (safeNative k 1984 (by decide))
      (by rw [stSmall k 1983 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1984 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1984 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1985 (by decide)) (safeNative k 1986 (by decide))
      (by rw [stSmall k 1985 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1986 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1986 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1987 (by decide)) (safeNative k 1988 (by decide))
      (by rw [stSmall k 1987 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1988 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1988 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1989 (by decide)) (safeNative k 1990 (by decide))
      (by rw [stSmall k 1989 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1990 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1990 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1991 (by decide)) (safeNative k 1992 (by decide))
      (by rw [stSmall k 1991 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1992 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1992 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1993 (by decide)) (safeNative k 1994 (by decide))
      (by rw [stSmall k 1993 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1994 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1994 (by decide),nativeRow]; rfl) (rrNil 9 (st k 1995)))))))))))) (paint1995 k) (trRight (rrNext (safeNative k 1998 (by decide)) (safeNative k 1999 (by decide))
      (by rw [stSmall k 1998 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1999 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1999 (by decide),nativeRow]; rfl) (rrNext (safeNative k 2000 (by decide)) (safeNative k 2001 (by decide))
      (by rw [stSmall k 2000 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 2001 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 2001 (by decide),nativeRow]; rfl) (rrNil 11 (st k 2002))))) (paint2002 k) (trLeft (rlNext (safeNative k 2005 (by decide)) (safeNative k 2006 (by decide))
      (by rw [stSmall k 2005 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 2006 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 2006 (by decide),nativeRow]; rfl) (rlNil 10 (st k 2007)))) (paint2007 k)
    (toH2010 k) (safeNative k 2034 (by decide))
    (by rw [stSmall k 2034 (by decide),nativeRow]; rfl)
private def finishState (k : Nat) (mode : Fin 3) : Fin (BodyIngress.machine k).stateCount :=
  st k (1861+58*mode.val)
private def finishCases (k : Nat) (mode : Fin 3) : FinishStageCode k mode (finishState k mode) := by
  refine Fin.cases (finish0 k) ?_ mode
  intro second
  refine Fin.cases (finish1 k) ?_ second
  intro third
  refine Fin.cases (finish2 k) ?_ third
  intro impossible
  exact Fin.elim0 impossible
end FullIngressClosure
