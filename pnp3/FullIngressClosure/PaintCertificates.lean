import FullIngressClosure.Paint
import FullIngressClosure.Certificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [
      ("Rows","native_row","nativeRow"),("Certificates","st","st"),
      ("Certificates","st_small","stSmall"),("Certificates","safeNative","safeNative"),
      ("Paint","PaintCode","PaintCode"),("Paint","PaintCode.mk","paintMk")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.FullIngressClosure."++mod++".") && n.toString.endsWith (".FullIngressClosure."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique native paint certificate {mod}/{key}: {found.map Prod.fst}"
private def paint1176 (k : Nat) : PaintCode k (st k 1176) (st k 1179) true := by
  refine paintMk (st k 1177) (st k 1178) (safeNative k 1176 (by decide))
    (safeNative k 1177 (by decide)) (safeNative k 1178 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1176 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1177 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1177 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1178 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1178 (by decide),nativeRow]; rfl
private def paint1323 (k : Nat) : PaintCode k (st k 1323) (st k 1326) true := by
  refine paintMk (st k 1324) (st k 1325) (safeNative k 1323 (by decide))
    (safeNative k 1324 (by decide)) (safeNative k 1325 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1323 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1324 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1324 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1325 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1325 (by decide),nativeRow]; rfl
private def paint1879 (k : Nat) : PaintCode k (st k 1879) (st k 1882) false := by
  refine paintMk (st k 1880) (st k 1881) (safeNative k 1879 (by decide))
    (safeNative k 1880 (by decide)) (safeNative k 1881 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1879 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1880 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1880 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1881 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1881 (by decide),nativeRow]; rfl
private def paint1886 (k : Nat) : PaintCode k (st k 1886) (st k 1889) false := by
  refine paintMk (st k 1887) (st k 1888) (safeNative k 1886 (by decide))
    (safeNative k 1887 (by decide)) (safeNative k 1888 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1886 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1887 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1887 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1888 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1888 (by decide),nativeRow]; rfl
private def paint1891 (k : Nat) : PaintCode k (st k 1891) (st k 1894) true := by
  refine paintMk (st k 1892) (st k 1893) (safeNative k 1891 (by decide))
    (safeNative k 1892 (by decide)) (safeNative k 1893 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1891 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1892 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1892 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1893 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1893 (by decide),nativeRow]; rfl
private def paint1937 (k : Nat) : PaintCode k (st k 1937) (st k 1940) false := by
  refine paintMk (st k 1938) (st k 1939) (safeNative k 1937 (by decide))
    (safeNative k 1938 (by decide)) (safeNative k 1939 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1937 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1938 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1938 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1939 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1939 (by decide),nativeRow]; rfl
private def paint1944 (k : Nat) : PaintCode k (st k 1944) (st k 1947) false := by
  refine paintMk (st k 1945) (st k 1946) (safeNative k 1944 (by decide))
    (safeNative k 1945 (by decide)) (safeNative k 1946 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1944 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1945 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1945 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1946 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1946 (by decide),nativeRow]; rfl
private def paint1949 (k : Nat) : PaintCode k (st k 1949) (st k 1952) true := by
  refine paintMk (st k 1950) (st k 1951) (safeNative k 1949 (by decide))
    (safeNative k 1950 (by decide)) (safeNative k 1951 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1949 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1950 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1950 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1951 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1951 (by decide),nativeRow]; rfl
private def paint1995 (k : Nat) : PaintCode k (st k 1995) (st k 1998) false := by
  refine paintMk (st k 1996) (st k 1997) (safeNative k 1995 (by decide))
    (safeNative k 1996 (by decide)) (safeNative k 1997 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1995 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1996 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1996 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 1997 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1997 (by decide),nativeRow]; rfl
private def paint2002 (k : Nat) : PaintCode k (st k 2002) (st k 2005) false := by
  refine paintMk (st k 2003) (st k 2004) (safeNative k 2002 (by decide))
    (safeNative k 2003 (by decide)) (safeNative k 2004 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 2002 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 2003 (by decide),nativeRow]; rfl)
  · rw [stSmall k 2003 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 2004 (by decide),nativeRow]; rfl)
  · rw [stSmall k 2004 (by decide),nativeRow]; rfl
private def paint2007 (k : Nat) : PaintCode k (st k 2007) (st k 2010) true := by
  refine paintMk (st k 2008) (st k 2009) (safeNative k 2007 (by decide))
    (safeNative k 2008 (by decide)) (safeNative k 2009 (by decide)) ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 2007 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 2008 (by decide),nativeRow]; rfl)
  · rw [stSmall k 2008 (by decide),nativeRow]; rfl
  · intro old; cases old <;> (rw [stSmall k 2009 (by decide),nativeRow]; rfl)
  · rw [stSmall k 2009 (by decide),nativeRow]; rfl
end FullIngressClosure
