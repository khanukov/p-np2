import FullIngressClosure.SourceBackRound
import FullIngressClosure.SourceCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("FullIngressClosure.SourceBackRound","FullIngressClosure","BackCode","BackCode"),
      ("FullIngressClosure.SourceBackRound","FullIngressClosure","BackCode.mk","backMk"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","hole1393","hole1393"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","hole1429","hole1429"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","hole1465","hole1465"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","sourceReturn1495","sourceReturn1495"),
      ("FullIngressClosure.SourceCertificates","FullIngressClosure","sourceReturn1521","sourceReturn1521"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1389","dec1389"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1425","dec1425"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1461","dec1461"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel","Travel"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.left","trLeft"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.nil","rlNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.next","rlNext") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique backward-round literal certificate {mod}/{key}: {found.map Prod.fst}"
private def back0 (k : Nat) : BackCode k (some false) (st k 1389) (st k 1389) (st k 1425) (st k 1423) := by
  exact backMk (st k 1393) (st k 1421) (st k 1422) (st k 1495) (st k 1521)
    (dec1389 k) (hole1393 k) (safeNative k 1421 (by decide)) (safeNative k 1422 (by decide))
    (by rw [stSmall k 1421 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1422 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1422 (by decide),nativeRow]; rfl)
    (sourceReturn1495 k) (sourceReturn1521 k)
private def back1 (k : Nat) : BackCode k (some true) (st k 1425) (st k 1389) (st k 1425) (st k 1459) := by
  exact backMk (st k 1429) (st k 1457) (st k 1458) (st k 1495) (st k 1521)
    (dec1425 k) (hole1429 k) (safeNative k 1457 (by decide)) (safeNative k 1458 (by decide))
    (by rw [stSmall k 1457 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1458 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1458 (by decide),nativeRow]; rfl)
    (sourceReturn1495 k) (sourceReturn1521 k)
private def back2 (k : Nat) : BackCode k none (st k 1461) (st k 1389) (st k 1425) (st k 1494) := by
  exact backMk (st k 1465) (st k 1492) (st k 1493) (st k 1495) (st k 1521)
    (dec1461 k) (hole1465 k) (safeNative k 1492 (by decide)) (safeNative k 1493 (by decide))
    (by rw [stSmall k 1492 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1493 (by decide),nativeRow]; rfl)
    (by rw [stSmall k 1493 (by decide),nativeRow]; rfl)
    (sourceReturn1495 k) (sourceReturn1521 k)
private def backExit0 (k : Nat) : Travel k 10 9 (st k 1423) (st k 1547) :=
  trLeft (rlNext (safeNative k 1423 (by decide)) (safeNative k 1424 (by decide))
    (by rw [stSmall k 1423 (by decide),nativeRow]; rfl)
    (by intro bit; cases bit <;> (rw [stSmall k 1424 (by decide),nativeRow]; rfl))
    (by rw [stSmall k 1424 (by decide),nativeRow]; rfl) (rlNil 9 (st k 1547)))
private def backExit1 (k : Nat) : Travel k 10 9 (st k 1459) (st k 1587) :=
  trLeft (rlNext (safeNative k 1459 (by decide)) (safeNative k 1460 (by decide))
    (by rw [stSmall k 1459 (by decide),nativeRow]; rfl)
    (by intro bit; cases bit <;> (rw [stSmall k 1460 (by decide),nativeRow]; rfl))
    (by rw [stSmall k 1460 (by decide),nativeRow]; rfl) (rlNil 9 (st k 1587)))
end FullIngressClosure
