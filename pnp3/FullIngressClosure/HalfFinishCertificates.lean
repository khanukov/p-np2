import FullIngressClosure.HalfFinish
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("FullIngressClosure.HalfFinish","FullIngressClosure","FinishCode","FinishCode"),
      ("FullIngressClosure.HalfFinish","FullIngressClosure","FinishCode.mk","finishMk"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative"),
      ("FullIngressClosure.Certificates","FullIngressClosure","inc1223","inc1223"),
      ("FullIngressClosure.Certificates","FullIngressClosure","inc1305","inc1305"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.right","trRight"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.left","trLeft"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel.stay","trStay"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.nil","rrNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.next","rrNext"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.nil","rlNil"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.next","rlNext") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique positive-half certificate {mod}/{key}: {found.map Prod.fst}"
private def leftFinish (k : Nat) : FinishCode k 1 8 (st k 1220) (st k 1239) := by
  refine finishMk (st k 1221) (st k 1223) (st k 1227)
    (safeNative k 1220 (by decide)) ?_ ?_ (trRight (rrNext (safeNative k 1221 (by decide)) (safeNative k 1222 (by decide))
      (by rw [stSmall k 1221 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1222 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1222 (by decide),nativeRow]; rfl) (rrNil 2 (st k 1223)))) (inc1223 k) (trRight (rrNext (safeNative k 1227 (by decide)) (safeNative k 1228 (by decide))
      (by rw [stSmall k 1227 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1228 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1228 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1229 (by decide)) (safeNative k 1230 (by decide))
      (by rw [stSmall k 1229 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1230 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1230 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1231 (by decide)) (safeNative k 1232 (by decide))
      (by rw [stSmall k 1231 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1232 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1232 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1233 (by decide)) (safeNative k 1234 (by decide))
      (by rw [stSmall k 1233 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1234 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1234 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1235 (by decide)) (safeNative k 1236 (by decide))
      (by rw [stSmall k 1235 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1236 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1236 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1237 (by decide)) (safeNative k 1238 (by decide))
      (by rw [stSmall k 1237 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1238 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1238 (by decide),nativeRow]; rfl) (rrNil 8 (st k 1239)))))))))
  · intro bit; cases bit <;> (rw [stSmall k 1220 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1220 (by decide),nativeRow]; rfl
private def rightFinish (k : Nat) : FinishCode k 8 1 (st k 1292) (st k 1180) := by
  refine finishMk (st k 1293) (st k 1305) (st k 1309)
    (safeNative k 1292 (by decide)) ?_ ?_ (trLeft (rlNext (safeNative k 1293 (by decide)) (safeNative k 1294 (by decide))
      (by rw [stSmall k 1293 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1294 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1294 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1295 (by decide)) (safeNative k 1296 (by decide))
      (by rw [stSmall k 1295 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1296 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1296 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1297 (by decide)) (safeNative k 1298 (by decide))
      (by rw [stSmall k 1297 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1298 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1298 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1299 (by decide)) (safeNative k 1300 (by decide))
      (by rw [stSmall k 1299 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1300 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1300 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1301 (by decide)) (safeNative k 1302 (by decide))
      (by rw [stSmall k 1301 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1302 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1302 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1303 (by decide)) (safeNative k 1304 (by decide))
      (by rw [stSmall k 1303 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1304 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1304 (by decide),nativeRow]; rfl) (rlNil 2 (st k 1305))))))))) (inc1305 k) (trLeft (rlNext (safeNative k 1309 (by decide)) (safeNative k 1310 (by decide))
      (by rw [stSmall k 1309 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1310 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1310 (by decide),nativeRow]; rfl) (rlNil 1 (st k 1180))))
  · intro bit; cases bit <;> (rw [stSmall k 1292 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1292 (by decide),nativeRow]; rfl
end FullIngressClosure
