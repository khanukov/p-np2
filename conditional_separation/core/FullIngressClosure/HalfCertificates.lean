import Complexity.PrivateInterfaceLookupResolvedHalving
import FullIngressClosure.HalfPair
import FullIngressClosure.Certificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateHalving.bindings `FullIngressClosure.HalfCertificates
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated halving identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private structure EmptyCode (k a : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  scan : Fin (BodyIngress.machine k).stateCount
  back : Fin (BodyIngress.machine k).stateCount
  exit : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  safeScan : Safe k scan
  safeBack : Safe k back
  enter : (BodyIngress.machine k).step entry none=(scan,none,.right)
  pass : (BodyIngress.machine k).step scan (some false)=(scan,some false,.right)
  stop : (BodyIngress.machine k).step scan none=(back,none,.left)
  retreat : ∀ bit,(BodyIngress.machine k).step back (some bit)=(back,some bit,.left)
  done : (BodyIngress.machine k).step back none=(exit,none,.stay)
  finish : Travel k a 1 exit out
private theorem empty_half {k lo P D a entry out} (code : EmptyCode k a entry out)
    (T : Nat → Option Bool) (grid : Grid D T) (ha : a < 12) (w : Nat)
    (len : D (a+1)=D a+w+1) (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (empty : BankUnary D T a 0) :
    ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t (pNode entry (D a) T) (pNode out (D 1) T) := by
  have low:=lower.trans (gridMono grid 0 a (Nat.zero_le a) (by omega))
  have high : D a+w+1 ≤ P:=by rw [← len]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry code.scan (D a) (D a+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2 ⟨low,by omega⟩ ⟨by omega,by omega⟩
    (by rw [gridBlank grid a (by omega)]; exact code.enter) rfl
  have cell (i : Nat) (il : D a < i) (iu : i < D a+w+1) : T i=some false := by
    rw [empty i il (by rwa [len]),decide_eq_false (by omega)]
  have scan:=pSweepR (k:=k) (lo:=lo) (hi:=P) code.scan T (D a+1) w (by omega) (by omega)
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2 (by
      intro i il iu
      rw [cell i (by omega) (by omega)]
      exact code.pass)
  rw [show D a+1+w=D a+w+1 by omega] at scan
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.scan code.back (D a+w+1) (D a+w) T .left
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2 ⟨by omega,high⟩ ⟨by omega,by omega⟩
    (by rw [← len,gridBlank grid (a+1) (by omega)]; exact code.stop) (by simp [dest])
  have back:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.back T (D a) w low (by omega)
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 (by
      intro i il iu
      rw [cell i il (by omega)]
      exact code.retreat false)
  have done:=pKeep (k:=k) (lo:=lo) (hi:=P) code.back code.exit (D a) (D a) T .stay
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 ⟨low,by omega⟩ ⟨low,by omega⟩
    (by rw [gridBlank grid a (by omega)]; exact code.done) rfl
  obtain ⟨t,price,finish⟩:=travel code.finish grid (by omega) (by decide) lower upper
  have path:=pAppend first (pAppend scan (pAppend stop (pAppend back (pAppend done finish))))
  refine ⟨_,?_,path⟩
  omega
private def leftEmpty (k : Nat) : EmptyCode k 1 (st k 1180) (st k 1311) := by
  refine EmptyCode.mk (st k 1181) (st k 1182) (st k 1183)
    (safeNative k 1180 (by decide)) (safeNative k 1181 (by decide)) (safeNative k 1182 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1180 (by decide),nativeRow]; rfl
  · rw [stSmall k 1181 (by decide),nativeRow]; rfl
  · rw [stSmall k 1181 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [stSmall k 1182 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1182 (by decide),nativeRow]; rfl
  · exact (trStay (safeNative k 1183 (by decide)) (by rw [stSmall k 1183 (by decide),nativeRow]; rfl))
private def rightEmpty (k : Nat) : EmptyCode k 8 (st k 1239) (st k 1311) := by
  refine EmptyCode.mk (st k 1240) (st k 1241) (st k 1242)
    (safeNative k 1239 (by decide)) (safeNative k 1240 (by decide)) (safeNative k 1241 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1239 (by decide),nativeRow]; rfl
  · rw [stSmall k 1240 (by decide),nativeRow]; rfl
  · rw [stSmall k 1240 (by decide),nativeRow]; rfl
  · intro bit; cases bit <;> (rw [stSmall k 1241 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1241 (by decide),nativeRow]; rfl
  · exact (trLeft (rlNext (safeNative k 1242 (by decide)) (safeNative k 1243 (by decide))
      (by rw [stSmall k 1242 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1243 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1243 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1244 (by decide)) (safeNative k 1245 (by decide))
      (by rw [stSmall k 1244 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1245 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1245 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1246 (by decide)) (safeNative k 1247 (by decide))
      (by rw [stSmall k 1246 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1247 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1247 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1248 (by decide)) (safeNative k 1249 (by decide))
      (by rw [stSmall k 1248 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1249 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1249 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1250 (by decide)) (safeNative k 1251 (by decide))
      (by rw [stSmall k 1250 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1251 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1251 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1252 (by decide)) (safeNative k 1253 (by decide))
      (by rw [stSmall k 1252 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1253 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1253 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1254 (by decide)) (safeNative k 1255 (by decide))
      (by rw [stSmall k 1254 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1255 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1255 (by decide),nativeRow]; rfl) (rlNil 1 (st k 1311))))))))))
private def leftOut (k : Nat) : Travel k 1 8 (st k 1188) (st k 1202) :=
  (trRight (rrNext (safeNative k 1188 (by decide)) (safeNative k 1189 (by decide))
      (by rw [stSmall k 1188 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1189 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1189 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1190 (by decide)) (safeNative k 1191 (by decide))
      (by rw [stSmall k 1190 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1191 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1191 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1192 (by decide)) (safeNative k 1193 (by decide))
      (by rw [stSmall k 1192 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1193 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1193 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1194 (by decide)) (safeNative k 1195 (by decide))
      (by rw [stSmall k 1194 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1195 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1195 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1196 (by decide)) (safeNative k 1197 (by decide))
      (by rw [stSmall k 1196 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1197 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1197 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1198 (by decide)) (safeNative k 1199 (by decide))
      (by rw [stSmall k 1198 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1199 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1199 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1200 (by decide)) (safeNative k 1201 (by decide))
      (by rw [stSmall k 1200 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1201 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1201 (by decide),nativeRow]; rfl) (rrNil 8 (st k 1202))))))))))
private def leftBack (k : Nat) : Travel k 8 1 (st k 1206) (st k 1184) :=
  (trLeft (rlNext (safeNative k 1206 (by decide)) (safeNative k 1207 (by decide))
      (by rw [stSmall k 1206 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1207 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1207 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1208 (by decide)) (safeNative k 1209 (by decide))
      (by rw [stSmall k 1208 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1209 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1209 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1210 (by decide)) (safeNative k 1211 (by decide))
      (by rw [stSmall k 1210 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1211 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1211 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1212 (by decide)) (safeNative k 1213 (by decide))
      (by rw [stSmall k 1212 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1213 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1213 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1214 (by decide)) (safeNative k 1215 (by decide))
      (by rw [stSmall k 1214 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1215 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1215 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1216 (by decide)) (safeNative k 1217 (by decide))
      (by rw [stSmall k 1216 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1217 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1217 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1218 (by decide)) (safeNative k 1219 (by decide))
      (by rw [stSmall k 1218 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1219 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1219 (by decide),nativeRow]; rfl) (rlNil 1 (st k 1184))))))))))
private def leftFirst (k : Nat) : PairCode k 1 8 (st k 1180) (st k 1184) := by
  refine pairMk (st k 1181) (st k 1186) (st k 1187) (st k 1188) (st k 1202) (st k 1206)
    (safeNative k 1180 (by decide)) (safeNative k 1181 (by decide))
    (safeNative k 1186 (by decide)) (safeNative k 1187 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ (leftOut k) (inc1202 k) (leftBack k)
  · rw [stSmall k 1180 (by decide),nativeRow]; rfl
  · rw [stSmall k 1181 (by decide),nativeRow]; rfl
  · rw [stSmall k 1181 (by decide),nativeRow]; rfl
  · rw [stSmall k 1186 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 1187 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1187 (by decide),nativeRow]; rfl
private def leftAgain (k : Nat) : PairCode k 1 8 (st k 1184) (st k 1184) := by
  refine pairMk (st k 1185) (st k 1186) (st k 1187) (st k 1188) (st k 1202) (st k 1206)
    (safeNative k 1184 (by decide)) (safeNative k 1185 (by decide))
    (safeNative k 1186 (by decide)) (safeNative k 1187 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ (leftOut k) (inc1202 k) (leftBack k)
  · rw [stSmall k 1184 (by decide),nativeRow]; rfl
  · rw [stSmall k 1185 (by decide),nativeRow]; rfl
  · rw [stSmall k 1185 (by decide),nativeRow]; rfl
  · rw [stSmall k 1186 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 1187 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1187 (by decide),nativeRow]; rfl
private def rightOut (k : Nat) : Travel k 8 1 (st k 1260) (st k 1274) :=
  (trLeft (rlNext (safeNative k 1260 (by decide)) (safeNative k 1261 (by decide))
      (by rw [stSmall k 1260 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1261 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1261 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1262 (by decide)) (safeNative k 1263 (by decide))
      (by rw [stSmall k 1262 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1263 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1263 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1264 (by decide)) (safeNative k 1265 (by decide))
      (by rw [stSmall k 1264 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1265 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1265 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1266 (by decide)) (safeNative k 1267 (by decide))
      (by rw [stSmall k 1266 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1267 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1267 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1268 (by decide)) (safeNative k 1269 (by decide))
      (by rw [stSmall k 1268 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1269 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1269 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1270 (by decide)) (safeNative k 1271 (by decide))
      (by rw [stSmall k 1270 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1271 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1271 (by decide),nativeRow]; rfl) (rlNext (safeNative k 1272 (by decide)) (safeNative k 1273 (by decide))
      (by rw [stSmall k 1272 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1273 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1273 (by decide),nativeRow]; rfl) (rlNil 1 (st k 1274))))))))))
private def rightBack (k : Nat) : Travel k 1 8 (st k 1278) (st k 1256) :=
  (trRight (rrNext (safeNative k 1278 (by decide)) (safeNative k 1279 (by decide))
      (by rw [stSmall k 1278 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1279 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1279 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1280 (by decide)) (safeNative k 1281 (by decide))
      (by rw [stSmall k 1280 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1281 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1281 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1282 (by decide)) (safeNative k 1283 (by decide))
      (by rw [stSmall k 1282 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1283 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1283 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1284 (by decide)) (safeNative k 1285 (by decide))
      (by rw [stSmall k 1284 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1285 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1285 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1286 (by decide)) (safeNative k 1287 (by decide))
      (by rw [stSmall k 1286 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1287 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1287 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1288 (by decide)) (safeNative k 1289 (by decide))
      (by rw [stSmall k 1288 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1289 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1289 (by decide),nativeRow]; rfl) (rrNext (safeNative k 1290 (by decide)) (safeNative k 1291 (by decide))
      (by rw [stSmall k 1290 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 1291 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 1291 (by decide),nativeRow]; rfl) (rrNil 8 (st k 1256))))))))))
private def rightFirst (k : Nat) : PairCode k 8 1 (st k 1239) (st k 1256) := by
  refine pairMk (st k 1240) (st k 1258) (st k 1259) (st k 1260) (st k 1274) (st k 1278)
    (safeNative k 1239 (by decide)) (safeNative k 1240 (by decide))
    (safeNative k 1258 (by decide)) (safeNative k 1259 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ (rightOut k) (inc1274 k) (rightBack k)
  · rw [stSmall k 1239 (by decide),nativeRow]; rfl
  · rw [stSmall k 1240 (by decide),nativeRow]; rfl
  · rw [stSmall k 1240 (by decide),nativeRow]; rfl
  · rw [stSmall k 1258 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 1259 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1259 (by decide),nativeRow]; rfl
private def rightAgain (k : Nat) : PairCode k 8 1 (st k 1256) (st k 1256) := by
  refine pairMk (st k 1257) (st k 1258) (st k 1259) (st k 1260) (st k 1274) (st k 1278)
    (safeNative k 1256 (by decide)) (safeNative k 1257 (by decide))
    (safeNative k 1258 (by decide)) (safeNative k 1259 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ (rightOut k) (inc1274 k) (rightBack k)
  · rw [stSmall k 1256 (by decide),nativeRow]; rfl
  · rw [stSmall k 1257 (by decide),nativeRow]; rfl
  · rw [stSmall k 1257 (by decide),nativeRow]; rfl
  · rw [stSmall k 1258 (by decide),nativeRow]; rfl
  · intro value; cases value <;> (rw [stSmall k 1259 (by decide),nativeRow]; rfl)
  · rw [stSmall k 1259 (by decide),nativeRow]; rfl
end FullIngressClosure
