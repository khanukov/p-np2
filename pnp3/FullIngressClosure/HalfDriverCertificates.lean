import FullIngressClosure.HalfIteration
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("FullIngressClosure.HalfIteration","FullIngressClosure","HalveCode","HalveCode"),
      ("FullIngressClosure.HalfIteration","FullIngressClosure","HalveCode.mk","halveMk"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative"),
      ("FullIngressClosure.HalfCertificates","FullIngressClosure","leftFirst","leftFirst"),
      ("FullIngressClosure.HalfCertificates","FullIngressClosure","leftAgain","leftAgain"),
      ("FullIngressClosure.HalfCertificates","FullIngressClosure","rightFirst","rightFirst"),
      ("FullIngressClosure.HalfCertificates","FullIngressClosure","rightAgain","rightAgain"),
      ("FullIngressClosure.HalfFinishCertificates","FullIngressClosure","leftFinish","leftFinish"),
      ("FullIngressClosure.HalfFinishCertificates","FullIngressClosure","rightFinish","rightFinish") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique full-half certificate {mod}/{key}: {found.map Prod.fst}"
private def leftHalf (k : Nat) : HalveCode k 1 8
    (st k 1180) (st k 1184) (st k 1181) (st k 1185) (st k 1186) (st k 1220) (st k 1239) := by
  refine halveMk (leftFirst k) (leftAgain k) (leftFinish k)
    (safeNative k 1180 (by decide)) (safeNative k 1184 (by decide))
    (safeNative k 1181 (by decide)) (safeNative k 1185 (by decide)) (safeNative k 1186 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1180 (by decide),nativeRow]; rfl
  · rw [stSmall k 1181 (by decide),nativeRow]; rfl
  · rw [stSmall k 1181 (by decide),nativeRow]; rfl
  · rw [stSmall k 1184 (by decide),nativeRow]; rfl
  · rw [stSmall k 1185 (by decide),nativeRow]; rfl
  · rw [stSmall k 1185 (by decide),nativeRow]; rfl
  · rw [stSmall k 1186 (by decide),nativeRow]; rfl
  · rw [stSmall k 1186 (by decide),nativeRow]; rfl
  · rw [stSmall k 1185 (by decide),nativeRow]; rfl
private def rightHalf (k : Nat) : HalveCode k 8 1
    (st k 1239) (st k 1256) (st k 1240) (st k 1257) (st k 1258) (st k 1292) (st k 1180) := by
  refine halveMk (rightFirst k) (rightAgain k) (rightFinish k)
    (safeNative k 1239 (by decide)) (safeNative k 1256 (by decide))
    (safeNative k 1240 (by decide)) (safeNative k 1257 (by decide)) (safeNative k 1258 (by decide))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stSmall k 1239 (by decide),nativeRow]; rfl
  · rw [stSmall k 1240 (by decide),nativeRow]; rfl
  · rw [stSmall k 1240 (by decide),nativeRow]; rfl
  · rw [stSmall k 1256 (by decide),nativeRow]; rfl
  · rw [stSmall k 1257 (by decide),nativeRow]; rfl
  · rw [stSmall k 1257 (by decide),nativeRow]; rfl
  · rw [stSmall k 1258 (by decide),nativeRow]; rfl
  · rw [stSmall k 1258 (by decide),nativeRow]; rfl
  · rw [stSmall k 1257 (by decide),nativeRow]; rfl
end FullIngressClosure
