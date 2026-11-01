import NormalFinalClosure.FinalFrame2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
open Pnp4.AlgorithmsToLowerBounds PairEncoding
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`RawCallerClosure.Frame,`RawCallerClosure,["normal_layout"]),
    (`NormalFinalClosure.FinalFrame2,`NormalFinalClosure,["rows_done_frame"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["GuardFrame"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact raw-to-final-frame API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing raw final-frame owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong raw final-frame owner"
      logInfo m!"same-raw-final-frame-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
/-- All static guard premises are derived from the SAME normal raw branch and
its exact caller image; no new support/scratch/accepted hypothesis is added. -/
private theorem normal_done_frame (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (capacity:n < FixedRawLengthFence.capacity a m z)
    (arena:a+m+z+n+3+2^n < FixedRawLengthFence.fencePos (pairLength a m))
    (physical:min (9+2*z+2^n) (a+m) < a+m)
    (ell:bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (window:Cursor.Target.W k n ≤ a+m-min (9+2*z+2^n) (a+m))
    (nodes used remaining : Nat) :
    let R:=pairLength a m;let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos R
    let Q:=2^n;let r:=S-min (9+2*z+Q) S;let W:=Cursor.Target.W k n
    let M:=Cursor.Target.M k n z;let B0:=FixedRawLengthFence.allocation R
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) Q Q false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
      F r n (n^k+k) (bitLength W) 0 0 W
    GuardFrame S z n F r W (Fin.append x w)
      (PhysicalCallerClosure.callerImage I S z n F r (n^k+k) W M 1 (Pnp3.Core.vecOfNat n 0) nodes used remaining 0) := by
  intro R S L F Q r W M B0 U V X Y Z I
  have layout:=normal_layout k x w gamma header capacity arena physical ell window
  have pSource:9+2*z ≤ S-r:=by
    have q:=Nat.two_pow_pos n
    have pEq:min (9+2*z+2^n) (a+m)=9+2*z+2^n:=Nat.min_eq_left (by omega)
    dsimp only [r,S,Q]
    rw [pEq]
    omega
  exact rows_done_frame layout pSource nodes used remaining 0 (Pnp3.Core.vecOfNat n 0)
end NormalFinalClosure
