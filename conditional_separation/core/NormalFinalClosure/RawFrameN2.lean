import NormalFinalClosure.RawFrame2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`NormalFinalClosure.Frame2,["GuardFrame"]),(`NormalFinalClosure.RawFrame2,["normal_done_frame"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `NormalFinalClosure) leaf
      let some ci:=e.find? name | throwError "Missing same-N raw frame API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing same-N frame owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong same-N frame owner"
      logInfo m!"same-original-N-raw-frame-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
/-- Proof-only name for the parent's ACTUAL reached whole tape. No machine
constructor or rawStep calls this definition; it performs no runtime install. -/
private def normalImage (k N : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (z n nodes used remaining : Nat) : Nat → Option Bool :=
  let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N;let Q:=2^n
  let r:=S-min (9+2*z+Q) S;let W:=Cursor.Target.W k n
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation N) x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) Q Q false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
    F r n (n^k+k) (bitLength W) 0 0 W
  PhysicalCallerClosure.callerImage I S z n F r (n^k+k) W (Cursor.Target.M k n z) 1
    (Pnp3.Core.vecOfNat n 0) nodes used remaining 0
private theorem frame_at_N (k N : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (same:pairLength a m=N)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (capacity:n < FixedRawLengthFence.capacity a m z)
    (arena:a+m+z+n+3+2^n < FixedRawLengthFence.fencePos N)
    (physical:min (9+2*z+2^n) (a+m) < a+m)
    (ell:bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (window:Cursor.Target.W k n ≤ a+m-min (9+2*z+2^n) (a+m))
    (nodes used remaining : Nat) :
    GuardFrame (a+m) z n (FixedRawLengthFence.fencePos N)
      (a+m-min (9+2*z+2^n) (a+m)) (Cursor.Target.W k n) (Fin.append x w)
      (normalImage k N x w z n nodes used remaining) := by
  subst N
  exact normal_done_frame k x w gamma header capacity arena physical ell window nodes used remaining
end NormalFinalClosure
