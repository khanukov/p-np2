import Cursor.Proof
namespace SuffixCap.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- COUNTED only: bank zero is true; no other bank has been installed. -/
def image (T : Nat → Option Bool) (F r : Nat) : Nat → Option Bool := fun i =>
  if F+2 ≤ i ∧ i < F+r+2 then some true else T i
def deadline (R : Nat) : Nat := 65536*(R+1)^2
/-- Full supported physical raw branch, at strict first arrival to live q98. -/
def Raw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
       2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 →
       min (9+2*z+2^pr.2.n) (a+m) < a+m →
        ∃ (t : Nat) (hS : a+m < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ deadline (pairLength a m) ∧
          (∀ u, u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.rReady k)) ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let T := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
          FixedRawLengthFence.fencePos (pairLength a m)+((a+m)-min (9+2*z+2^pr.2.n) (a+m))+2 <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.rReady k,⟨a+m,hS⟩,fun i => image T (FixedRawLengthFence.fencePos (pairLength a m))
                ((a+m)-min (9+2*z+2^pr.2.n) (a+m)) i.val⟩)
end SuffixCap.Target
