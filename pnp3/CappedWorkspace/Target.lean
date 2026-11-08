import SuffixCap.Raw
namespace CappedWorkspace.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- q201, before bitLength: assignment true; bank0 true; banks1..5 false. -/
def image (C : Nat → Option Bool) (L n F r : Nat) : Nat → Option Bool := fun i =>
  if L < i ∧ i < L+n+1 then some true else
  if (F+r+2 < i ∧ i < F+r+n+3) ∨
     (F+r+n+3 < i ∧ i < F+2*r+n+4) ∨
     (F+2*r+n+4 < i ∧ i < F+3*r+n+5) ∨
     (F+3*r+n+5 < i ∧ i < F+4*r+n+6) ∨
     (F+4*r+n+6 < i ∧ i < F+5*r+n+7) then some false else C i
def deadline (R : Nat) : Nat := 1048576*(R+1)^3
/-- Literal supported raw branch to first six-bank boundary; no arithmetic success premise. -/
def Raw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
       2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 →
       min (9+2*z+2^pr.2.n) (a+m) < a+m →
        ∃ (t : Nat) (hD : FixedRawLengthFence.fencePos (pairLength a m)+1 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ deadline (pairLength a m) ∧
          (∀ u, u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 201)) ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let T := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
          FixedRawLengthFence.fencePos (pairLength a m)+5*((a+m)-min (9+2*z+2^pr.2.n) (a+m))+pr.2.n+7 <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 201,⟨FixedRawLengthFence.fencePos (pairLength a m)+1,hD⟩,fun i =>
                image (SuffixCap.Target.image T (FixedRawLengthFence.fencePos (pairLength a m))
                  ((a+m)-min (9+2*z+2^pr.2.n) (a+m))) (a+m+z+2) pr.2.n
                  (FixedRawLengthFence.fencePos (pairLength a m))
                  ((a+m)-min (9+2*z+2^pr.2.n) (a+m)) i.val⟩)
end CappedWorkspace.Target
