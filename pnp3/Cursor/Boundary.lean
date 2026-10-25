import Cursor.Target
import Cursor.Transport
namespace Cursor.Boundary
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Connected M closure restricted to a table-end already at virtual EOF.
The physical-suffix arithmetic branch of Target.Raw remains a separate RED target. -/
def EOF (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
       2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 →
       a+m ≤ 9+2*z+2^pr.2.n →
        ∃ (t : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ Target.deadline k (pairLength a m) ∧ a+m ≤ Target.M k pr.2.n z ∧
          padRead (Fin.append x w) (Target.M k pr.2.n z)=false ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let T := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
          (rawMachine k).run t (initialConfig (rawMachine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (machine k)
              ⟨mReady k ⟨2,by decide⟩,⟨a+m+z+pr.2.n+3,hH⟩,fun i => T i.val⟩)
end Cursor.Boundary
