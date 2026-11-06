import InputRead.Raw
import GammaSupport.Closure
namespace ConnectedRead
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Exact accepted-side first connected read with no extra physical-gamma guard.
This is not a serialized witness reader or a content verdict. -/
def Exact (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w = true →
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      (3 ≤ pr.2.n → ∃ (z T : Nat)
        (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m)
          (FixedRawLengthFence.allocation (pairLength a m))) (mode : Fin 3),
        2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        9+2*z ≤ a+m ∧
        T+pr.2.n+2+InputRead.readClock pr.2.n z (a+m-(9+2*z)) ≤ 144*(pairLength a m+1)^2 ∧
        (mode.val=2 ↔ 9+2*z=a+m) ∧
        (∀ hi : 9+2*z < a+m, InputRead.result mode=Fin.append x w ⟨9+2*z,hi⟩) ∧
        InputRead.rawMachine.run (T+pr.2.n+2+InputRead.readClock pr.2.n z (a+m-(9+2*z)))
          (initialConfig InputRead.rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
          FixedRawLengthFence.prefixed.seqEmbedRight InputRead.machine
            ⟨InputRead.ready mode,⟨a+m+2+z+pr.2.n+1,hR⟩,
              fun i => if i.val=9+2*z then none else
                Body.installedTape (FixedRawLengthFence.countdownTape
                  (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n)
                  (a+m+2+z) pr.2.n i⟩)
end ConnectedRead
