import Stream.Geometry
namespace Stream.RawTarget
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Frozen actual raw accepted-branch orbit. The physical next-field cursor is
exported; serialized witness offset M and the content verdict remain RED. -/
def AcceptedOrbit (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      (3 ≤ pr.2.n → ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 2048*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
          (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          rawMachine.run t (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight machine
              ⟨paid (Target.mode U (Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          rawMachine.run T (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight machine
              ⟨q (if Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩)
end Stream.RawTarget
