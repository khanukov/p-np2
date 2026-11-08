import Stream.RawTarget
namespace Stream.BodyTarget
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Raw orbit for every physically supported parsed body, including rejected
content. No relation=true premise supplies the physical row cutoff. -/
def Orbit (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
        ∃ (T : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          T ≤ 2048*(pairLength a m+1)^2 ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let F := FixedRawLengthFence.fencePos (pairLength a m)
          let cap := F-(a+m+z+pr.2.n+3)-1
          (∀ r, r < min (2^pr.2.n) cap → ∃ t, t ≤ T ∧
            rawMachine.run t (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
              FixedRawLengthFence.prefixed.seqEmbedRight machine
                ⟨paid (Target.mode U (Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                  fun i => Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
          (if 2^pr.2.n ≤ cap then
            ∃ hp : Target.cursor (9+2*z) (a+m) (2^pr.2.n) < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
              rawMachine.run T (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
                FixedRawLengthFence.prefixed.seqEmbedRight machine
                  ⟨q (if Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),⟨Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                    fun i => Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩
           else ∃ hF : F < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
              rawMachine.run T (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
                FixedRawLengthFence.prefixed.seqEmbedRight machine ⟨machine.reject,⟨F,hF⟩,
                  fun i => Target.image U (a+m) z pr.2.n (9+2*z) cap cap true i.val⟩))
end Stream.BodyTarget
