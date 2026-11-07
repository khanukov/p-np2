import AllArityCursor.Surface
import SuffixCap.Kernel
namespace AllArityCounted.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Same concrete producer288/Cursor family, every accepted arity, actual tape.
Physical arrival is FIRST COUNTED. EOF claims an executed endpoint, not firstness. -/
def AcceptedRaw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z t : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        t ≤ 4096*(pairLength a m+1)^2 ∧
        let S := a+m
        let F := FixedRawLengthFence.fencePos (pairLength a m)
        let Q := 2^pr.2.n
        let U := Body.extend (Body.installedTape (SmallIngress.prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (S+z+2) pr.2.n)
        let V := Stream.Target.image U S z pr.2.n (9+2*z) Q Q false
        let p := min (9+2*z+Q) S
        let r := S-p
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        ∃ hp : p < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ ∧
          (∀ u, u < t → ((AllArityCursor.machine k).run u c).state.val < 352) ∧
          (p < S → ∃ hS : S < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
            F+r+2 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
            t+(2+r*(2*(F-p)+6)) ≤ 65536*(pairLength a m+1)^2 ∧
            (∀ u, u < t+(2+r*(2*(F-p)+6)) → ((AllArityCursor.machine k).run u c).state≠
              SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k)) ∧
            (AllArityCursor.machine k).run (t+(2+r*(2*(F-p)+6))) c=
              SmallIngress.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.rReady k,⟨S,hS⟩,fun i => SuffixCap.Target.image V F r i.val⟩ ∧
            (∀ u, u ≤ t+(2+r*(2*(F-p)+6)) →
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject)) ∧
          (p=S → t+(z+pr.2.n+5) ≤ 65536*(pairLength a m+1)^2 ∧
            S ≤ Cursor.Target.M k pr.2.n z ∧
            padRead (Fin.append x w) (Cursor.Target.M k pr.2.n z)=false ∧
            (AllArityCursor.machine k).run (t+(z+pr.2.n+5)) c=
              SmallIngress.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+pr.2.n+3,hH⟩,fun i => V i.val⟩ ∧
            (∀ u, u ≤ t+(z+pr.2.n+5) →
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject))
end AllArityCounted.Target
