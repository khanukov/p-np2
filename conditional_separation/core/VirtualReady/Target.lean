import AllArityBitLength.Raw
import IngressRepair.Runtime
namespace VirtualReady.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Accepted raw seed/EOF plus actually executed bitLength-overflow cleanup, unchanged table/allocation. -/
def AcceptedVirtual (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        let S := a+m
        let R := pairLength a m
        let B := FixedRawLengthFence.allocation R
        let F := FixedRawLengthFence.fencePos R
        let n := pr.2.n
        let L := S+z+2
        let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
        let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
        let p := min (9+2*z+2^n) S
        let r := S-p
        let X := CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
        let Y := RuntimeBitLength.Target.fullImage X L n F r
        let c := initialConfig (IngressRepair.machine k) B (encodePair x w)
        (p=S → ∃ t, t ≤ 134217728*(R+1)^4 ∧ S ≤ Cursor.Target.M k n z ∧
          padRead (Fin.append x w) (Cursor.Target.M k n z)=false ∧
          (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩ ∧
          (∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
            ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject)) ∧
        (p<S → F+5*r+n+7 < tapeLength R B ∧
          (bitLength n ≤ r → ∃ (t : Nat) (h : F+2*r+n+4 < tapeLength R B),
            t ≤ 134217728*(R+1)^4 ∧
            (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 329,⟨F+2*r+n+4,h⟩,fun i => AllArityBitLength.Target.seedImage Y F r n i.val⟩ ∧
            (∀ u, u<t → ((IngressRepair.machine k).run u c).state≠
              IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 329)) ∧
            (∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
              ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject)) ∧
          (r<bitLength n → ∃ t, t ≤ 134217728*(R+1)^4 ∧ S<Cursor.Target.M k n z ∧
            padRead (Fin.append x w) (Cursor.Target.M k n z)=false ∧
            (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,
                fun i => Cursor.Target.image V k S n z F i.val⟩ ∧
            (∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
              ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject)))
end VirtualReady.Target
