import CappedWeight.Target
namespace CappedWeight.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
def RawProduct (k : Nat) : Prop :=
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
        let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
        (p=S → ∃ t, t ≤ 67108864*(R+1)^4 ∧ S ≤ Cursor.Target.M k n z ∧
          padRead (Fin.append x w) (Cursor.Target.M k n z)=false ∧
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩) ∧
        (p<S → ∃ (t : Nat)
          (h : (if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3) < tapeLength R B),
          t ≤ 67108864*(R+1)^4 ∧ F+5*r+n+7 < tapeLength R B ∧
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
              ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,h⟩,
              fun i => (if bitLength n ≤ r then AllArityBitLength.Target.seedImage Y F r n else Y) i.val⟩ ∧
          (∀ u, u<t → ((AllArityCursor.machine k).run u c).state≠
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 329)) ∧
          (r<bitLength n → S<Cursor.Target.M k n z) ∧
          (bitLength n≤r → ∀ (fit : F+5*r+n+7 < tapeLength R B), ∃ d, d≤1024*(n+r+1)^2*(F+5*r+n+9) ∧
            (AllArityCursor.machine k).run (t+d) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (if n≤r then 411 else 798+93*k),
                ⟨if n≤r then F+2*r+n+4 else F+1,
                  by exact lt_of_le_of_lt (by split <;> omega : (if n≤r then F+2*r+n+4 else F+1) ≤ F+5*r+n+7) fit⟩,
                fun i => image (AllArityBitLength.Target.seedImage Y F r n) L n F r (bitLength n)
                  (if n≤r then n else 0) (if n≤r then 0 else r) 0 (if n≤r then 0 else r+1) i.val⟩ ∧
            t+d≤268435456*(R+1)^4 ∧
            (∀ u, u<d → ((AllArityCursor.machine k).run (t+u) c).state.val<699) ∧
            (r<n → S<Cursor.Target.M k n z)))
end CappedWeight.Target
