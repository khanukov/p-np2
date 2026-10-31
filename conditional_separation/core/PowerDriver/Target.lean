import CappedWeight.Raw
namespace PowerDriver.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
def RawPower (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      ∃ (z : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      let S := a+m; let R := pairLength a m; let B := FixedRawLengthFence.allocation R
      let n := pr.2.n; let L := S+z+2; let F := FixedRawLengthFence.fencePos R
      let p := min (9+2*z+2^n) S; let r := S-p
      let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
      let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
      let X := CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
      let Y := RuntimeBitLength.Target.fullImage X L n F r
      let Z := AllArityBitLength.Target.seedImage Y F r n
      let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
      (p=S → ∃ t, t≤1073741824*(k+1)*(R+1)^4 ∧ S≤Cursor.Target.M k n z ∧
        (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩) ∧
      (p<S → ∃ (h : F+5*r+n+7 < tapeLength R B) (t : Nat),
        t≤1073741824*(k+1)*(R+1)^4 ∧
        ((r<bitLength n ∧ S<Cursor.Target.M k n z ∧
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) h⟩,fun i => Y i.val⟩) ∨
         (bitLength n≤r ∧
          (((n^k≤r) ∧
            (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (329+82*k),⟨F+2*r+n+4,lt_of_le_of_lt (by omega : F+2*r+n+4 ≤ F+5*r+n+7) h⟩,
                fun i => CappedWeight.Target.image Z L n F r (bitLength n) (n^k) 0 0 0 i.val⟩ ∧
            ∀ u, u<t → ((AllArityCursor.machine k).run u c).state.val<288+329+82*k) ∨
           (∃ j a e, j<k ∧ a<n^j ∧ e<n ∧ r=a*n+e ∧ S<Cursor.Target.M k n z ∧
            (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (798+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1 ≤ F+5*r+n+7) h⟩,
                fun i => CappedWeight.Target.image Z L n F r (bitLength n) (n^j-a-1) r 0 (e+1) i.val⟩ ∧
            ∀ u, u<t → ((AllArityCursor.machine k).run u c).state.val<288+329+82*k)))))
end PowerDriver.Target
