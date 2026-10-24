import RawPrelude.Join
namespace RawPrelude.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Accepted raw prelude. q613 is a computed-field boundary, never MReady.
EOF retains V; only the two physically cleared arms use Cursor.Target.image. -/
def Raw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      ∃ (z : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
      let n:=pr.2.n; let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
      let p:=min (9+2*z+2^n) S; let r:=S-p
      let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
      let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
      let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
      let Y:=RuntimeBitLength.Target.fullImage X L n F r
      let Z:=AllArityBitLength.Target.seedImage Y F r n
      let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
      (p=S → ∃ t, t≤2147483648*(k+1)*(R+1)^5 ∧ S≤Cursor.Target.M k n z ∧
        (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩ ∧
        ∀ u, u≤t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
          ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject) ∧
      (p<S → ∃ fit : F+5*r+n+7 < tapeLength R B,
        (r<bitLength n ∧ S<Cursor.Target.M k n z ∧
          ∃ t, t≤268435456*(k+1)*(R+1)^4 ∧
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) fit⟩,fun i => Y i.val⟩ ∧
          t+(F-H+19*r+7*n+48)≤2147483648*(k+1)*(R+1)^5 ∧
          (AllArityCursor.machine k).run (t+(F-H+19*r+7*n+48)) c=
            SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => Cursor.Target.image V k S n z F i.val⟩ ∧
          ∀ u, u≤t+(F-H+19*r+7*n+48) →
            ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
            ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject) ∨
        (bitLength n≤r ∧
          ((Cursor.Target.W k n≤r ∧ ∃ t d,
            t≤268435456*(k+1)*(R+1)^4 ∧ d≤524288*(R+1)^3 ∧
            (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) fit⟩,
                fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩ ∧
            (∀ u, u<t → ((AllArityCursor.machine k).run u c).state≠
              SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))) ∧
            t+d≤2147483648*(k+1)*(R+1)^5 ∧
            (AllArityCursor.machine k).run (t+d) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (613+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1 ≤ F+5*r+n+7) fit⟩,
                fun i => CappedWeight.Target.image Z L n F r (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩ ∧
            ∀ u, u≤t+d → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject) ∨
          (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d ∧ S<Cursor.Target.M k n z ∧
            ∃ t, t≤268435456*(k+1)*(R+1)^4 ∧
            (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (798+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1 ≤ F+5*r+n+7) fit⟩,
                fun i => CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d i.val⟩ ∧
            (∀ u, u<t → ((AllArityCursor.machine k).run u c).state≠
              SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (798+93*k))) ∧
            t+(F-H+18*r+6*n+44)≤2147483648*(k+1)*(R+1)^5 ∧
            (AllArityCursor.machine k).run (t+(F-H+18*r+6*n+44)) c=
              SmallIngress.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => Cursor.Target.image V k S n z F i.val⟩ ∧
            ∀ u, u≤t+(F-H+18*r+6*n+44) →
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject))))
end RawPrelude.Target
