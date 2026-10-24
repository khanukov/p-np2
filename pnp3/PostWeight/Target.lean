import PostWeight.Pilot
namespace PostWeight.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- PREPARED exact W endpoint. FullRaw/raw-to-W is deliberately not a premise
or a conclusion. No wanted bitLength/selection/cleanup run is assumed. -/
def Normal (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∀ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    ∀ z, FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z →
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    p<S → bitLength n≤r → Cursor.Target.W k n≤r →
    ∀ fit : F+5*r+n+7 < tapeLength R B,
    let C : Config (Cursor.machine k).stateCount R B :=
      ⟨Cursor.q k (430+93*k),⟨F+r+n+3,by omega⟩,
        fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩
    ∃ (t : Nat) (hH : H < tapeLength R B) (mode : Fin 3),
      t≤1073741824*(k+1)*(R+1)^5 ∧
      (mode.val=2 ↔ S≤Cursor.Target.M k n z) ∧
      InputRead.result mode=padRead (Fin.append x w) (Cursor.Target.M k n z) ∧
      (Cursor.machine k).run t C=
        ⟨Cursor.mReady k mode,⟨H,hH⟩,fun i => Cursor.Target.image V k S n z F i.val⟩ ∧
      (∀ u, u≤t → ((Cursor.machine k).run u C).state≠(Cursor.machine k).accept ∧
        ((Cursor.machine k).run u C).state≠(Cursor.machine k).reject)
end PostWeight.Target
