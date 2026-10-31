import VirtualReady.Fixtures
namespace VirtualReady.Audit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 10000
def pin_AcceptedVirtual : (k : Nat) → Prop := @VirtualReady.Target.AcceptedVirtual
theorem check_accepted_virtual (k : Nat) :
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
              ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject))) := by
  exact VirtualReady.accepted_virtual k
theorem check_canonical_outcome (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    let a := treeMCSPPrefixM codec n.val
    let m := Pnp3.ComplexityInterfaces.certificateLength a 1
    let x := zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 134217728*(pairLength a m+1)^4 ∧
        let c := initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 329) ∨
         ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) ∧
        (∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
          ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject) := by
  exact VirtualReady.canonical_outcome k n b
theorem check_fullImage_eq_1 (X : Nat → Option Bool) (L n F r i : Nat) :
    RuntimeBitLength.Target.fullImage X L n F r i =
      if L < i ∧ i < L+n+1 then
        some (decide (r < bitLength n ∧ (r+1)%2=0 ∧ i ≤ L+n/2^(r+1))) else
      if F+r+2 < i ∧ i < F+r+n+3 then
        some (decide (r < bitLength n ∧ (r+1)%2=1 ∧ i ≤ F+r+2+n/2^(r+1))) else
      if F+r+n+3 < i ∧ i ≤ F+r+n+3+min (bitLength n) r then some true else X i := by
  exact RuntimeBitLength.Target.fullImage.eq_1 X L n F r i
theorem check_scratch_eq_1 (T : Nat → Option Bool) (F r n i : Nat) :
    Cursor.Target.scratch T F r n i =
      if F+1 < i ∧ i < F+r+2 ∨ F+r+2 < i ∧ i < F+r+n+3 ∨
         F+r+n+3 < i ∧ i < F+2*r+n+4 ∨ F+2*r+n+4 < i ∧ i < F+3*r+n+5 ∨
         F+3*r+n+5 < i ∧ i < F+4*r+n+6 ∨ F+4*r+n+6 < i ∧ i < F+5*r+n+7
      then some false else T i := by
  exact Cursor.Target.scratch.eq_1 T F r n i
theorem check_image_eq_1 (T : Nat → Option Bool) (k S n z F i : Nat) :
    Cursor.Target.image T k S n z F i =
      if i=Cursor.Target.M k n z ∧ i<S then none else
      (if min (9+2*z+2^n) S < S then Cursor.Target.scratch T F (S-min (9+2*z+2^n) S) n else T) i := by
  exact Cursor.Target.image.eq_1 T k S n z F i
end VirtualReady.Audit
#print axioms VirtualReady.Target.AcceptedVirtual
#print axioms VirtualReady.Audit.pin_AcceptedVirtual
#print axioms VirtualReady.accepted_virtual
#print axioms VirtualReady.Audit.check_accepted_virtual
#print axioms VirtualReady.canonical_outcome
#print axioms VirtualReady.Audit.check_canonical_outcome
#print axioms RuntimeBitLength.Target.fullImage.eq_1
#print axioms VirtualReady.Audit.check_fullImage_eq_1
#print axioms Cursor.Target.scratch.eq_1
#print axioms VirtualReady.Audit.check_scratch_eq_1
#print axioms Cursor.Target.image.eq_1
#print axioms VirtualReady.Audit.check_image_eq_1
