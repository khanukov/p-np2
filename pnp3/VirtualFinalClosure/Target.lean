import VirtualFinalClosure.Finite
namespace VirtualFinalClosure.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option autoImplicit false
/-- Exact normalized virtual FINAL tape. EOF has no invented scratch banks.
A resized cap path retains its actual occupied delimiters and capacity C. -/
def virtualImage (V : Nat → Option Bool) (S z n F p C : Nat) : Nat → Option Bool :=
  fun i=>if i=S+z+n+3 then (if n=0 then none else some false)
    else if p=S then V i else Cursor.Target.scratch V F C n i
/-- Full unconditional raw execution target, frozen after literal ROM pilots.
All semantic and geometric facts are returned, never caller premises. -/
def Raw (k : Nat) : Prop :=
  ∀ (N : Nat) (y : Bitstring N),
    let B:=allocation k N;let O:=CertificateGuardClosure.machine k
    let C0:=CertificateGuardClosure.allocation k N;let M:=machine k
    let c:=initialConfig M B y;let old:=initialConfig O C0 y
    ∃ (T : Nat),T ≤ deadline k N ∧
      (∀ u,u ≤ T → (M.run u c).head.val ≤ spaceBound k N) ∧
      (∀ u,u < T → (M.run u c).state ≠ M.accept ∧ (M.run u c).state ≠ M.reject ∧
        ∀ (mode : Fin 3) (flag : Fin 144),(M.run u c).state ≠ control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k
            (BodyIngress.body k (SerializedBody.entry mode)))) flag) ∧
      ((∃ (h : C0 ≤ B) (s : Nat),s=T ∧ s ≤ CertificateGuardClosure.deadline k N ∧
          (O.run s old).state=O.reject ∧
          M.run T c=config k ⟨8,by decide⟩ (IngressAllocation.extendConfig h (O.run s old)) ∧
          encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false) ∨
       (∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN:pairLength a m=N),
          decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
          ∃ (n z : Nat) (hH:a+m+z+n+3 < tapeLength N B),
          FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
          FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
          contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
          let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N
          let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
          let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
          let g:=n^k+k;let B0:=FixedRawLengthFence.allocation N
          let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
          let V:=Stream.Target.image U S z n (9+2*z) Q Q false
          let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
          let Y:=RuntimeBitLength.Target.fullImage X L n F r
          let Z:=AllArityBitLength.Target.seedImage Y F r n
          let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 g W 0 0)
            F r n g (bitLength W) 0 0 W
          n < FixedRawLengthFence.capacity a m z ∧ S+z+n+3+Q < F ∧
          ((p < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
              SerializedBody.delimiter F r n 12 < tapeLength N B ∧
              (∀ i,address ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
              ∃ (h : C0 ≤ B),T ≤ CertificateGuardClosure.deadline k N ∧
                (∀ u,u ≤ T → ∃ flag : Fin 144,
                  M.run u c=config k flag (IngressAllocation.extendConfig h (O.run u old))) ∧
                M.run T c=⟨control k (CertificateGuardClosure.old k (TotalIngressClosure.old k
                  (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address)))))
                    ⟨8,by decide⟩,⟨S+z+n+3,hH⟩,
                  fun i=>SerializedBody.prepared I S address F r n g W i.val⟩) ∨
           (S ≤ address ∧
              ((p=S) ∨ (p<S ∧ (r<bitLength n ∨ (bitLength n≤r ∧
                ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d)))) ∧
              (∀ j : Fin W,padRead (Fin.append x w) (address+j.val)=false) ∧
              (n=0 → (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=none) ∧
              (∀ positive : 0<n,(treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=
                some (Pnp3.Models.Circuit.input ⟨0,positive⟩)) ∧
              ∃ (C : Nat),((p=S ∧ C=0) ∨ (p<S ∧ r ≤ C ∧ C ≤ 2*(W+r+1))) ∧
                F+5*C+n+7 < tapeLength N B ∧
                M.run T c=⟨if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y
                    then M.accept else M.reject,⟨S+z+n+3,hH⟩,
                  fun i=>virtualImage V S z n F p C i.val⟩))))
private def virtualImage_type : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Bool := virtualImage
private def Raw_type : Nat → Prop := Raw
#print axioms virtualImage
#print axioms Raw
#print axioms virtualImage_type
#print axioms Raw_type
end VirtualFinalClosure.Target
