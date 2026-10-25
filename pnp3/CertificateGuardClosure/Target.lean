import CertificateGuardClosure.Machine
namespace CertificateGuardClosure.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- The predecessor's entire concrete per-time outcome, copied as a proposition
with an explicit elapsed witness, not a provider premise or a new language. -/
def Frontier (k N : Nat) (y : Bitstring N) (t : Nat) : Prop :=
    let B:=TotalIngressClosure.allocation k N; let B0:=FixedRawLengthFence.allocation N
    let M:=TotalIngressClosure.machine k; let O:=BodyIngress.machine k
    let c:=initialConfig M B y;let c0:=initialConfig O B0 y;let large:=initialConfig O B y
    t ≤ TotalIngressClosure.deadline k N ∧
      (∀ u,u ≤ t → (M.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ t → (M.run u c).state ≠ M.accept) ∧
      (∀ u,u < t → (M.run u c).state ≠ M.reject ∧
        (∀ b,(M.run u c).state ≠ TotalIngressClosure.old k (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))) ∧
        (∀ mode:Fin 3,(M.run u c).state ≠ TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) ∧
      ((decodePair y=none ∧ t=FixedPairParser.clock N ∧
          M.run t c=⟨M.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩ ∧
          encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false) ∨
       ∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN:pairLength a m=N),
        decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧
        y=(hN ▸ encodePair x w) ∧
        ∃ d,t=FixedPairParser.clock N+d ∧
          (∀ u,M.run (FixedPairParser.clock N+u) c=TotalIngressClosure.config k (O.run u large)) ∧
          ∃ hBudget:B0 ≤ B,
            FixedPairParser.ConfigExtension hBudget c0 large ∧
            IngressAllocation.Footprint O (C:=B0) y d (12*(N+1)^2) ∧
            IngressAllocation.MoveRoom O (C:=B0) y d ∧
            IngressAllocation.Trace O hBudget y d ∧
            (M.run t c=TotalIngressClosure.config k (IngressAllocation.extendConfig hBudget (O.run d c0))) ∧
            (((O.run d c0).state=O.reject ∧
                PartAEndpoint.thresholdContentWitnessRelation k a m x w=false) ∨
             ∃ (n z : Nat) (hH:a+m+z+n+3 < tapeLength N B0),
              FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
              FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
              contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
              let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N
              let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
              let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
              let H:Fin (tapeLength N B0):=⟨S+z+n+3,hH⟩
              let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
              let V:=Stream.Target.image U S z n (9+2*z) Q Q false
              let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
              let Y:=RuntimeBitLength.Target.fullImage X L n F r
              let Z:=AllArityBitLength.Target.seedImage Y F r n
              let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
                F r n (n^k+k) (bitLength W) 0 0 W
              n < FixedRawLengthFence.capacity a m z ∧ H.val+Q < F ∧
              ((p < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
                  SerializedBody.delimiter F r n 12 < tapeLength N B0 ∧
                  (∀ i,address ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
                  O.run d c0=⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address)),H,
                    fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩) ∨
               (∃ positive : 0 < n, S ≤ address ∧
                  (∀ j:Fin W,padRead (Fin.append x w) (address+j.val)=false) ∧
                  (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=
                    some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
                  ((p=S ∧ O.run d c0=
                      ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                        Function.update (fun i=>V i.val) H (some false)⟩) ∨
                   (p < S ∧
                      ((r < bitLength n) ∨
                       (bitLength n ≤ r ∧ ∃ v2 v3 v4 v5 residual,
                          CappedWeight.Target.Cap k n r v2 v3 v4 v5 residual)) ∧
                      O.run d c0=
                        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                          Function.update (fun i=>Cursor.Target.image V k S n z F i.val) H (some false)⟩))))))

/-- Unconditional physical exact-length guard and the SAME concrete ingress.
All source, parse and length facts occur inside the result, never as premises. -/
def Raw (k : Nat) : Prop :=
  ∀ (N : Nat) (y : Bitstring N),
    let B:=allocation k N;let M:=machine k;let O:=TotalIngressClosure.machine k
    let c:=initialConfig M B y;let c0:=initialConfig O B y
    ∃ T,T ≤ deadline k N ∧
      (∀ u,u ≤ T → (M.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ T → (M.run u c).state ≠ M.accept) ∧
      (∀ u,u < T → (M.run u c).state ≠ M.reject ∧
        (∀ b,(M.run u c).state ≠ old k (TotalIngressClosure.old k
          (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))) ∧
        (∀ mode:Fin 3,(M.run u c).state ≠ old k (TotalIngressClosure.old k
          (BodyIngress.body k (SerializedBody.entry mode))))) ∧
      ((decodePair y=none ∧ T=FixedPairParser.clock N ∧
          M.run T c=⟨M.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩ ∧
          encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false) ∨
       (∃ (a m:Nat) (x:Bitstring a) (w:Bitstring m) (hN:pairLength a m=N),
          decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧
          m ≠ a+1 ∧ T ≤ FixedPairParser.clock N+64*(N+1)^2 ∧
          M.run T c=⟨M.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩ ∧
          PartAEndpoint.thresholdContentWitnessRelation k a m x w=false) ∨
       (∃ (a m:Nat) (x:Bitstring a) (w:Bitstring m) (hN:pairLength a m=N),
          decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧
          m=a+1 ∧ ∃ g d,T=g+d ∧ g ≤ FixedPairParser.clock N+64*(N+1)^2 ∧
          (∀ u,u < g → (M.run u c).state.val < 77) ∧
          M.run g c=config k c0 ∧
          (∀ u,M.run (g+u) c=config k (O.run u c0)) ∧
          Frontier k N y d ∧ M.run T c=config k (O.run d c0)))
end CertificateGuardClosure.Target
