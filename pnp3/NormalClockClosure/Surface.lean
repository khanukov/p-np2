import NormalClockClosure.Driver
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Independently expanded full resource/clock proposition: actual same raw
witness, both finite tape domains, every low/high cell, all three outcomes and
original witness-prefix tests. There is no prepared/provider/run hypothesis. -/
theorem bridge_full (k : Nat) :
    ∀ (N : Nat) (y : Fin N → Bool),
    let G:=1099511627776*(k+1)*(N+1)^8
    let M:=NormalFinalClosure.machine2 k
    let C:=initialConfig M G y
    let O:=RawCallerClosure.machine k
    let oldC:=initialConfig O G y
    let rows:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
    let virtual (b : Bool):=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
    let P:=N^(4503599627370496*(k+1)+64)+(4503599627370496*(k+1)+64)
    ∃ (d t : Nat) (_hGP:G ≤ P),d ≤ t ∧ t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
      t+1 ≤ G ∧ 17592186044416*(k+1)*(N+1)^8 ≤ P ∧
      (∀ u,u ≤ t → (M.run u C).head.val+1 < tapeLength N G) ∧
      (∀ (B : Nat) (hGB:G ≤ B),
        (∀ u,u ≤ t →
          (M.run u C).state=(M.run u (initialConfig M B y)).state ∧
          (M.run u (initialConfig M B y)).head=FixedPairParser.tapeEmbed hGB (M.run u C).head ∧
          (∀ i:Fin (tapeLength N G),(M.run u (initialConfig M B y)).tape (FixedPairParser.tapeEmbed hGB i)=(M.run u C).tape i) ∧
          (∀ j:Fin (tapeLength N B),tapeLength N G ≤ j.val → (M.run u (initialConfig M B y)).tape j=none) ∧
          (M.run u C).head.val ≤ t ∧ (M.run u (initialConfig M B y)).head.val ≤ t) ∧
        (∀ u,u < t → (M.run u (initialConfig M B y)).state≠M.accept ∧
          (M.run u (initialConfig M B y)).state≠M.reject ∧
          ∀ b,(M.run u (initialConfig M B y)).state≠NormalFinalClosure.old2 k (virtual b)) ∧
        (∀ T,t ≤ T → (M.run t C).state=M.accept ∨ (M.run t C).state=M.reject →
          M.run T (initialConfig M B y)=M.run t (initialConfig M B y))) ∧
      (∀ answer : Bool,(M.run t C).state=(if answer then M.accept else M.reject) →
        M.run P (initialConfig M P y)=M.run t (initialConfig M P y) ∧
        DecidesAt M P P y answer ∧ DecidesWithin M P y answer) ∧
      (∀ u,u ≤ d → M.run u C=NormalFinalClosure.config2 k (O.run u oldC)) ∧
      (∀ u,u ≤ d → (O.run u oldC).state≠O.accept) ∧
      (∀ u,u < d → (O.run u oldC).state≠O.reject ∧ (O.run u oldC).state≠rows ∧
        ∀ b,(O.run u oldC).state≠virtual b) ∧
      (∀ u,u < t → (M.run u C).state≠M.accept ∧ (M.run u C).state≠M.reject ∧
        ∀ b,(M.run u C).state≠NormalFinalClosure.old2 k (virtual b)) ∧
      ((t=d ∧ (∃ b,(O.run d oldC).state=virtual b) ∧
          M.run t C=NormalFinalClosure.config2 k (O.run d oldC)) ∨
       (t=d ∧ (O.run d oldC).state=O.reject ∧
          encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false ∧
          M.run t C=NormalFinalClosure.config2 k (O.run d oldC)) ∨
       (∃ (a m : Nat) (x : Fin a → Bool) (w : Fin m → Bool) (hN:pairLength a m=N),
          decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
          ∃ n z,FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
          FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
          contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
          let S:=a+m;let F:=FixedRawLengthFence.fencePos N
          let r:=S-min (9+2*z+2^n) S;let W:=Cursor.Target.W k n
          min (9+2*z+2^n) S < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
          (O.run d oldC).state=rows ∧
          ∃ hH:S+z+2+n+1 < tapeLength N G,
          (O.run d oldC).head=⟨S+z+2+n+1,hH⟩ ∧
          ∃ answer : Bool,
          answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y ∧
          answer=PartAEndpoint.thresholdContentWitnessRelation k a m x w ∧
          (answer=true ↔ ∃ i,
            readNatBE (padWord (Fin.append x w) (9+2*z+2^n+bitLength W+W)) (9+2*z+2^n) (bitLength W)=some i ∧
            i ≤ W ∧
            (∀ j,j < i → padRead (Fin.append x w) (9+2*z+2^n+bitLength W+j)=
              padRead (Fin.append x w) (9+2*z+2^n+bitLength W+W+j)) ∧
            (∀ j,i ≤ j → j < W → padRead (Fin.append x w) (9+2*z+2^n+bitLength W+j)=false)) ∧
          M.run t C=⟨if answer then M.accept else M.reject,⟨S+z+2+n+1,hH⟩,
            NormalFinalClosure.Target.cleared (O.run d oldC).tape F r n⟩)) := by
  exact bridge k
#print axioms bridge
#print axioms bridge_full
end NormalClockClosure
