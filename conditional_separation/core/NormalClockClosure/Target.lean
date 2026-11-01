import NormalClockClosure.Joint
import Complexity.Uniform.V1.PolynomialTime
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Transparent fixed-k degree; no proof-to-data degree extraction. -/
def degree (k : Nat) : Nat := 4503599627370496*(k+1)+64
namespace Target
/-- SAME frozen table, all raw inputs; SAME actual witnesses and full original
partition, guarded ambient extension, and real V1 clock-indexed decisions on
literal terminal branches. Virtual WORK remains a nonverdict handoff. -/
def Bridge (k : Nat) : Prop :=
  ∀ (N : Nat) (y : Bitstring N),
  let G:=RawCallerClosure.allocation k N
  let M:=NormalFinalClosure.machine2 k
  let C:=initialConfig M G y
  let O:=RawCallerClosure.machine k
  let oldC:=initialConfig O G y
  let rows:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
  let virtual (b : Bool):=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
  let P:=polyClock (degree k) N
  ∃ (d t : Nat) (_hGP:G ≤ P), d ≤ t ∧ t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
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
    (∀ u,u ≤ d → (NormalFinalClosure.machine2 k).run u C=
      NormalFinalClosure.config2 k (O.run u oldC)) ∧
    (∀ u,u ≤ d → (O.run u oldC).state≠O.accept) ∧
    (∀ u,u < d → (O.run u oldC).state≠O.reject ∧ (O.run u oldC).state≠rows ∧
      ∀ b,(O.run u oldC).state≠virtual b) ∧
    (∀ u,u < t → ((NormalFinalClosure.machine2 k).run u C).state≠(NormalFinalClosure.machine2 k).accept ∧
      ((NormalFinalClosure.machine2 k).run u C).state≠(NormalFinalClosure.machine2 k).reject ∧
      ∀ b,((NormalFinalClosure.machine2 k).run u C).state≠NormalFinalClosure.old2 k (virtual b)) ∧
    ((t=d ∧ (∃ b,(O.run d oldC).state=virtual b) ∧
      (NormalFinalClosure.machine2 k).run t C=NormalFinalClosure.config2 k (O.run d oldC)) ∨
     (t=d ∧ (O.run d oldC).state=O.reject ∧
      encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false ∧
      (NormalFinalClosure.machine2 k).run t C=NormalFinalClosure.config2 k (O.run d oldC)) ∨
     (∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN : pairLength a m=N),
      decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
      ∃ n z, FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
      let S:=a+m;let F:=FixedRawLengthFence.fencePos N;let r:=S-min (9+2*z+2^n) S
      let W:=Cursor.Target.W k n
      min (9+2*z+2^n) S < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
      (O.run d oldC).state=rows ∧
      ∃ hH:S+z+2+n+1 < tapeLength N G,
      (O.run d oldC).head=⟨S+z+2+n+1,hH⟩ ∧
      ∃ answer : Bool,
      answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y ∧
      answer=PartAEndpoint.thresholdContentWitnessRelation k a m x w ∧
      (answer=true ↔ NormalFinalClosure.Target.PrefixOK (Fin.append x w) n z W) ∧
      (NormalFinalClosure.machine2 k).run t C=
        ⟨if answer then (NormalFinalClosure.machine2 k).accept else (NormalFinalClosure.machine2 k).reject,
          ⟨S+z+2+n+1,hH⟩,NormalFinalClosure.Target.cleared (O.run d oldC).tape F r n⟩))
end Target
end NormalClockClosure
