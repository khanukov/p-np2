import NormalFinalClosure.Driver2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Independent full proposition mirror: arbitrary raw input, FIRST old
frontier preserved, actual NORMAL literal verdict, original-language BE/prefix/
inactive-padding correctness, exact full tape/head and length-only price. -/
theorem normal_raw_full (k : Nat) :
    ∀ (N : Nat) (y : Fin N → Bool),
    let B:=RawCallerClosure.allocation k N
    let O:=RawCallerClosure.machine k
    let c:=initialConfig (NormalFinalClosure.machine2 k) B y
    let oldc:=initialConfig O B y
    let rowExit:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
    let virtual (b : Bool):=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
    ∃ d t,d ≤ t ∧ t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
      (∀ u,u ≤ d → (NormalFinalClosure.machine2 k).run u c=NormalFinalClosure.config2 k (O.run u oldc)) ∧
      (∀ u,u ≤ d → (O.run u oldc).state≠O.accept) ∧
      (∀ u,u < d → (O.run u oldc).state≠O.reject ∧ (O.run u oldc).state≠rowExit ∧
        ∀ b,(O.run u oldc).state≠virtual b) ∧
      (∀ u,u < t → ((NormalFinalClosure.machine2 k).run u c).state≠(NormalFinalClosure.machine2 k).accept ∧
        ((NormalFinalClosure.machine2 k).run u c).state≠(NormalFinalClosure.machine2 k).reject ∧
        ∀ b,((NormalFinalClosure.machine2 k).run u c).state≠NormalFinalClosure.old2 k (virtual b)) ∧
      ((t=d ∧ (∃ b,(O.run d oldc).state=virtual b) ∧
        (NormalFinalClosure.machine2 k).run t c=NormalFinalClosure.config2 k (O.run d oldc)) ∨
       (t=d ∧ (O.run d oldc).state=O.reject ∧
        encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false ∧
        (NormalFinalClosure.machine2 k).run t c=NormalFinalClosure.config2 k (O.run d oldc)) ∨
       (∃ (a m : Nat) (x : Fin a → Bool) (w : Fin m → Bool) (hN : pairLength a m=N),
        decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
        ∃ n z,FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
        let S:=a+m;let F:=FixedRawLengthFence.fencePos N
        let r:=S-min (9+2*z+2^n) S;let W:=Cursor.Target.W k n
        min (9+2*z+2^n) S < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
        (O.run d oldc).state=rowExit ∧
        ∃ hH:S+z+2+n+1 < tapeLength N B,
        (O.run d oldc).head=⟨S+z+2+n+1,hH⟩ ∧
        ∃ answer : Bool,
        answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y ∧
        answer=PartAEndpoint.thresholdContentWitnessRelation k a m x w ∧
        (answer=true ↔ ∃ i,
          readNatBE (padWord (Fin.append x w) (9+2*z+2^n+bitLength W+W)) (9+2*z+2^n) (bitLength W)=some i ∧
          i ≤ W ∧
          (∀ j,j < i → padRead (Fin.append x w) (9+2*z+2^n+bitLength W+j)=
            padRead (Fin.append x w) (9+2*z+2^n+bitLength W+W+j)) ∧
          (∀ j,i ≤ j → j < W → padRead (Fin.append x w) (9+2*z+2^n+bitLength W+j)=false)) ∧
        (NormalFinalClosure.machine2 k).run t c=
          ⟨if answer then (NormalFinalClosure.machine2 k).accept else (NormalFinalClosure.machine2 k).reject,
            ⟨S+z+2+n+1,hH⟩,Target.cleared (O.run d oldc).tape F r n⟩)) := by
  exact normal_raw k
#print axioms NormalFinalClosure.normal_raw
#print axioms NormalFinalClosure.normal_raw_full
end NormalFinalClosure
