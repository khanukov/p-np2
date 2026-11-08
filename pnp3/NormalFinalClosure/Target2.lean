import NormalFinalClosure.Machine2
import NormalFinalClosure.Target
namespace NormalFinalClosure.Target2
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Complete connected NORMAL raw-to-literal-FINAL goal. No decoded/header/
accepted/frame/outcome premise is supplied. The exact virtual WORK Config is
preserved for the separate virtual owner. All old paid starts are retained by
whole-prefix equality at the same actual old frontier time, before activation. -/
def Raw (k : Nat) : Prop :=
  ∀ (N : Nat) (y : Bitstring N),
  let B:=RawCallerClosure.allocation k N
  let O:=RawCallerClosure.machine k
  let C:=initialConfig (NormalFinalClosure.machine2 k) B y
  let oldC:=initialConfig O B y
  let rows:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
  let virtual (b : Bool):=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
  ∃ d t, d ≤ t ∧ t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
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
      ∃ hH:S+z+2+n+1 < tapeLength N B,
      (O.run d oldC).head=⟨S+z+2+n+1,hH⟩ ∧
      ∃ answer : Bool,
      answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y ∧
      answer=PartAEndpoint.thresholdContentWitnessRelation k a m x w ∧
      (answer=true ↔ Target.PrefixOK (Fin.append x w) n z W) ∧
      (NormalFinalClosure.machine2 k).run t C=
        ⟨if answer then (NormalFinalClosure.machine2 k).accept else (NormalFinalClosure.machine2 k).reject,
          ⟨S+z+2+n+1,hH⟩,Target.cleared (O.run d oldC).tape F r n⟩))
end NormalFinalClosure.Target2
