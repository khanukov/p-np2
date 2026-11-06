import NormalFinalClosure.Machine
namespace NormalFinalClosure.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Specification of the final cleanup, relative to the ACTUAL whole old
rowsDone tape. Source, assignment, metadata, all delimiters and exterior stay exact. -/
def cleared {N B : Nat} (T : Fin (tapeLength N B) → Option Bool) (F r n : Nat) :
    Fin (tapeLength N B) → Option Bool := fun i=>
  if (SerializedBody.delimiter F r n 4 < i.val ∧ i.val < SerializedBody.delimiter F r n 5) ∨
     (SerializedBody.delimiter F r n 5 < i.val ∧ i.val < SerializedBody.delimiter F r n 6) ∨
     (SerializedBody.delimiter F r n 6 < i.val ∧ i.val < SerializedBody.delimiter F r n 7) ∨
     (SerializedBody.delimiter F r n 11 < i.val ∧ i.val < SerializedBody.delimiter F r n 12)
  then some false
  else if SerializedBody.delimiter F r n 10 < i.val ∧ i.val < SerializedBody.delimiter F r n 11
  then some true else T i
/-- The original prefix/index/padding tests, using the entire original witness
window. This is proof specification only, never an executable TM instruction. -/
def PrefixOK {S : Nat} (source : Fin S → Bool) (n z W : Nat) : Prop :=
  ∃ i, readNatBE (padWord source (9+2*z+2^n+bitLength W+W)) (9+2*z+2^n) (bitLength W)=some i ∧
    i ≤ W ∧
    (∀ j,j < i → padRead source (9+2*z+2^n+bitLength W+j)=
      padRead source (9+2*z+2^n+bitLength W+W+j)) ∧
    (∀ j,i ≤ j → j < W → padRead source (9+2*z+2^n+bitLength W+j)=false)
/-- Complete connected NORMAL raw-to-literal-FINAL goal. No decoded/header/
accepted/frame/outcome premise is supplied. The exact virtual WORK Config is
preserved for the separate virtual owner. All old paid starts are retained by
whole-prefix equality at the same actual old frontier time, before activation. -/
def Raw (k : Nat) : Prop :=
  ∀ (N : Nat) (y : Bitstring N),
  let B:=RawCallerClosure.allocation k N
  let O:=RawCallerClosure.machine k
  let C:=initialConfig (NormalFinalClosure.machine k) B y
  let oldC:=initialConfig O B y
  let rows:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
  let virtual (b : Bool):=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
  ∃ d t, d ≤ t ∧ t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
    (∀ u,u ≤ d → (NormalFinalClosure.machine k).run u C=
      NormalFinalClosure.config k (O.run u oldC)) ∧
    (∀ u,u ≤ d → (O.run u oldC).state≠O.accept) ∧
    (∀ u,u < d → (O.run u oldC).state≠O.reject ∧ (O.run u oldC).state≠rows ∧
      ∀ b,(O.run u oldC).state≠virtual b) ∧
    (∀ u,u < t → ((NormalFinalClosure.machine k).run u C).state≠(NormalFinalClosure.machine k).accept ∧
      ((NormalFinalClosure.machine k).run u C).state≠(NormalFinalClosure.machine k).reject ∧
      ∀ b,((NormalFinalClosure.machine k).run u C).state≠NormalFinalClosure.old k (virtual b)) ∧
    ((t=d ∧ (∃ b,(O.run d oldC).state=virtual b) ∧
      (NormalFinalClosure.machine k).run t C=NormalFinalClosure.config k (O.run d oldC)) ∨
     (t=d ∧ (O.run d oldC).state=O.reject ∧
      encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false ∧
      (NormalFinalClosure.machine k).run t C=NormalFinalClosure.config k (O.run d oldC)) ∨
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
      (answer=true ↔ PrefixOK (Fin.append x w) n z W) ∧
      (NormalFinalClosure.machine k).run t C=
        ⟨if answer then (NormalFinalClosure.machine k).accept else (NormalFinalClosure.machine k).reject,
          ⟨S+z+2+n+1,hH⟩,cleared (O.run d oldC).tape F r n⟩))
end NormalFinalClosure.Target
