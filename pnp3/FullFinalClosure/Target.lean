import FullFinalClosure.Machine
import VirtualFinalClosure.Raw
import NormalFinalClosure.Surface2
import UniformClassBridgeClosure.Lifts
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
/-- The exact original NORMAL source image; specification only. -/
def normalBase (k N : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z n : Nat) : Nat → Option Bool :=
  let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N;let Q:=2^n
  let r:=S-min (9+2*z+Q) S;let W:=Cursor.Target.W k n;let g:=n^k+k
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation N) x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) Q Q false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 g W 0 0) F r n g (bitLength W) 0 0 W
namespace Target
/-- Complete all-input literal FINAL, strict FIRST and actual whole-configuration
handoff/callee coupling. There are no parser, semantic or execution premises. -/
def Raw (k : Nat) : Prop :=
  ∀ N (y : Bitstring N),
  let B:=allocation k N;let A:=VirtualFinalClosure.machine k;let M:=machine k
  let c:=initialConfig M B y;let ac:=initialConfig A B y
  ∃ d t,d ≤ t ∧ t ≤ runtimeBound k N ∧
    (∀ u,u ≤ d → M.run u c=configA k (A.run u ac)) ∧
    (∀ u,u < d → (A.run u ac).state≠A.accept ∧ (A.run u ac).state≠A.reject ∧
      ∀ (mode : Fin 3) (flag : Fin 144),(A.run u ac).state≠VirtualFinalClosure.control k
        (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) flag) ∧
    (∀ u,u < t → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject) ∧
    (∀ u,u ≤ t → (M.run u c).head.val+1 < tapeLength N B) ∧
    (M.run t c).state=(if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y
      then M.accept else M.reject) ∧
    ((t=d ∧ (A.run d ac).state=(if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y
        then A.accept else A.reject)) ∨
     (∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN:pairLength a m=N),
       decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
       ∃ n z,FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
       FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
       contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
       let S:=a+m;let F:=FixedRawLengthFence.fencePos N;let r:=S-min (9+2*z+2^n) S
       let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
       let mode:=SerializedBody.sourceMode (Fin.append x w) address
       n < FixedRawLengthFence.capacity a m z ∧ S+z+n+3+2^n < F ∧
       min (9+2*z+2^n) S < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
       ∃ hH:S+z+n+3 < tapeLength N B,
       let body : Config (NormalFinalClosure.machine2 k).stateCount N B:=
         ⟨entryB k mode,⟨S+z+n+3,hH⟩,
           fun i=>SerializedBody.prepared (normalBase k N x w z n) S address F r n (n^k+k) W i.val⟩
       A.run d ac=⟨entryA k mode,body.head,body.tape⟩ ∧
       M.run (d+1) c=configB k body ∧
       ∃ s,t=d+1+s ∧
         (∀ v,v ≤ s → M.run (d+1+v) c=configB k ((NormalFinalClosure.machine2 k).run v body))))
/-- Full pointwise extension at every prefix, followed by actual polynomial
clock decisions. Only literal terminals are extended to the deadline. -/
def Clock (k : Nat) : Prop :=
  allocation k 0 ≤ polyClock (degree k) 0 ∧
  (∀ N,allocation k N ≤ polyClock (degree k) N) ∧
  ∀ N (y : Bitstring N),∃ t,t ≤ runtimeBound k N ∧
    (∀ (B : Nat) (h:allocation k N ≤ B),∀ u,u ≤ t →
      FixedPairParser.ConfigExtension h
        ((machine k).run u (initialConfig (machine k) (allocation k N) y))
        ((machine k).run u (initialConfig (machine k) B y))) ∧
    (machine k).run (polyClock (degree k) N) (initialConfig (machine k) (polyClock (degree k) N) y)=
      (machine k).run t (initialConfig (machine k) (polyClock (degree k) N) y) ∧
    DecidesAt (machine k) (polyClock (degree k) N) (polyClock (degree k) N) y
      (encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y) ∧
    DecidesWithin (machine k) (polyClock (degree k) N) y
      (encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y)
def Witnesses (k : Nat) : Prop :=
  ∀ a (x : Bitstring a),ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)) a x=true ↔
    ∃ m,∃ w:Bitstring m,m ≤ polyClock 1 a ∧ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true
/-- Concrete same relation/language/exponent endpoint in both supplied models. -/
def Full (k : Nat) : Prop := Raw k ∧ Clock k ∧
  VerifiesRelation (machine k) (degree k) (PartAEndpoint.thresholdContentWitnessRelation k) ∧ Witnesses k ∧
  UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  UniformClassBridgeClosure.Ordinary.Verifies (StandardTMBridgeClosure.compile (machine k))
    (some ((machine k).accept,0)) (some ((machine k).reject,0)) (4*degree k+4)
    (PartAEndpoint.thresholdContentWitnessRelation k) ∧
  UniformClassBridgeClosure.Ordinary.UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)))
end Target
end FullFinalClosure
