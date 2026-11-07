import FullFinalClosure.Endpoint
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`FullFinalClosure.Raw,["raw_complete"]),(`FullFinalClosure.Clock,["clock_complete","concrete_verifier"]),
      (`FullFinalClosure.Witnesses,["original_witnesses"]),(`FullFinalClosure.Endpoint,["full_endpoint"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `FullFinalClosure) leaf
      let some (.thmInfo ci):=e.find? n | throwError "Missing exact public surface proof {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing public surface owner"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong public surface owner"
      logInfo m!"registered-interface|{owner}|{n}|theorem|{(repr ci.type).pretty 1000000000}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
/-- Complete independently written public proposition. -/
theorem raw_full (k : Nat) :
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
         (∀ v,v ≤ s → M.run (d+1+v) c=configB k ((NormalFinalClosure.machine2 k).run v body)))) := raw_complete k
#print axioms raw_full
/-- Complete independently written public proposition. -/
theorem check_raw_full (k : Nat) :
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
         (∀ v,v ≤ s → M.run (d+1+v) c=configB k ((NormalFinalClosure.machine2 k).run v body)))) := raw_complete k
#print axioms check_raw_full
/-- Complete independently written public proposition. -/
theorem clock_full (k : Nat) :
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
      (encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y) := clock_complete k
#print axioms clock_full
/-- Complete independently written public proposition. -/
theorem check_clock_full (k : Nat) :
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
      (encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y) := clock_complete k
#print axioms check_clock_full
/-- Complete independently written public proposition. -/
theorem verifier_full (k : Nat) :
VerifiesRelation (machine k) (degree k) (PartAEndpoint.thresholdContentWitnessRelation k) := concrete_verifier k
#print axioms verifier_full
/-- Complete independently written public proposition. -/
theorem check_verifier_full (k : Nat) :
VerifiesRelation (machine k) (degree k) (PartAEndpoint.thresholdContentWitnessRelation k) := concrete_verifier k
#print axioms check_verifier_full
/-- Complete independently written public proposition. -/
theorem witnesses_full (k : Nat) :
  ∀ a (x : Bitstring a),ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)) a x=true ↔
    ∃ m,∃ w:Bitstring m,m ≤ polyClock 1 a ∧ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true := original_witnesses k
#print axioms witnesses_full
/-- Complete independently written public proposition. -/
theorem check_witnesses_full (k : Nat) :
  ∀ a (x : Bitstring a),ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)) a x=true ↔
    ∃ m,∃ w:Bitstring m,m ≤ polyClock 1 a ∧ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true := original_witnesses k
#print axioms check_witnesses_full
/-- Complete independently written public proposition. -/
theorem uniformNP_full (k : Nat) :
UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := (full_endpoint k).2.2.2.2.1
#print axioms uniformNP_full
/-- Complete independently written public proposition. -/
theorem check_uniformNP_full (k : Nat) :
UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := (full_endpoint k).2.2.2.2.1
#print axioms check_uniformNP_full
/-- Complete independently written public proposition. -/
theorem ordinary_verifier_full (k : Nat) :
UniformClassBridgeClosure.Ordinary.Verifies (StandardTMBridgeClosure.compile (machine k))
    (some ((machine k).accept,0)) (some ((machine k).reject,0)) (4*degree k+4)
    (PartAEndpoint.thresholdContentWitnessRelation k) := (full_endpoint k).2.2.2.2.2.1
#print axioms ordinary_verifier_full
/-- Complete independently written public proposition. -/
theorem check_ordinary_verifier_full (k : Nat) :
UniformClassBridgeClosure.Ordinary.Verifies (StandardTMBridgeClosure.compile (machine k))
    (some ((machine k).accept,0)) (some ((machine k).reject,0)) (4*degree k+4)
    (PartAEndpoint.thresholdContentWitnessRelation k) := (full_endpoint k).2.2.2.2.2.1
#print axioms check_ordinary_verifier_full
/-- Complete independently written public proposition. -/
theorem ordinary_uniformNP_full (k : Nat) :
UniformClassBridgeClosure.Ordinary.UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := (full_endpoint k).2.2.2.2.2.2
#print axioms ordinary_uniformNP_full
/-- Complete independently written public proposition. -/
theorem check_ordinary_uniformNP_full (k : Nat) :
UniformClassBridgeClosure.Ordinary.UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := (full_endpoint k).2.2.2.2.2.2
#print axioms check_ordinary_uniformNP_full
/-- Complete independently written public proposition. -/
theorem full_endpoint_full (k : Nat) :
(  ∀ N (y : Bitstring N),
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
         (∀ v,v ≤ s → M.run (d+1+v) c=configB k ((NormalFinalClosure.machine2 k).run v body))))) ∧ (  allocation k 0 ≤ polyClock (degree k) 0 ∧
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
      (encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y)) ∧
  VerifiesRelation (machine k) (degree k) (PartAEndpoint.thresholdContentWitnessRelation k) ∧ (  ∀ a (x : Bitstring a),ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)) a x=true ↔
    ∃ m,∃ w:Bitstring m,m ≤ polyClock 1 a ∧ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) ∧
  UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  UniformClassBridgeClosure.Ordinary.Verifies (StandardTMBridgeClosure.compile (machine k))
    (some ((machine k).accept,0)) (some ((machine k).reject,0)) (4*degree k+4)
    (PartAEndpoint.thresholdContentWitnessRelation k) ∧
  UniformClassBridgeClosure.Ordinary.UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := full_endpoint k
#print axioms full_endpoint_full
/-- Complete independently written public proposition. -/
theorem check_full_endpoint_full (k : Nat) :
(  ∀ N (y : Bitstring N),
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
         (∀ v,v ≤ s → M.run (d+1+v) c=configB k ((NormalFinalClosure.machine2 k).run v body))))) ∧ (  allocation k 0 ≤ polyClock (degree k) 0 ∧
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
      (encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y)) ∧
  VerifiesRelation (machine k) (degree k) (PartAEndpoint.thresholdContentWitnessRelation k) ∧ (  ∀ a (x : Bitstring a),ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)) a x=true ↔
    ∃ m,∃ w:Bitstring m,m ≤ polyClock 1 a ∧ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) ∧
  UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  UniformClassBridgeClosure.Ordinary.Verifies (StandardTMBridgeClosure.compile (machine k))
    (some ((machine k).accept,0)) (some ((machine k).reject,0)) (4*degree k+4)
    (PartAEndpoint.thresholdContentWitnessRelation k) ∧
  UniformClassBridgeClosure.Ordinary.UniformNP (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := full_endpoint k
#print axioms check_full_endpoint_full
end FullFinalClosure
