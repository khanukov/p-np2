import CertificateGuardClosure.Raw
import CertificateGuardClosure.Rows
namespace CertificateGuardClosure.Audit
set_option autoImplicit false
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Independent full proposition, including the full predecessor outcome rather
than a Target-only alias or a provider carrying a desired run. -/
theorem check_raw (k : Nat) :
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
          (let B:=TotalIngressClosure.allocation k N; let B0:=FixedRawLengthFence.allocation N
    let M:=TotalIngressClosure.machine k; let O:=BodyIngress.machine k
    let c:=initialConfig M B y;let c0:=initialConfig O B0 y;let large:=initialConfig O B y
    d ≤ TotalIngressClosure.deadline k N ∧
      (∀ u,u ≤ d → (M.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ d → (M.run u c).state ≠ M.accept) ∧
      (∀ u,u < d → (M.run u c).state ≠ M.reject ∧
        (∀ b,(M.run u c).state ≠ TotalIngressClosure.old k (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))) ∧
        (∀ mode:Fin 3,(M.run u c).state ≠ TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) ∧
      ((decodePair y=none ∧ d=FixedPairParser.clock N ∧
          M.run d c=⟨M.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩ ∧
          encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false) ∨
       ∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN:pairLength a m=N),
        decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧
        y=(hN ▸ encodePair x w) ∧
        ∃ suffixTicks,d=FixedPairParser.clock N+suffixTicks ∧
          (∀ u,M.run (FixedPairParser.clock N+u) c=TotalIngressClosure.config k (O.run u large)) ∧
          ∃ hBudget:B0 ≤ B,
            FixedPairParser.ConfigExtension hBudget c0 large ∧
            IngressAllocation.Footprint O (C:=B0) y suffixTicks (12*(N+1)^2) ∧
            IngressAllocation.MoveRoom O (C:=B0) y suffixTicks ∧
            IngressAllocation.Trace O hBudget y suffixTicks ∧
            (M.run d c=TotalIngressClosure.config k (IngressAllocation.extendConfig hBudget (O.run suffixTicks c0))) ∧
            (((O.run suffixTicks c0).state=O.reject ∧
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
                  O.run suffixTicks c0=⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address)),H,
                    fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩) ∨
               (∃ positive : 0 < n, S ≤ address ∧
                  (∀ j:Fin W,padRead (Fin.append x w) (address+j.val)=false) ∧
                  (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=
                    some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
                  ((p=S ∧ O.run suffixTicks c0=
                      ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                        Function.update (fun i=>V i.val) H (some false)⟩) ∨
                   (p < S ∧
                      ((r < bitLength n) ∨
                       (bitLength n ≤ r ∧ ∃ v2 v3 v4 v5 residual,
                          CappedWeight.Target.Cap k n r v2 v3 v4 v5 residual)) ∧
                      O.run suffixTicks c0=
                        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                          Function.update (fun i=>Cursor.Target.image V k S n z F i.val) H (some false)⟩))))))) ∧ M.run T c=config k (O.run d c0))) := by
  exact CertificateGuardClosure.raw k
/-- Independent full all-row embedding contract. -/
theorem check_component_rows (k : Nat) :
    Function.Injective (old k) ∧
    old k (TotalIngressClosure.machine k).accept=(machine k).accept ∧
    old k (TotalIngressClosure.machine k).reject=(machine k).reject ∧
    ∀ (s:Fin (TotalIngressClosure.machine k).stateCount) (b:Option Bool),
      (machine k).step (old k s) b=
        (old k (((TotalIngressClosure.machine k).step s b).1),((TotalIngressClosure.machine k).step s b).2) := by
  exact CertificateGuardClosure.component_rows k
open Lean Elab Command
run_cmd do
  let found:=(←getEnv).constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.CertificateGuardClosure.Machine." && n.toString.endsWith ".CertificateGuardClosure.raw"
  match found with
  | [(n,.defnInfo ci)]=>
    logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `guardRawCore n::st.openDecls}
  | _=>throwError "Nonunique fixed original comparator ROM definition {found.map Prod.fst}"
#check (guardRawCore : Fin 67 → Option Bool → Fin 67 × Option Bool × Move)
/-- Full independent equation for the lazily generated comparator definition. -/
theorem check_guard_equation : guard =
    ({stateCount:=67,start:=⟨64,by decide⟩,accept:=⟨65,by decide⟩,reject:=⟨66,by decide⟩,
      accept_ne_reject:=by decide,rawStep:=guardRawCore} : UniformTM) := by
  exact CertificateGuardClosure.guard.eq_1
/-- Full independent original content-relation equation, including its exact
certificate guard and the dependent certificate cast. -/
theorem check_content_equation :
    ∀ {threshold:Nat → Nat} (codec:TreeCircuitWitnessCodec threshold) (a m:Nat)
      (query:Bitstring a) (cert:Bitstring m),
      PartAEndpoint.contentWitnessRelation codec a m query cert=
        if h:m=Pnp3.ComplexityInterfaces.certificateLength a 1 then
          contentSemanticAccepts codec (PartAEndpoint.concatV1ToPrefixBitVec query (h ▸ cert))
        else false := by
  intro threshold codec a m query cert
  exact PartAEndpoint.contentWitnessRelation.eq_1 codec a m query cert
/-- Full independent exact threshold-family equation; no prefix-language substitution. -/
theorem check_threshold_equation (k:Nat) :
    PartAEndpoint.thresholdContentWitnessRelation k=
      PartAEndpoint.contentWitnessRelation (treeCircuitWitnessCodec (thresholdPoly k)) := by
  exact PartAEndpoint.thresholdContentWitnessRelation.eq_1 k
#check (guard : UniformTM)
#check (machine : Nat → UniformTM)
#check (old : (k:Nat) → Fin (TotalIngressClosure.machine k).stateCount → Fin (machine k).stateCount)
#check (@config : (k N B:Nat) → Config (TotalIngressClosure.machine k).stateCount N B → Config (machine k).stateCount N B)
#check (allocation : Nat → Nat → Nat)
#check (deadline : Nat → Nat → Nat)
#check (Target.Frontier : (k N:Nat) → Bitstring N → Nat → Prop)
#check (Target.Raw : Nat → Prop)
end CertificateGuardClosure.Audit
#print axioms CertificateGuardClosure.guard
#print axioms CertificateGuardClosure.machine
#print axioms CertificateGuardClosure.old
#print axioms CertificateGuardClosure.config
#print axioms CertificateGuardClosure.allocation
#print axioms CertificateGuardClosure.deadline
#print axioms CertificateGuardClosure.Target.Frontier
#print axioms CertificateGuardClosure.Target.Raw
#print axioms CertificateGuardClosure.wrong_length
#print axioms CertificateGuardClosure.wrong_length_mirror
#print axioms CertificateGuardClosure.exists_canonical
#print axioms CertificateGuardClosure.exists_canonical_mirror
#print axioms CertificateGuardClosure.raw
#print axioms CertificateGuardClosure.component_rows
#print axioms CertificateGuardClosure.Audit.check_raw
#print axioms CertificateGuardClosure.Audit.check_component_rows
#print axioms CertificateGuardClosure.guard.eq_1
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation.eq_1
#print axioms Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation.eq_1
#print axioms CertificateGuardClosure.Audit.check_guard_equation
#print axioms CertificateGuardClosure.Audit.check_content_equation
#print axioms CertificateGuardClosure.Audit.check_threshold_equation
