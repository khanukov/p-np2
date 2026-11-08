import StandardTMBridgeClosure.Raw
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Full independent actual-step/tape/midpoint proposition, not a Target alias. -/
theorem simulation_full (M : UniformTM) :
  ∀ (N B t : Nat) (y : Bitstring N),
  let c:=initialConfig M B y
  let start : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)):=
    TM0.init (encode (List.ofFn y))
  (∀ u,u < t → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject) →
  (∀ u,u < t → (M.step (M.run u c).state ((M.run u c).tape (M.run u c).head)).2.2=Move.right →
    (M.run u c).head.val+1 < tapeLength N B) →
  (∀ u,u ≤ t → ∃ v,steps M (1+2*u) start=some v ∧ v.q=some ((M.run u c).state,0) ∧ ∀ i : Int,
      v.Tape.nth i=
        if h:0 ≤ ((M.run u c).head.val : Int)+i ∧ ((M.run u c).head.val : Int)+i < (tapeLength N B : Int)
        then (decide (((M.run u c).head.val : Int)+i=0),
          (M.run u c).tape ⟨(((M.run u c).head.val : Int)+i).toNat,by omega⟩)
        else (false,none)) ∧
  (∀ u,u < t →
    let s:=M.run u c
    let a:=M.step s.state (s.tape s.head)
    ∃ v,steps M (2+2*u) start=some v ∧
      v.q=some (a.1,match a.2.2 with | .left=>1 | .stay=>2 | .right=>3) ∧
      ∀ i : Int,v.Tape.nth i=
        if i=0 then (decide (s.head.val=0),a.2.1)
        else if h:0 ≤ (s.head.val : Int)+i ∧ (s.head.val : Int)+i < (tapeLength N B : Int)
        then (decide ((s.head.val : Int)+i=0),s.tape ⟨((s.head.val : Int)+i).toNat,by omega⟩)
        else (false,none)) := by
  exact simulation M
/-- Complete independent same-raw-source/actual-standard-execution proposition. -/
theorem raw_full (k : Nat) :
  ∀ (N : Nat) (y : Bitstring N),
  let M:=NormalFinalClosure.machine2 k
  let G:=RawCallerClosure.allocation k N
  let c:=initialConfig M G y
  let start : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)):=
    TM0.init (encode (List.ofFn y))
  let virtual (b : Bool):=NormalFinalClosure.old2 k (RawCallerClosure.old k
    (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))))
  let O:=RawCallerClosure.machine k
  let oldC:=initialConfig O G y
  let rows:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
  let priorVirtual (b : Bool):=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
  ∃ (d t : Nat) (last : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))),
    (
  d ≤ t ∧ t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
    (∀ u,u ≤ d → (NormalFinalClosure.machine2 k).run u c=
      NormalFinalClosure.config2 k (O.run u oldC)) ∧
    (∀ u,u ≤ d → (O.run u oldC).state≠O.accept) ∧
    (∀ u,u < d → (O.run u oldC).state≠O.reject ∧ (O.run u oldC).state≠rows ∧
      ∀ b,(O.run u oldC).state≠priorVirtual b) ∧
    (∀ u,u < t → ((NormalFinalClosure.machine2 k).run u c).state≠(NormalFinalClosure.machine2 k).accept ∧
      ((NormalFinalClosure.machine2 k).run u c).state≠(NormalFinalClosure.machine2 k).reject ∧
      ∀ b,((NormalFinalClosure.machine2 k).run u c).state≠NormalFinalClosure.old2 k (priorVirtual b)) ∧
    ((t=d ∧ (∃ b,(O.run d oldC).state=priorVirtual b) ∧
      (NormalFinalClosure.machine2 k).run t c=NormalFinalClosure.config2 k (O.run d oldC)) ∨
     (t=d ∧ (O.run d oldC).state=O.reject ∧
      encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false ∧
      (NormalFinalClosure.machine2 k).run t c=NormalFinalClosure.config2 k (O.run d oldC)) ∨
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
      (answer=true ↔ ∃ i,
        readNatBE (padWord (Fin.append x w) (9+2*z+2^n+bitLength W+W)) (9+2*z+2^n) (bitLength W)=some i ∧
        i ≤ W ∧
        (∀ j,j < i → padRead (Fin.append x w) (9+2*z+2^n+bitLength W+j)=
          padRead (Fin.append x w) (9+2*z+2^n+bitLength W+W+j)) ∧
        (∀ j,i ≤ j → j < W → padRead (Fin.append x w) (9+2*z+2^n+bitLength W+j)=false)) ∧
      (NormalFinalClosure.machine2 k).run t c=
        ⟨if answer then (NormalFinalClosure.machine2 k).accept else (NormalFinalClosure.machine2 k).reject,
          ⟨S+z+2+n+1,hH⟩,NormalFinalClosure.Target.cleared (O.run d oldC).tape F r n⟩))
    ) ∧
    1+2*t ≤ N^(4*(4503599627370496*(k+1)+64)+4)+(4*(4503599627370496*(k+1)+64)+4) ∧
    steps M (1+2*t) start=some last ∧ (last.q=some ((M.run t c).state,0) ∧ ∀ i : Int,
      last.Tape.nth i=
        if h:0 ≤ ((M.run t c).head.val : Int)+i ∧ ((M.run t c).head.val : Int)+i < (tapeLength N G : Int)
        then (decide (((M.run t c).head.val : Int)+i=0),
          (M.run t c).tape ⟨(((M.run t c).head.val : Int)+i).toNat,by omega⟩)
        else (false,none)) ∧
    (∀ u,u ≤ t → ∃ v,steps M (1+2*u) start=some v ∧ v.q=some ((M.run u c).state,0) ∧ ∀ i : Int,
      v.Tape.nth i=
        if h:0 ≤ ((M.run u c).head.val : Int)+i ∧ ((M.run u c).head.val : Int)+i < (tapeLength N G : Int)
        then (decide (((M.run u c).head.val : Int)+i=0),
          (M.run u c).tape ⟨(((M.run u c).head.val : Int)+i).toNat,by omega⟩)
        else (false,none)) ∧
    (∀ j,j ≤ 1+2*t → ∃ v,steps M j start=some v) ∧
    (∀ j,j < 1+2*t → ∀ v,steps M j start=some v →
      v.q≠some (M.accept,0) ∧ v.q≠some (M.reject,0) ∧ ∀ b,v.q≠some (virtual b,0)) ∧
    ((∃ b,last.q=some (virtual b,0) ∧ TM0.step (compile M) last≠none) ∨
     (∃ answer : Bool,answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y ∧
       last.q=some ((if answer then M.accept else M.reject),0) ∧
       TM0.step (compile M) last=none)) := by
  exact raw k
/-- The fixed symbol encoding is injective on the original Boolean words. -/
theorem encode_injective : Function.Injective encode := by
  intro a b eq
  have recovered:=congrArg (List.map (fun s : Bool × Option Bool=>s.2.getD false)) eq
  rw [(encoding a).2,(encoding b).2] at recovered
  exact recovered
theorem encode_injective_full : ∀ a b : List Bool,encode a=encode b → a=b := encode_injective
#print axioms simulation
#print axioms simulation_full
#print axioms raw
#print axioms raw_full
#print axioms encode_injective
#print axioms encode_injective_full
end StandardTMBridgeClosure
