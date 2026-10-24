import RawCallerClosure.Driver
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Independently explicit entire raw proposition: predecessor framing and every
normal decoder, paid-start, full-tape and final comparison branch are expanded. -/
theorem raw_mirror (k : Nat) :
∀ (N : Nat) (y : Bitstring N),
  let B:=allocation k N; let C:=initialConfig (machine k) B y
  let G:=CertificateGuardClosure.machine k
  let oldC:=initialConfig G B y
  let work (b : Bool):=CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))
  ∃ pre t, (let T:=pre;
let B:=CertificateGuardClosure.allocation k N;let M:=CertificateGuardClosure.machine k;let O:=TotalIngressClosure.machine k
    let c:=initialConfig M B y;let c0:=initialConfig O B y
    T ≤ CertificateGuardClosure.deadline k N ∧
      (∀ u,u ≤ T → (M.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ T → (M.run u c).state ≠ M.accept) ∧
      (∀ u,u < T → (M.run u c).state ≠ M.reject ∧
        (∀ b,(M.run u c).state ≠ CertificateGuardClosure.old k (TotalIngressClosure.old k
          (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))) ∧
        (∀ mode:Fin 3,(M.run u c).state ≠ CertificateGuardClosure.old k (TotalIngressClosure.old k
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
          M.run g c=CertificateGuardClosure.config k c0 ∧
          (∀ u,M.run (g+u) c=CertificateGuardClosure.config k (O.run u c0)) ∧
          (let t:=d;
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
) ∧ M.run T c=CertificateGuardClosure.config k (O.run d c0)))
) ∧ pre ≤ t ∧ t ≤ deadline k N ∧
    (∀ u,u ≤ pre → (machine k).run u C=oldConfig k (G.run u oldC)) ∧
    (∀ u,u ≤ t → ((machine k).run u C).state≠(machine k).accept) ∧
    (∀ u,u < t → ((machine k).run u C).state≠(machine k).reject ∧
      ((machine k).run u C).state≠callerState k (PhysicalCallerClosure.rowsDone k) ∧
      (∀ b,((machine k).run u C).state≠old k (work b))) ∧
    ((t=pre ∧ (G.run pre oldC).state=G.reject ∧
        (machine k).run t C=oldConfig k (G.run pre oldC) ∧
        encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false) ∨
      (t=pre ∧ (∃ b,(G.run pre oldC).state=work b) ∧
        (machine k).run t C=oldConfig k (G.run pre oldC)) ∨
      (∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN:pairLength a m=N),
        decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
        ∃ (n z : Nat),
        FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
        let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N
        let B0:=FixedRawLengthFence.allocation N
        let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
        let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
        let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
        let V:=Stream.Target.image U S z n (9+2*z) Q Q false
        let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
        let Y:=RuntimeBitLength.Target.fullImage X L n F r
        let Z:=AllArityBitLength.Target.seedImage Y F r n
        let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
          F r n (n^k+k) (bitLength W) 0 0 W
        p<S ∧ bitLength n ≤ r ∧ W ≤ r ∧
        n < FixedRawLengthFence.capacity a m z ∧ S+z+n+3+Q < F ∧
        ∃ hH:S+z+2+n+1 < tapeLength N B,
          (machine k).run pre C=callerConfig k
            ⟨PhysicalCallerClosure.oldState k (BodyIngress.body k
              (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address))),⟨S+z+2+n+1,hH⟩,
              fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩ ∧
          (let R:=N;let g:=n^k+k;let M:=address;let A:=9+2*z;
let source:=Fin.append x w;let T:=I;let c:=C;
let H:=S+z+2+n+1; let F:=FixedRawLengthFence.fencePos R
  let bits:=SerializedBody.window source M W;
    (∀ u,u ≤ t  →  ((machine k).run u c).state≠(machine k).accept)  ∧
    (∀ u,u < t  →  ((machine k).run u c).state≠(machine k).reject  ∧
      ((machine k).run u c).state≠callerState k (PhysicalCallerClosure.rowsDone k))  ∧
    match decodeCircuitFull n (bitLength n) bits with
    | none=>(machine k).run t c=⟨(machine k).reject,⟨H,hH⟩,
        fun i=>PhysicalCallerClosure.callerImage T S z n F r g W M Q (Pnp3.Core.vecOfNat n 0) 0 0 0 0 i.val⟩
    | some (circuit,tail)=>
      (¬circuit.size ≤ g  ∧  (machine k).run t c=⟨(machine k).reject,⟨H,hH⟩,
        fun i=>PhysicalCallerClosure.callerImage T S z n F r g W M Q (Pnp3.Core.vecOfNat n 0) 0 0 0 0 i.val⟩) ∨
      (circuit.size ≤ g  ∧
        let used:=W-tail.length
        let good (i : Nat):=padRead source (A+i)=Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n i)
        used ≤ W  ∧  tail=bits.drop used  ∧
        (∃ starts:Fin (min (2^n) Q)  →  Nat,
          (∀ i,(∀ j,j < i.val  →  good j)  →  starts i < t  ∧
            (machine k).run (starts i) c=
              ⟨callerState k (PhysicalCallerClosure.evalState k (SerializedBody.entry (SerializedBody.sourceMode source M))),⟨H,hH⟩,
                fun h=>(fun address : Nat=>
let D:=SerializedBody.delimiter F r n 12
  let tableVirtual:=decide (S ≤ A+i.val)
  let tableBit:=padRead source (A+i.val)
  let anchorVirtual:=decide (S ≤ M)
  let anchorBit:=padRead source (M-1)
  if address=D+1 then some tableVirtual
  else if address=D+2 then some tableBit
  else if address=D+3 then some anchorVirtual
  else if address=D+4 then some (if M < S then anchorBit else false)
  else if address=D+5 then some false
  else if address=A+i.val  ∧  address < S then none
  else if M < S  ∧  address=M-1 then none
  else if address=M  ∧  address < S then none
  else PhysicalCallerClosure.callerImage T S z n F r g W M (max 1 (Q-i.val)) (Pnp3.Core.vecOfNat n i.val) 0 0 W g address
              ) h.val⟩)  ∧
          (∀ i j,i.val < j.val  →  (∀ q,q < j.val  →  good q)  →  starts i < starts j))  ∧
        ((2^n ≤ Q  ∧  (∀ i,i < 2^n  →  good i)  ∧
            (machine k).run t c=⟨callerState k (PhysicalCallerClosure.rowsDone k),⟨H,hH⟩,
              fun i=>PhysicalCallerClosure.callerImage T S z n F r g W M (max 1 (Q-2^n)) (Pnp3.Core.vecOfNat n 0)
                circuit.size used (W-used) 0 i.val⟩) ∨
          (∃ row,row < min (2^n) Q  ∧  (∀ j,j < row  →  good j)  ∧  ¬good row  ∧
            (machine k).run t c=⟨(machine k).reject,⟨H,hH⟩,
              fun i=>PhysicalCallerClosure.callerImage T S z n F r g W M (max 1 (Q-row)) (Pnp3.Core.vecOfNat n row)
                circuit.size used (W-used) 0 i.val⟩) ∨
          (Q < 2^n  ∧  (∀ j,j < Q  →  good j)  ∧
            (machine k).run t c=⟨(machine k).reject,⟨H,hH⟩,
              fun i=>PhysicalCallerClosure.callerImage T S z n F r g W M 1 (Pnp3.Core.vecOfNat n Q)
                circuit.size used (W-used) 0 i.val⟩)))
))) := by
  exact raw k
/-- Full pointwise mirror of the generated equation, owned by Rows. -/
theorem machine_equation_mirror (k : Nat) : machine k=
    FixedPairParser.machine.seq (CertificateGuardClosure.guard.seq
      (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k))) := machine.eq_1 k
/-- Full pointwise mirror of the generated control inclusion equation. -/
theorem callerState_equation_mirror (k : Nat) (s : Fin (PhysicalCallerClosure.callerMachine k).stateCount) :
    callerState k s=FixedPairParser.machine.seqRight _ (CertificateGuardClosure.guard.seqRight _
      (FixedPairParser.machine.seqRight _ s)) := callerState.eq_1 k s
/-- Full pointwise mirror of the generated whole-configuration inclusion equation. -/
theorem callerConfig_equation_mirror (k : Nat) {N B : Nat}
    (c : Config (PhysicalCallerClosure.callerMachine k).stateCount N B) :
    callerConfig k c=⟨callerState k c.state,c.head,c.tape⟩ := callerConfig.eq_1 k c
#print axioms machine.eq_1
#print axioms machine_equation_mirror
#print axioms callerState.eq_1
#print axioms callerState_equation_mirror
#print axioms callerConfig.eq_1
#print axioms callerConfig_equation_mirror
private def pin_Prelude : (k N : Nat) → Bitstring N → Nat → Prop :=
  (show (k N : Nat) → Bitstring N → Nat → Prop from Target.Prelude)
private def pin_RowsResult : (k B R S z n r g W M A Q : Nat) → (Fin S → Bool) →
    (Nat → Option Bool) → (S+z+2+n+1 < tapeLength R B) →
    Config (machine k).stateCount R B → Nat → Prop :=
  (show (k B R S z n r g W M A Q : Nat) → (Fin S → Bool) →
    (Nat → Option Bool) → (S+z+2+n+1 < tapeLength R B) →
    Config (machine k).stateCount R B → Nat → Prop from Target.RowsResult)
private def pin_Raw : Nat → Prop := (show Nat → Prop from Target.Raw)
#print axioms raw
#print axioms raw_mirror
#print axioms Target.Prelude
#print axioms pin_Prelude
#print axioms Target.RowsResult
#print axioms pin_RowsResult
#print axioms Target.Raw
#print axioms pin_Raw
end RawCallerClosure
