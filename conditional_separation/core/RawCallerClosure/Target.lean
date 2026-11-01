import RawCallerClosure.Embedding
namespace RawCallerClosure.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Exact per-time old all-input guard outcome. This is a conclusion, never a runtime premise. -/
def Prelude (k N : Nat) (y : Bitstring N) (T : Nat) : Prop :=
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
          CertificateGuardClosure.Target.Frontier k N y d ∧ M.run T c=CertificateGuardClosure.config k (O.run d c0)))

/-- Complete original caller semantic result on the actual raw run, with absolute paid times. -/
def RowsResult (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool)
    (T : Nat → Option Bool) (hH : S+z+2+n+1 < tapeLength R B)
    (c : Config (machine k).stateCount R B) (t : Nat) : Prop :=
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

/-- Every raw word: literal sound ingress reject, preserved virtual WORK, or
complete NORMAL all-row caller. No parser/header/frame/accepted premise is supplied. -/
def Raw (k : Nat) : Prop :=
  ∀ (N : Nat) (y : Bitstring N),
  let B:=allocation k N; let C:=initialConfig (machine k) B y
  let G:=CertificateGuardClosure.machine k
  let oldC:=initialConfig G B y
  let work (b : Bool):=CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))
  ∃ pre t, Prelude k N y pre ∧ pre ≤ t ∧ t ≤ deadline k N ∧
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
          RowsResult k B N S z n r (n^k+k) W address (9+2*z) Q (Fin.append x w) I hH C t))
end RawCallerClosure.Target
