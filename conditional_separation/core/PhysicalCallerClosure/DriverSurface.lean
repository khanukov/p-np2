import PhysicalCallerClosure.Driver
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
/-- Full independent all-frame physical caller contract, including every whole tape and paid start. -/
theorem caller_rows_mirror : ∀ k : Nat,
∀ (B R S z n r g W M A Q : Nat) (source : Fin S  →  Bool) (T : Nat  →  Option Bool),
  1 ≤ R  →  r ≤ S  →  S ≤ R  →  g ≤ r  →  0 < W  →  W ≤ r  →  bitLength n ≤ r  →  S-min M S ≤ r  →
  2 ≤ A  →  A ≤ S  →  A+2^n+1 ≤ M  →
  let L:=S+z+2;let H:=L+n+1;let F:=FixedRawLengthFence.fencePos R
  0 < Q  →  H+Q < F  →
  T (A-2)=none  →  T (A-1)=some true  →
  (∀ i,A ≤ i  →  ∀ hi:i < S,T i=some (source ⟨i,hi⟩))  →
  T S=none  →  (∀ i,S < i  →  i < L  →  T i=some false)  →  T L=none  →  T H=none  →
  (∀ j:Fin n,T (H-1-j.val)=some false)  →
  (∀ i,H < i  →  i ≤ H+Q  →  T i=some true)  →
  (∀ i,H+Q < i  →  i < F  →  T i=none)  →  T F=some false  →
  (∀ i,SerializedBody.delimiter F r n 12 < i  →  i ≤ SerializedBody.delimiter F r n 12+6  →  T i=none)  →
  ∀ _fit:SerializedBody.delimiter F r n 12+6 < tapeLength R B,
  ∀ hH:H < tapeLength R B,
  let c : Config (callerMachine k).stateCount R B:=
    ⟨oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),
      ⟨H,hH⟩,fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
  let bits:=SerializedBody.window source M W
  ∃ t,t ≤ 1099511627776*(R+1)^8  ∧
    (∀ u,u ≤ t  →  ((callerMachine k).run u c).state≠(callerMachine k).accept)  ∧
    (∀ u,u < t  →  ((callerMachine k).run u c).state≠(callerMachine k).reject  ∧
      ((callerMachine k).run u c).state≠rowsDone k)  ∧
    match decodeCircuitFull n (bitLength n) bits with
    | none=>(callerMachine k).run t c=⟨(callerMachine k).reject,⟨H,hH⟩,
        fun i=>callerImage T S z n F r g W M Q (Pnp3.Core.vecOfNat n 0) 0 0 0 0 i.val⟩
    | some (circuit,tail)=>
      (¬circuit.size ≤ g  ∧  (callerMachine k).run t c=⟨(callerMachine k).reject,⟨H,hH⟩,
        fun i=>callerImage T S z n F r g W M Q (Pnp3.Core.vecOfNat n 0) 0 0 0 0 i.val⟩) ∨
      (circuit.size ≤ g  ∧
        let used:=W-tail.length
        let good (i : Nat):=padRead source (A+i)=Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n i)
        used ≤ W  ∧  tail=bits.drop used  ∧
        (∃ starts:Fin (min (2^n) Q)  →  Nat,
          (∀ i,(∀ j,j < i.val  →  good j)  →  starts i < t  ∧
            (callerMachine k).run (starts i) c=
              ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,hH⟩,
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
  else callerImage T S z n F r g W M (max 1 (Q-i.val)) (Pnp3.Core.vecOfNat n i.val) 0 0 W g address
              ) h.val⟩)  ∧
          (∀ i j,i.val < j.val  →  (∀ q,q < j.val  →  good q)  →  starts i < starts j))  ∧
        ((2^n ≤ Q  ∧  (∀ i,i < 2^n  →  good i)  ∧
            (callerMachine k).run t c=⟨rowsDone k,⟨H,hH⟩,
              fun i=>callerImage T S z n F r g W M (max 1 (Q-2^n)) (Pnp3.Core.vecOfNat n 0)
                circuit.size used (W-used) 0 i.val⟩) ∨
          (∃ row,row < min (2^n) Q  ∧  (∀ j,j < row  →  good j)  ∧  ¬good row  ∧
            (callerMachine k).run t c=⟨(callerMachine k).reject,⟨H,hH⟩,
              fun i=>callerImage T S z n F r g W M (max 1 (Q-row)) (Pnp3.Core.vecOfNat n row)
                circuit.size used (W-used) 0 i.val⟩) ∨
          (Q < 2^n  ∧  (∀ j,j < Q  →  good j)  ∧
            (callerMachine k).run t c=⟨(callerMachine k).reject,⟨H,hH⟩,
              fun i=>callerImage T S z n F r g W M 1 (Pnp3.Core.vecOfNat n Q)
                circuit.size used (W-used) 0 i.val⟩))) := by
  intro k
  exact caller_rows k
#print axioms caller_rows
#print axioms caller_rows_mirror
end PhysicalCallerClosure
