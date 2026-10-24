import PhysicalCallerClosure.ControllerSurface
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
/-- Proof specification only. The constructor/rows never call this function.
The persistent navigation mark is included in marks; five new metadata cells end false. -/
def callerImage (T : Nat  →  Option Bool) (S z n F r g W M marks : Nat) (beta : Fin n  →  Bool)
    (nodes used remaining quota : Nat) : Nat  →  Option Bool := fun i=>
  let L:=S+z+2
  let H:=L+n+1
  if h:L < i  ∧  i < H then some (beta ⟨H-1-i,by dsimp only [H]at h;omega⟩)
  else if H < i  ∧  i < F then if i ≤ H+marks then some true else none
  else if SerializedBody.delimiter F r n 12 < i  ∧  i < SerializedBody.delimiter F r n 12+6 then some false
  else SerializedBody.image T F r n g W (S-min M S) nodes used remaining quota i
/-- Ghost specification of the actual row-entry ABI, never runtime advice. -/
private def rowImage (T : Nat  →  Option Bool)
    (S z n F r g W M A Q row : Nat) (source : Fin S  →  Bool) : Nat  →  Option Bool := fun i=>
  let D:=SerializedBody.delimiter F r n 12
  let tableVirtual:=decide (S ≤ A+row)
  let tableBit:=padRead source (A+row)
  let anchorVirtual:=decide (S ≤ M)
  let anchorBit:=padRead source (M-1)
  if i=D+1 then some tableVirtual
  else if i=D+2 then some tableBit
  else if i=D+3 then some anchorVirtual
  else if i=D+4 then some (if M < S then anchorBit else false)
  else if i=D+5 then some false
  else if i=A+row  ∧  i < S then none
  else if M < S  ∧  i=M-1 then none
  else if i=M  ∧  i < S then none
  else callerImage T S z n F r g W M (max 1 (Q-row)) (Pnp3.Core.vecOfNat n row) 0 0 W g i
/-- Complete prepared physical caller target. Budget Q is actual H-right marks,
not a host cutoff. A shortage is an explicit physical abort arm. No AST/success premise.
The all-rows success is WORK only; prefix/inactive-padding and final verdict are separate. -/
def CallerRows (k : Nat) : Prop :=
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
                fun h=>rowImage T S z n F r g W M A Q i.val source h.val⟩)  ∧
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
                circuit.size used (W-used) 0 i.val⟩)))
end PhysicalCallerClosure
