import RuntimeBitLength.Raw
namespace BitLengthDriver
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
/-- Positive-width prepared full driver. Raw legacy endpoint is EXACT immutable H.FullRaw. -/
def Prepared (k N B L n Q F r : Nat) (X : Nat → Option Bool) : Prop :=
  0 < n → 0 < r → 0 < Q → ∀ (room : L+n+1+Q < F),
  X L=none → (∀ i, L < i → i < L+n+1 → X i=some true) → X (L+n+1)=none →
  (∀ i, L+n+1 < i → i ≤ L+n+1+Q → X i=some true) →
  (∀ i, L+n+1+Q < i → i < F → X i=none) → X F=some false → X (F+1)=none →
  (∀ i, F+1 < i → i < F+r+2 → X i=some true) → X (F+r+2)=none →
  (∀ i, F+r+2 < i → i < F+r+n+3 → X i=some false) → X (F+r+n+3)=none →
  (∀ i, F+r+n+3 < i → i < F+2*r+n+4 → X i=some false) → X (F+2*r+n+4)=none →
  ∀ (fit : F+5*r+n+7 < tapeLength N B),
  ∃ (t : Nat) (h : (if bitLength n ≤ r then L else F+r+n+3) < tapeLength N B),
    t ≤ 4096*(n+r+1)^2*(F+5*r+n+8) ∧
    (∀ u, u < t → ∀ s ∈ [308,250,304],
      ((Cursor.machine k).run u (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state ≠ Cursor.q k s) ∧
    (Cursor.machine k).run t (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
        ⟨if bitLength n ≤ r then L else F+r+n+3,h⟩,
        fun i => RuntimeBitLength.Target.fullImage X L n F r i.val⟩
end BitLengthDriver
