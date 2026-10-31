import VirtualFinalClosure.GuardMeaning
namespace VirtualFinalClosure.GuardPayloadMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
set_option autoImplicit false
/-- On a genuinely virtual witness branch the STRICT W-bit payload window
contains every remaining physical source cell and only virtual zeros beyond it.
This is the exact semantic predicate computed by the native padding scan. -/
private theorem exact_window {S : Nat} (word : Bitstring S) (p ell W : Nat)
    (virtual : S ≤ p+ell+W) :
    (∀ j : Fin W,padRead word (p+ell+j.val)=false) ↔
      ∀ i,min (p+ell) S ≤ i → i < S → padRead word i=false := by
  constructor
  · intro zero i lo hi
    have start : p+ell ≤ i:=by omega
    have width : i-(p+ell) < W:=by omega
    have atZero:=zero ⟨i-(p+ell),width⟩
    simpa only [show p+ell+(i-(p+ell))=i by omega] using atZero
  · intro zero j
    by_cases physical : p+ell+j.val < S
    · exact zero _ (by omega) physical
    · exact padRead_ge word (by omega)
/-- The occupied source version of exact_window. NONE and Some false remain
distinct in the machine; the equality here is solely a codec-side statement. -/
private theorem source_window {S : Nat} (word : Bitstring S) (bits : Nat → Bool)
    (p ell W : Nat) (same : ∀ (i : Nat) (hi : i < S),bits i=word ⟨i,hi⟩)
    (virtual : S ≤ p+ell+W) :
    (∀ j : Fin W,padRead word (p+ell+j.val)=false) ↔
      ∀ i,min (p+ell) S ≤ i → i < S → bits i=false := by
  rw [exact_window word p ell W virtual]
  constructor
  · intro zero i lo hi
    rw [same i hi]
    have atZero:=zero i lo hi
    dsimp only [padRead] at atZero
    rwa [dif_pos hi] at atZero
  · intro zero i lo hi
    dsimp only [padRead]
    rw [dif_pos hi]
    exact (same i hi).symm.trans (zero i lo hi)
#print axioms exact_window
#print axioms source_window
end VirtualFinalClosure.GuardPayloadMeaning
