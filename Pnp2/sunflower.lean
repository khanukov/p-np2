import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card

/-!
Minimal Sunflower lemma interface for the migrated `Pnp2` library.
The full classical proof is omitted; we record only the statements
used elsewhere in the repository.  This keeps the module lightweight
while ensuring compatibility with earlier versions.
-/

open Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-- `IsSunflower p T core` means that `T` is a family of `p` sets whose
    pairwise intersections coincide with `core`.  The precise structure
    matches the previous development, but proofs are omitted here. -/
structure IsSunflower (p : ℕ) (T : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : T.card = p
  pairwise_inter :
    ∀ A ∈ T, ∀ B ∈ T, A ≠ B → A ∩ B = core

/-- A family `S` *has* a sunflower of size `p` and set size `w` if there
    exists a subfamily `T ⊆ S` together with a common intersection `core`
    such that every member of `T` has size `w` and forms a sunflower. -/
def HasSunflower (S : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ T ⊆ S, ∃ core, IsSunflower (α := α) p T core ∧ ∀ A ∈ T, A.card = w

/-- **Erdős–Rado Sunflower Lemma** (statement only).  If a `w`‑set family
    has more than `(p - 1)! * w ^ p` members, then it contains a
    `p`-sunflower.  The proof is omitted in this lightweight version and
    provided as an axiom. -/
axiom sunflower_exists
  (S : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
  (h_size : (p - 1).factorial * w ^ p < S.card)
  (h_w : ∀ A ∈ S, A.card = w) :
  HasSunflower S w p

/-- Convenience wrapper specialised to the Boolean cube.  We simply
    delegate to `sunflower_exists`. -/
lemma sunflower_exists_of_fixedSize
  (S : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
  (h_cards : ∀ A ∈ S, A.card = w)
  (h_big : S.card > (p - 1).factorial * w ^ p) :
  HasSunflower S w p := by
  have h_bound : (p - 1).factorial * w ^ p < S.card :=
    lt_of_le_of_ne (Nat.le_of_lt h_big)
      (by simpa [h_big.ne] using h_big.ne.symm)
  exact sunflower_exists S w p hw hp h_bound h_cards

end Sunflower
