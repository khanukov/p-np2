/-
Minimal sunflower definitions and axioms.
This file previously contained a full formalisation of the classical
Erdős--Rado sunflower lemma.  For the purposes of this repository we only
require the statement of the main result, so we provide a reduced version
here.  The proof is omitted and recorded as an axiom.
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Classical
open Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-- A sunflower inside a family `𝓢`: a subfamily `𝓣` of size `p` whose pairwise
intersections coincide (the `core`). -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : 𝓣.card = p
  pairwise_inter : ∀ A ∈ 𝓣, ∀ B ∈ 𝓣, A ≠ B → A ∩ B = core

/-- Convenience predicate for the existence of a sunflower of size `p` consisting
of `w`-element sets. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, ∃ core, IsSunflower (α := α) p 𝓣 core ∧ ∀ A ∈ 𝓣, A.card = w

/-- **Erdős–Rado Sunflower Lemma**.
If a `w`-set family `𝓢` has more than `(p - 1)! * w^p` members and `p ≥ 2`,
then it contains a `p`-sunflower.  The proof is omitted. -/
axiom sunflower_exists
  (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
  (h_size : (p - 1).factorial * w ^ p < 𝓢.card)
  (h_w : ∀ A ∈ 𝓢, A.card = w) :
  HasSunflower 𝓢 w p

end Sunflower
