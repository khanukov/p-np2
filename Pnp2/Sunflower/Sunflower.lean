import Mathlib.Data.Nat.Factorial.Basic
import Pnp2.Boolcube

/-! # Classical sunflower lemma

This module provides a minimal interface for the classical
Erdős–Rado sunflower lemma.  The combinatorial proof is omitted and the
result is recorded as an axiom so that other parts of the development
can rely on the statement without depending on a particular proof.
-/

open Classical Finset

noncomputable section

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-- A `p`‑sunflower inside a family `𝓢` consists of a subfamily `𝓣` of
cardinality `p` whose pairwise intersections all coincide with a set
`core`. -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : 𝓣.card = p
  pairwise_inter :
    ∀ ⦃A⦄, A ∈ 𝓣 → ∀ ⦃B⦄, B ∈ 𝓣 → A ≠ B → A ∩ B = core

/-- A family `𝓢` *has* a `p`‑sunflower of width `w` if it contains a
subfamily with the sunflower property and all petals have size `w`. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, ∃ core, IsSunflower (α := α) p 𝓣 core ∧ ∀ A ∈ 𝓣, A.card = w

/-- **Erdős–Rado sunflower lemma** (axiom).  If a finite family of
`w`‑sets has more than `(p - 1)! * w^p` members, then it contains a
`p`‑sunflower. -/
axiom sunflower_exists
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : (p - 1).factorial * w ^ p < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w p

/-- Convenient wrapper for the sunflower lemma when the family is
already known to consist of `w`‑sets. -/
lemma sunflower_exists_of_fixedSize
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_cards : ∀ A ∈ 𝓢, A.card = w)
    (h_big  : 𝓢.card > (p - 1).factorial * w ^ p) :
    HasSunflower 𝓢 w p :=
  sunflower_exists 𝓢 w p hw hp
    (by simpa using h_big) h_cards

/-! ## Structures for the cover algorithm -/

open Boolcube

abbrev Petal (n : ℕ) := Finset (Fin n)

/-- Data of a sunflower family in the Boolean cube. -/
structure SunflowerFam (n t : ℕ) where
  petals : Finset (Petal n)
  tsize  : petals.card = t
  core   : Petal n
  sub_core : ∀ P ∈ petals, core ⊆ P
  pairwise_core :
    ∀ P₁ ∈ petals, ∀ P₂ ∈ petals, P₁ ≠ P₂ → P₁ ∩ P₂ = core

namespace SunflowerFam

variable {n w t : ℕ}

/-- Existence of a sunflower family given a large collection of petals. -/
lemma exists_of_large_family
    {F : Finset (Petal n)}
    (hw : 0 < w) (ht : 2 ≤ t)
    (hcard : ∀ S ∈ F, S.card = w)
    (hbig : F.card > Nat.factorial (t - 1) * w ^ t) :
    ∃ S : SunflowerFam n t, S.petals ⊆ F := by
  classical
  -- Apply the classical sunflower lemma to obtain a `t`-sunflower inside `F`.
  rcases sunflower_exists (𝓢 := F) (w := w) (p := t) hw ht
      (by simpa using hbig) hcard with
    ⟨pet, hsub, core, hSun, hcards⟩
  -- Break down the `IsSunflower` structure into its two components.
  rcases hSun with ⟨hsize, hpair⟩
  -- We now show that the common `core` is contained in every petal.
  have hsub_core : ∀ P ∈ pet, core ⊆ P := by
    intro P hP
    -- Show that the family has at least two petals.
    have h_two : 1 < pet.card := by
      have h : 2 ≤ pet.card := by simpa [hsize] using ht
      have h12 : 1 < 2 := by decide
      exact lt_of_lt_of_le h12 h
    -- Obtain a different petal `Q` using `exists_ne_of_one_lt_card`.
    obtain ⟨Q, hQ, hne⟩ := Finset.exists_ne_of_one_lt_card h_two P
    -- The sunflower property says `P ∩ Q = core`, hence `core ⊆ P`.
    have hPQ := hpair (A := P) hP (B := Q) hQ (Ne.symm hne)
    simpa [hPQ] using (Finset.inter_subset_left : P ∩ Q ⊆ P)
  -- Assemble the final `SunflowerFam` structure.
  refine ⟨⟨pet, hsize, core, hsub_core, ?_⟩, hsub⟩
  -- The pairwise intersection condition follows directly from `hpair`.
  intro P₁ h₁ P₂ h₂ hne
  exact hpair (A := P₁) h₁ (B := P₂) h₂ hne

end SunflowerFam

end Sunflower

