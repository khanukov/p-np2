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

/-!
Additional small facts about sunflower families.  These are
convenient when reasoning about the petals of an existing
`SunflowerFam`.  They avoid repeatedly rewriting with
`SunflowerFam.tsize`.
-/
namespace SunflowerFam

variable {n t : ℕ}

lemma petals_nonempty {S : SunflowerFam n t} (ht : 0 < t) :
    S.petals.Nonempty := by
  rw [← Finset.card_pos]
  rw [S.tsize]
  exact ht

/--
When a sunflower family contains two distinct petals, its core is strictly
smaller than each of those petals.  This basic combinatorial fact is convenient
when reasoning about dimensions of subcubes extracted from the sunflower.
-/
lemma core_card_lt_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    S.core.card < P₁.card := by
  classical
  -- The core is always contained in any petal.
  have hsub : S.core ⊆ P₁ := S.sub_core _ h₁
  -- Hence its cardinality is bounded by that of the petal.
  have hle : S.core.card ≤ P₁.card := Finset.card_le_card hsub
  -- Show that equality of cardinalities would force the two petals to coincide.
  have hneq : S.core.card ≠ P₁.card := by
    intro hEq
    -- Convert the inclusion into an equality of sets.
    have hcore_eq : S.core = P₁ :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hEq])
    -- From the sunflower property we deduce `P₁ ⊆ P₂`.
    have hsubset : P₁ ⊆ P₂ := by
      have htmp : P₁ ∩ P₂ = P₁ := by
        simpa [hcore_eq] using S.pairwise_core P₁ h₁ P₂ h₂ hne
      have hsubset_inter : P₁ ∩ P₂ ⊆ P₂ := Finset.inter_subset_right
      simpa [htmp] using hsubset_inter
    -- Equal cardinalities force the two petals to coincide.
    have hcardle : P₂.card ≤ P₁.card := by simpa [hcard]
    have : P₁ = P₂ := Finset.eq_of_subset_of_card_le hsubset hcardle
    exact hne this
  exact lt_of_le_of_ne hle hneq

/-
If a sunflower family contains two distinct petals of equal cardinality,
then the common core is strictly contained in each of those petals.  This
reformulation of `core_card_lt_of_two_petals` exposes the set-theoretic
relationship which is often more convenient to exploit directly.
-/
lemma core_ssubset_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    S.core ⊂ P₁ := by
  classical
  -- The core is contained in any petal by definition.
  have hsub : S.core ⊆ P₁ := S.sub_core _ h₁
  -- Cardinality considerations rule out equality of `core` and `P₁`.
  have hneq : S.core ≠ P₁ := by
    intro hEq
    have hlt := core_card_lt_of_two_petals (S := S)
      (P₁ := P₁) (P₂ := P₂) h₁ h₂ hcard hne
    simpa [hEq] using hlt
  -- Together these facts yield the desired strict inclusion.
  exact (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hneq⟩

end SunflowerFam

end Sunflower

