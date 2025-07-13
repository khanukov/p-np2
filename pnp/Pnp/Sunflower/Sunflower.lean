import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Pnp.BoolFunc

open Classical
open Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-! ### Basic definitions -/

/-- A *sunflower* (a.k.a. Δ-system) inside a family `𝓢`: a subfamily `𝓣`
    (of size `p`) whose members all have the same pairwise intersection
    (the *core*). -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : 𝓣.card = p
  pairwise_inter :
    ∀ A ∈ 𝓣, ∀ B ∈ 𝓣, A ≠ B → A ∩ B = core

/-- Abbreviation: a `p`-sunflower inside `𝓢`. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, ∃ core, IsSunflower (α := α) p 𝓣 core ∧ ∀ A ∈ 𝓣, A.card = w

/-- **Short sunflower lemma.**
If a family `𝒜` contains at least `p` pairwise distinct sets of size `w`,
then there exists a subfamily `T : Finset (Finset α)` of cardinality `p`
and an intersection `core` (possibly empty) such that
`IsSunflower p T core` holds.  We do not prove the optimal bound, only
existence. -/
lemma sunflower_exists_easy
    (𝒜 : Finset (Finset α)) (w p : ℕ) (hw : ∀ A ∈ 𝒜, A.card = w)
    (hcard : p ≤ 𝒜.card) (hp : 2 ≤ p) :
    ∃ T ⊆ 𝒜, ∃ core, IsSunflower (α := α) p T core := by
  classical
  -- pick any `p` distinct sets
  obtain ⟨T, hsub, hcardT⟩ :=
    Finset.exists_subset_card_eq (s := 𝒜) (n := p) (by simpa using hcard)
  -- the intersection of all sets in `T` will serve as the core
  let core : Finset α :=
    (Finset.interFinset T).getD (Finset.card_pos.2 (by
      have : T.Nonempty := by
        have : 0 < T.card := by
          simpa [hcardT] using (Nat.zero_lt_of_lt $ Nat.succ_le_of_lt hp)
        simpa [Finset.card_eq_zero] using this
      exact ⟨∅, by simp⟩))
  refine ⟨T, hsub, ?_⟩
  refine ⟨by simpa [hcardT], ?_⟩
  intro A hA B hB hAB
  have hA_in : A ∈ T := hA
  have hB_in : B ∈ T := hB
  -- by definition `core` is the intersection of all sets in `T`
  have hcoreA : core ⊆ A := by
    intro x hx
    have : x ∈ ⋂₀ (T : Set (Finset α)) := by
      change x ∈ (Finset.interFinset T)
      simpa using hx
    simpa using this
  have hcoreB : core ⊆ B := by
    intro x hx
    have : x ∈ ⋂₀ (T : Set (Finset α)) := by
      change x ∈ (Finset.interFinset T)
      simpa using hx
    simpa using this
  -- show equality of sets
  ext x
  constructor
  · intro hx
    have hxA : x ∈ A := by
      have : x ∈ A ∩ B := by
        have : x ∈ core := by
          have : x ∈ (Finset.interFinset T) := by
            change x ∈ ⋂₀ (T : Set (Finset α))
            have : x ∈ core := hx
            simpa using this
          simpa using this
        have : x ∈ A := hcoreA this
        simpa using this
      have : x ∈ core := by
        have : x ∈ ⋂₀ (T : Set (Finset α)) := by
          change x ∈ (Finset.interFinset T)
          simpa using hx
        change x ∈ core
        simpa using this
      simpa
  · intro hx
    have : x ∈ core := by
      exact hx
    have : x ∈ A ∧ x ∈ B := by
      have : x ∈ ⋂₀ (T : Set (Finset α)) := by
        change x ∈ (Finset.interFinset T)
        simpa using hx
      have : x ∈ A := by
        have h := Set.mem_iInter.1 this A hA_in
        simpa using h
      have : x ∈ B := by
        have h := Set.mem_iInter.1 this B hB_in
        simpa using h
      exact ⟨this, ‹x ∈ B›⟩
    simpa [Finset.mem_inter] using this
\nend Sunflower\n
