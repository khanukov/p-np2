/-
sunflower.lean
===============

A **self‑contained** file formalising *just enough* of the classical
Erdős–Rado Sunflower Lemma for the FCE‑Lemma project.

* We work with **finite sets** (`Finset α`) over an arbitrary type `α`
  with decidable equality.

* A **`w`‑set family** is a `Finset (Finset α)` each of whose members has
  cardinality **exactly** `w`.

* A **sunflower of size `p`** (a.k.a. *`p`‑sunflower*) is a sub‑family
  whose pairwise intersections are identical (the *core*).

The classical bound we need (and use downstream) is:

> If a `w`‑set family has more than `(p - 1)! * w^p` members,
> then it contains a `p`‑sunflower.

We *state* and export this lemma as `sunflower_exists`.  A complete,
fully‑formal proof is deferred (`sorry`) so that all dependent modules
compile immediately.  Replacing the `sorry` with a full proof is task
**C** in the overall roadmap.

The lemma’s **interface is frozen**—other files (`cover.lean` etc.)
rely only on its statement, not on the proof term.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Classical
open Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-! ### Basic definitions -/

/-- A *sunflower* (a.k.a. Δ‑system) inside a family `𝓢`:
    a sub‑family `𝓣` (of size `p`) whose members all have the **same**
    pairwise intersection (the *core*).  We store both `𝓣` and its
    intersection `core` for convenience.                                                  -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : 𝓣.card = p
  pairwise_inter :
    ∀ A ∈ 𝓣, ∀ B ∈ 𝓣, A ≠ B → A ∩ B = core

/-- Abbreviation: a `p`‑sunflower is *some* `𝓣` satisfying `IsSunflower`. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, ∃ core, IsSunflower (α := α) p 𝓣 core ∧ ∀ A ∈ 𝓣, A.card = w


/-- **Короткая версия** sunflower‑леммы:  
    если семья `𝒜` содержит хотя бы `p` попарочно *различных* `w`‑множеств,
    то существует подсемейство `T : Finset (Finset α)` размера `p`
    и некоторое его пересечение `core` (возможно, пустое)
    такие, что `IsSunflower p T core`.
    (Мы не доказываем оптимальную оценку, нам достаточно факта существования.) -/
lemma sunflower_exists_easy
    (𝒜 : Finset (Finset α)) (w p : ℕ) (hw : ∀ A ∈ 𝒜, A.card = w)
    (hcard : p ≤ 𝒜.card) (hp : 2 ≤ p) :
    ∃ T ⊆ 𝒜, ∃ core, IsSunflower (α:=α) p T core := by
  classical
  -- возьмём любые p разных множеств
  obtain ⟨T, hsub, hcardT⟩ :=
    (Finset.exists_subset_card_eq p).2 (by
      simpa using hcard)
  -- у пересечения всех множеств T будет нужное свойство
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
  -- по определению `core` – пересечение всех множеств из T
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
  -- покажем равенства множеств
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
/-! ### The classical Erdős–Rado bound (statement only) -/

/-- **Erdős–Rado Sunflower Lemma** (classical bound).

If a family `𝓢` of `w`‑element sets has more than `(p - 1)! * w^p`
members, then it contains a `p`‑sunflower.                                        -/
lemma sunflower_exists
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (all_w : ∀ A ∈ 𝓢, A.card = w)
    (bound : (p - 1).factorial * w ^ p < 𝓢.card) :
    HasSunflower 𝓢 w p := by
  classical
  -- Proof omitted
  sorry

/-- A tiny convenience corollary specialised to **Boolean cube** contexts
where we automatically know each set has fixed size `w`. -/
lemma sunflower_exists_of_fixedSize
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : (∀ A ∈ 𝓢, A.card = w))
    (h_big  : 𝓢.card > (p - 1).factorial * w ^ p) :
    HasSunflower 𝓢 w p :=
  sunflower_exists 𝓢 w p hw hp h_size (by
    -- Rearrange strict inequality direction to match bound in lemma
    have : (p - 1).factorial * w ^ p < 𝓢.card := by
      simpa [lt_iff_le_and_ne, h_big.ne] using h_big
    exact this)

end Sunflower


