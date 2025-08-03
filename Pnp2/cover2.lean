import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support
import Pnp2.Sunflower.RSpread
import Pnp2.low_sensitivity_cover
import Pnp2.Boolcube
import Pnp2.Cover.SubcubeAdapters -- subcube conversion utilities
import Pnp2.Cover.Bounds -- numeric bounds for the cover construction
import Pnp2.Cover.Uncovered -- predicates about uncovered points
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Classical
open Finset
open Agreement
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)
open Sunflower

namespace Cover2

/-!  This module gradually reimplements the original `cover.lean` file.
Most numeric and combinatorial lemmas have already been ported, while the
recursive cover construction is currently represented by a lightweight stub.
Remaining gaps are tracked in `docs/cover_migration_plan.md`.

The heavy arithmetic lemmas surrounding the auxiliary function `mBound`
now live in `Pnp2.Cover.Bounds` to keep this file focused on the cover
construction itself.
-/

@[simp] def size {n : ℕ} (Rset : Finset (Subcube n)) : ℕ := Rset.card

lemma cover_size_bound {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ Fintype.card (Subcube n) := by
  classical
  simpa [size] using (Finset.card_le_univ (s := Rset))

@[simp] def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

lemma size_bounds {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ bound_function n := by
  classical
  simpa [bound_function] using cover_size_bound (Rset := Rset)

variable {n h : ℕ} (F : Family n)

/-! ### Simple termination measure

`mu` tracks the remaining entropy budget together with the number of
currently uncovered pairs.  The measure is used in the original
construction to show that each recursive step makes progress.  We only
record a minimal API for now. -/

noncomputable def mu (F : Family n) (h : ℕ) (Rset : Finset (Subcube n)) : ℕ :=
  2 * h + (uncovered (n := n) F Rset).toFinset.card

/-!
If all `1`‑inputs of `F` already lie inside some rectangle of `Rset`,
then the uncovered set is empty and the measure `μ` collapses to `2 * h`.
-/
  lemma mu_of_allCovered {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ}
      (hcov : AllOnesCovered (n := n) F Rset) :
      mu (n := n) F h Rset = 2 * h := by
    classical
    -- Replace the uncovered set by `∅` using the coverage assumption.
    have hzero :
        uncovered (n := n) F Rset =
          (∅ : Set (Σ _ : BFunc n, Point n)) :=
      uncovered_eq_empty_of_allCovered
        (n := n) (F := F) (Rset := Rset) hcov
    -- Unfold `μ` and simplify using the empty uncovered set.
    calc
      mu (n := n) F h Rset
          = 2 * h + (uncovered (n := n) F Rset).toFinset.card := rfl
      _ = 2 * h + (∅ : Set (Σ _ : BFunc n, Point n)).toFinset.card := by
          -- Apply `congrArg` to rewrite the uncovered set using `hzero`.
          have := congrArg
            (fun s : Set (Σ _ : BFunc n, Point n) => 2 * h + s.toFinset.card)
            hzero
          simpa using this
      _ = 2 * h + 0 := by simp
      _ = 2 * h := by simp


lemma mu_of_firstUncovered_none {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hfu : firstUncovered (n := n) F Rset = none) :
    mu (n := n) F h Rset = 2 * h := by
  have hcov : AllOnesCovered (n := n) F Rset :=
    allOnesCovered_of_firstUncovered_none (n := n) (F := F)
      (Rset := Rset) hfu
  simpa using
    (mu_of_allCovered (n := n) (F := F) (Rset := Rset) (h := h) hcov)


/-!
Conversely, if the measure `μ` equals `2 * h`, then no uncovered pairs remain.
Consequently all `1`‑inputs of `F` must already be covered by `Rset`.
-/
lemma allOnesCovered_of_mu_eq {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hμ : mu (n := n) F h Rset = 2 * h) :
    AllOnesCovered (n := n) F Rset := by
  classical
  -- From the equality on `μ` we deduce that the uncovered set has
  -- cardinality `0`.
  have hμ' : 2 * h + (uncovered (n := n) F Rset).toFinset.card =
      2 * h + 0 := by
    simpa [mu] using hμ
  have hcard0 : (uncovered (n := n) F Rset).toFinset.card = 0 :=
    Nat.add_left_cancel hμ'
  -- Hence the uncovered set itself is empty.
  have hset : uncovered (n := n) F Rset =
      (∅ : Set (Σ _ : BFunc n, Point n)) := by
    classical
    -- Convert cardinality information into emptiness of the uncovered set.
    have hfin :
        (uncovered (n := n) F Rset).toFinset =
          (∅ : Finset (Σ _ : BFunc n, Point n)) :=
      Finset.card_eq_zero.mp hcard0
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    -- Membership in the set contradicts the finset being empty.
    have hpFin : p ∈ (uncovered (n := n) F Rset).toFinset :=
      Set.mem_toFinset.mpr hp
    -- Rewrite using `hfin` and derive a contradiction.
    rw [hfin] at hpFin
    cases hpFin
  -- Conclude by converting the empty uncovered set into coverage.
  have hfu : firstUncovered (n := n) F Rset = none :=
    (firstUncovered_none_iff (n := n) (F := F) (R := Rset)).2
      (by simpa using hset)
  exact allOnesCovered_of_firstUncovered_none
      (F := F) (Rset := Rset) hfu

/-!  Basic properties of the measure `μ`. -/

lemma mu_nonneg {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    0 ≤ mu (n := n) F h Rset := by
  -- Since `μ` is a natural number, nonnegativity is immediate.
  exact Nat.zero_le _

lemma mu_lower_bound {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    2 * h ≤ mu (n := n) F h Rset := by
  -- The uncovered cardinality is nonnegative, so `μ` is at least `2 * h`.
    -- `simp` proves the inequality after unfolding `μ`.
    simp [mu]

lemma mu_mono_h {F : Family n} {Rset : Finset (Subcube n)}
    {h₁ h₂ : ℕ} (hh : h₁ ≤ h₂) :
    mu (n := n) F h₁ Rset ≤ mu (n := n) F h₂ Rset := by
  -- Increasing the entropy budget can only increase the measure.
  dsimp [mu]
  exact add_le_add (Nat.mul_le_mul_left _ hh) le_rfl

lemma mu_union_singleton_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ} :
    mu (n := n) F h (Rset ∪ {R}) ≤ mu (n := n) F h Rset := by
  classical
  -- Adding a rectangle can only reduce the uncovered set.
  have hsub : uncovered (n := n) F (Rset ∪ {R}) ⊆
      uncovered (n := n) F Rset :=
    uncovered_subset_of_union_singleton
      (F := F) (Rset := Rset) (R := R)
  -- Convert the set inclusion into a finset inclusion on cardinals.
  have hsubF : (uncovered (n := n) F (Rset ∪ {R})).toFinset ⊆
        (uncovered (n := n) F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered (n := n) F Rset := hsub hx'
    simpa using hx''
  -- Cardinalities respect inclusion.
  have hcard := Finset.card_le_card hsubF
  -- Add the entropy contribution to both sides.
  have := add_le_add_left hcard (2 * h)
  simpa [mu] using this

/-!
Adding a rectangle that covers at least one previously uncovered pair strictly
decreases the measure `μ`.  This lemma will be useful when reasoning about
progress of the cover construction.
-/
lemma mu_union_singleton_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R) :
    mu (n := n) F h (Rset ∪ {R}) < mu (n := n) F h Rset := by
  classical
  rcases hx with ⟨p, hpU, hpR⟩
  have hp_not : p ∉ uncovered (n := n) F (Rset ∪ {R}) := by
    rcases hpU with ⟨hf, hx, hnc⟩
    intro hp'
    rcases hp' with ⟨hf', hx', hnc'⟩
    have := hnc' R (by simp) hpR
    exact this
  have hsub : (uncovered (n := n) F (Rset ∪ {R})).toFinset ⊆
      (uncovered (n := n) F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton
        (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  have hproper : ¬((uncovered (n := n) F Rset).toFinset ⊆
        (uncovered (n := n) F (Rset ∪ {R})).toFinset) := by
    intro hsubset
    have hpFin : p ∈ (uncovered (n := n) F Rset).toFinset := by simpa using hpU
    have := hsubset hpFin
    exact hp_not (by simpa using this)
  have hcard := Finset.card_lt_card ⟨hsub, hproper⟩
  have := Nat.add_lt_add_left hcard (2 * h)
  simpa [mu] using this

/-!  A convenient corollary of `mu_union_singleton_lt`: if at least one new
pair becomes covered, the measure decreases by one.  This quantified version is
occasionally handy for numeric estimates. -/
lemma mu_union_singleton_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R) :
    mu (n := n) F h (Rset ∪ {R}) + 1 ≤ mu (n := n) F h Rset := by
  classical
  have hlt :=
    mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx
  exact Nat.succ_le_of_lt hlt

/--
If a rectangle covers two distinct uncovered pairs, the measure drops strictly
after inserting this rectangle.  The proof reuses the single-pair inequality on
one witness.
-/
lemma mu_union_singleton_double_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
      {p₁ p₂ : Σ _ : BFunc n, Point n}
      (hp₁ : p₁ ∈ uncovered (n := n) F Rset)
      (_hp₂ : p₂ ∈ uncovered (n := n) F Rset)
      (hp₁R : p₁.2 ∈ₛ R) (_hp₂R : p₂.2 ∈ₛ R)
      (_hne : p₁ ≠ p₂) :
    mu (n := n) F h (Rset ∪ {R}) < mu (n := n) F h Rset := by
  classical
  -- It suffices to cover one of the two pairs.
  have hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R := ⟨p₁, hp₁, hp₁R⟩
  -- Apply the basic inequality for a newly covered pair.
  exact mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx

/--
If a rectangle covers two distinct uncovered pairs, the measure drops by at
least two after inserting this rectangle.  This strengthening of
`mu_union_singleton_succ_le` mirrors the bookkeeping argument from the original
`cover` module.
-/
lemma mu_union_singleton_double_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F Rset) (hp₂ : p₂ ∈ uncovered (n := n) F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂) :
    mu (n := n) F h (Rset ∪ {R}) + 2 ≤ mu (n := n) F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F Rset).toFinset
  let T : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hxT
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton
        (F := F) (Rset := Rset) (R := R) hx'
    simpa [S] using hx''
  -- Membership facts for the two pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  -- After adding `R`, the pairs `p₁` and `p₂` are no longer uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂`.
  have hsub2 : T ⊆ (S.erase p₁).erase p₂ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq
      have : p₁ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq
      have : p₂ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₂T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    exact Finset.mem_erase.mpr ⟨hxne2, hx1⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne.symm, hp₂S⟩
  have hcard_le : T.card ≤ ((S.erase p₁).erase p₂).card :=
    Finset.card_le_card hsub2
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 : ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard_final : T.card ≤ S.card - 2 := by
    have := hcard_le
    simpa [hcard1, hcard2] using this
  -- `S` contains both `p₁` and `p₂`, so its cardinality is at least two.
  have htwo : 2 ≤ S.card := by
    classical
    have hsub_pair : ({p₁, p₂} : Finset _) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hp₁S
      · have hx' := Finset.mem_singleton.mp hx; simpa [hx'] using hp₂S
    have hcard_pair : ({p₁, p₂} : Finset _).card = 2 := by
      classical
      -- Use the dedicated lemma for the cardinality of a pair.
      exact Finset.card_pair (a := p₁) (b := p₂) hne
    have htwo_aux : 2 ≤ ({p₁, p₂} : Finset _).card := by
      -- Rewrite using the computed cardinality.
      simp [hcard_pair]
    exact le_trans htwo_aux (Finset.card_le_card hsub_pair)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le htwo).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

/-!
If a rectangle covers three distinct uncovered pairs, the measure drops
strictly after inserting this rectangle.  The proof reuses the basic
single-pair inequality on one witness.-/
lemma mu_union_singleton_triple_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
      {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
      (hp₁ : p₁ ∈ uncovered (n := n) F Rset)
      (_hp₂ : p₂ ∈ uncovered (n := n) F Rset)
      (_hp₃ : p₃ ∈ uncovered (n := n) F Rset)
      (hp₁R : p₁.2 ∈ₛ R)
      (_hp₂R : p₂.2 ∈ₛ R) (_hp₃R : p₃.2 ∈ₛ R)
      (_hne₁₂ : p₁ ≠ p₂) (_hne₁₃ : p₁ ≠ p₃) (_hne₂₃ : p₂ ≠ p₃) :
    mu (n := n) F h (Rset ∪ {R}) < mu (n := n) F h Rset := by
  classical
  -- It suffices to cover one of the three pairs.
  have hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R := ⟨p₁, hp₁, hp₁R⟩
  exact mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx

/--
Adding a rectangle that covers *three distinct* uncovered pairs decreases the
measure `μ` by at least three.  This strengthening of
`mu_union_singleton_double_succ_le` mirrors the bookkeeping argument from the
original `cover` module.-/
lemma mu_union_singleton_triple_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F Rset) (hp₂ : p₂ ∈ uncovered (n := n) F Rset)
    (hp₃ : p₃ ∈ uncovered (n := n) F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃) :
    mu (n := n) F h (Rset ∪ {R}) + 3 ≤ mu (n := n) F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F Rset).toFinset
  let T : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hxT
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa [S] using hx''
  -- Membership facts for the three pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  have hp₃S : p₃ ∈ S := by simpa [S] using hp₃
  -- After adding `R`, none of the pairs remain uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  have hp₃T : p₃ ∉ T := by
    intro hx
    have hx' : p₃ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₃R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂.erase p₃`.
  have hsub3 : T ⊆ ((S.erase p₁).erase p₂).erase p₃ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq
      have : p₁ ∈ T := by
        simpa [T, hxEq] using hxT
      exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq
      have : p₂ ∈ T := by
        simpa [T, hxEq] using hxT
      exact hp₂T this
    have hxne3 : x ≠ p₃ := by
      intro hxEq
      have : p₃ ∈ T := by
        simpa [T, hxEq] using hxT
      exact hp₃T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    have hx2 : x ∈ (S.erase p₁).erase p₂ := Finset.mem_erase.mpr ⟨hxne2, hx1⟩
    exact Finset.mem_erase.mpr ⟨hxne3, hx2⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne₁₂.symm, hp₂S⟩
  have hp₃_in_erase2 : p₃ ∈ (S.erase p₁).erase p₂ := by
    have hp₃_in_erase1 : p₃ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₃.symm, hp₃S⟩
    exact Finset.mem_erase.mpr ⟨hne₂₃.symm, hp₃_in_erase1⟩
  have hcard_le : T.card ≤ (((S.erase p₁).erase p₂).erase p₃).card :=
    Finset.card_le_card hsub3
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 : ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard3 : (((S.erase p₁).erase p₂).erase p₃).card =
      ((S.erase p₁).erase p₂).card - 1 :=
    Finset.card_erase_of_mem hp₃_in_erase2
  have hcard_final : T.card ≤ S.card - 3 := by
    have := hcard_le
    simpa [hcard1, hcard2, hcard3] using this
  -- `S` contains the three distinct pairs, so its cardinality is at least three.
  have hthree : 3 ≤ S.card := by
    classical
      have hsub_trip : ({p₁, p₂, p₃} : Finset _) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with hx₁ | hxrest
        · simpa [hx₁] using hp₁S
        rcases Finset.mem_insert.mp hxrest with hx₂ | hx₃
        · subst hx₂
          simpa using hp₂S
        · have hx' := Finset.mem_singleton.mp hx₃
          simpa [hx'] using hp₃S
    have hcard_trip : ({p₁, p₂, p₃} : Finset _).card = 3 := by
      classical
      have hnot12 : p₁ ≠ p₂ := hne₁₂
      have hnot13 : p₁ ≠ p₃ := hne₁₃
      have hnot23 : p₂ ≠ p₃ := hne₂₃
      -- Remove the unused lemma and simplify.
      simp [Finset.card_insert_of_notMem, hnot12, hnot13, hnot23]
    have hthree_aux : 3 ≤ ({p₁, p₂, p₃} : Finset _).card := by
      -- Simplify using the computed cardinality.
      simp [hcard_trip]
    exact hthree_aux.trans (Finset.card_le_card hsub_trip)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le hthree).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

lemma mu_union_singleton_quad_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ p₄ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F Rset)
    (hp₂ : p₂ ∈ uncovered (n := n) F Rset)
    (hp₃ : p₃ ∈ uncovered (n := n) F Rset)
    (hp₄ : p₄ ∈ uncovered (n := n) F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R)
    (hp₃R : p₃.2 ∈ₛ R) (hp₄R : p₄.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₁₄ : p₁ ≠ p₄)
    (hne₂₃ : p₂ ≠ p₃) (hne₂₄ : p₂ ≠ p₄) (hne₃₄ : p₃ ≠ p₄) :
    mu (n := n) F h (Rset ∪ {R}) + 4 ≤ mu (n := n) F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F Rset).toFinset
  let T : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hxT
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa [S] using hx''
  -- Membership facts for the four pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  have hp₃S : p₃ ∈ S := by simpa [S] using hp₃
  have hp₄S : p₄ ∈ S := by simpa [S] using hp₄
  -- After inserting `R`, none of the pairs remain uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  have hp₃T : p₃ ∉ T := by
    intro hx
    have hx' : p₃ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₃R
  have hp₄T : p₄ ∉ T := by
    intro hx
    have hx' : p₄ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₄R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂.erase p₃.erase p₄`.
  have hsub4 :
      T ⊆ (((S.erase p₁).erase p₂).erase p₃).erase p₄ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq
      have : p₁ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq
      have : p₂ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₂T this
    have hxne3 : x ≠ p₃ := by
      intro hxEq
      have : p₃ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₃T this
    have hxne4 : x ≠ p₄ := by
      intro hxEq
      have : p₄ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₄T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    have hx2 : x ∈ (S.erase p₁).erase p₂ :=
      Finset.mem_erase.mpr ⟨hxne2, hx1⟩
    have hx3 : x ∈ ((S.erase p₁).erase p₂).erase p₃ :=
      Finset.mem_erase.mpr ⟨hxne3, hx2⟩
    exact Finset.mem_erase.mpr ⟨hxne4, hx3⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne₁₂.symm, hp₂S⟩
  have hp₃_in_erase2 : p₃ ∈ (S.erase p₁).erase p₂ := by
    have hp₃_in_erase1 : p₃ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₃.symm, hp₃S⟩
    exact Finset.mem_erase.mpr ⟨hne₂₃.symm, hp₃_in_erase1⟩
  have hp₄_in_erase3 : p₄ ∈ ((S.erase p₁).erase p₂).erase p₃ := by
    have hp₄_in_erase1 : p₄ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₄.symm, hp₄S⟩
    have hp₄_in_erase2 : p₄ ∈ (S.erase p₁).erase p₂ :=
      Finset.mem_erase.mpr ⟨hne₂₄.symm, hp₄_in_erase1⟩
    exact Finset.mem_erase.mpr ⟨hne₃₄.symm, hp₄_in_erase2⟩
  have hcard_le :
      T.card ≤ ((((S.erase p₁).erase p₂).erase p₃).erase p₄).card :=
    Finset.card_le_card hsub4
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 :
      ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard3 :
      (((S.erase p₁).erase p₂).erase p₃).card =
        ((S.erase p₁).erase p₂).card - 1 :=
    Finset.card_erase_of_mem hp₃_in_erase2
  have hcard4 :
      ((((S.erase p₁).erase p₂).erase p₃).erase p₄).card =
        (((S.erase p₁).erase p₂).erase p₃).card - 1 :=
    Finset.card_erase_of_mem hp₄_in_erase3
  have hcard_final : T.card ≤ S.card - 4 := by
    have := hcard_le
    simpa [hcard1, hcard2, hcard3, hcard4] using this
  -- `S` contains the four distinct pairs, so its cardinality is at least four.
  have hfour : 4 ≤ S.card := by
    classical
    have hsub_quad : ({p₁, p₂, p₃, p₄} : Finset _) ⊆ S := by
      intro x hx
      have hx' : x = p₁ ∨ x = p₂ ∨ x = p₃ ∨ x = p₄ := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_assoc, or_left_comm,
              or_comm] using hx
      rcases hx' with h₁ | hx'
      · subst h₁; simpa using hp₁S
      rcases hx' with h₂ | hx'
      · subst h₂; simpa using hp₂S
      rcases hx' with h₃ | h₄
      · subst h₃; simpa using hp₃S
      · subst h₄; simpa using hp₄S
    have hcard_quad : ({p₁, p₂, p₃, p₄} : Finset _).card = 4 := by
      classical
      have hnot12 : p₁ ≠ p₂ := hne₁₂
      have hnot13 : p₁ ≠ p₃ := hne₁₃
      have hnot14 : p₁ ≠ p₄ := hne₁₄
      have hnot23 : p₂ ≠ p₃ := hne₂₃
      have hnot24 : p₂ ≠ p₄ := hne₂₄
      have hnot34 : p₃ ≠ p₄ := hne₃₄
      -- Omit the unused lemma and simplify.
      simp [Finset.card_insert_of_notMem,
            hnot12, hnot13, hnot14, hnot23, hnot24, hnot34]
    have hfour_aux : 4 ≤ ({p₁, p₂, p₃, p₄} : Finset _).card := by
      -- Simplify using the established cardinality.
      simp [hcard_quad]
    exact hfour_aux.trans (Finset.card_le_card hsub_quad)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le hfour).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this


/-!
Taking the union of two rectangle sets cannot increase the measure `μ`.  This
simple monotonicity fact follows by induction on the second set using the
single--rectangle lemma `mu_union_singleton_le`.
-/
lemma mu_union_le {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ} :
    mu (n := n) F h (R₁ ∪ R₂) ≤ mu (n := n) F h R₁ := by
  classical
  -- We induct over `R₂`, inserting one rectangle at a time.
  refine Finset.induction_on R₂ ?base ?step
  · -- Base case: union with the empty set has no effect.
    simp [mu]
  · -- Induction step: insert a rectangle `R` into the growing set `S`.
    intro R S hR hIH
    -- First bound the union with `R` using the single-rectangle lemma.
    have hstep :=
      mu_union_singleton_le (F := F) (Rset := R₁ ∪ S) (R := R) (h := h)
    -- Combine with the induction hypothesis.
    have hcomb := le_trans hstep hIH
    -- Reassociate unions to match the induction hypothesis.
    have : R₁ ∪ insert R S = (R₁ ∪ S) ∪ {R} := by
      ext x; by_cases hx : x = R
      · subst hx; simp [hR]
      · simp [Finset.mem_insert, hx]
    simpa [this, Finset.union_assoc] using hcomb

/-!  A convenient corollary of `mu_union_le`: if `R₁ ⊆ R₂`, then `μ` for the
smaller set dominates the measure for the larger one.  In other words,
adding rectangles can only decrease the measure. -/
lemma mu_mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ}
    (hsub : R₁ ⊆ R₂) :
    mu (n := n) F h R₂ ≤ mu (n := n) F h R₁ := by
  classical
  -- Express `R₂` as `R₁ ∪ (R₂ \ R₁)` and apply `mu_union_le`.
  have hunion : R₂ = R₁ ∪ (R₂ \ R₁) := by
    ext x; by_cases hx : x ∈ R₁
    · constructor
      · intro _; exact Finset.mem_union.mpr <| Or.inl hx
      · intro _; exact hsub hx
    · constructor
      · intro hxR2
        have hxRdiff : x ∈ R₂ \ R₁ :=
          -- Rewrite membership in the difference using `simp`.
          Finset.mem_sdiff.mpr ⟨hxR2, by simp [hx]⟩
        exact Finset.mem_union.mpr <| Or.inr hxRdiff
      · intro hxUnion
        rcases Finset.mem_union.mp hxUnion with hx₁ | hx₂
        · exact hsub hx₁
        · exact (Finset.mem_sdiff.mp hx₂).1
  have hmain := mu_union_le (n := n) (F := F) (h := h)
      (R₁ := R₁) (R₂ := R₂ \ R₁)
  have hrewrite :
      mu (n := n) F h R₂ = mu (n := n) F h (R₁ ∪ (R₂ \ R₁)) :=
    congrArg (fun S => mu (n := n) F h S) hunion
  have := hrewrite ▸ hmain
  simpa using this

/-- `mu_union_lt` generalises `mu_union_singleton_lt` to an arbitrary set of
rectangles.  If some uncovered pair of `R₁` is covered by a rectangle from
`R₂`, then the measure strictly decreases after taking the union. -/
lemma mu_union_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F R₁, ∃ R ∈ R₂, p.2 ∈ₛ R) :
    mu (n := n) F h (R₁ ∪ R₂) < mu (n := n) F h R₁ := by
  classical
  rcases hx with ⟨p, hpU, R, hR, hpR⟩
  -- First insert the specific rectangle that covers `p`.
  have hx_singleton : ∃ q ∈ uncovered (n := n) F R₁, q.2 ∈ₛ R :=
    ⟨p, hpU, hpR⟩
  have hstep :=
    mu_union_singleton_lt (F := F) (Rset := R₁) (R := R)
      (h := h) hx_singleton
  -- Adding more rectangles cannot increase the measure.
  have hsubset : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx'
    rcases Finset.mem_union.mp hx' with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hR
  have hmono :=
    mu_mono_subset (F := F) (h := h)
      (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsubset
  exact lt_of_le_of_lt hmono hstep

/-- `mu_union_double_succ_le` combines the single-rectangle estimate with
monotonicity.  If some rectangle in `R₂` covers two distinct uncovered pairs of
`R₁`, then the measure drops by at least two after taking the union. -/
lemma mu_union_double_succ_le {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁) (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) + 2 ≤ mu (n := n) F h R₁ := by
  classical
  -- Adding additional rectangles can only decrease the measure.
  have hsub : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hmem
  have hmono := mu_mono_subset (F := F) (h := h)
      (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsub
  have hdouble := mu_union_singleton_double_succ_le
      (F := F) (Rset := R₁) (R := R) (h := h)
      hp₁ hp₂ hp₁R hp₂R hne
  have := add_le_add_right hmono 2
  exact le_trans this hdouble

/-- `mu_union_double_lt` is the strict version of `mu_union_double_succ_le`. -/
lemma mu_union_double_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁) (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) < mu (n := n) F h R₁ := by
  classical
  have hdrop :=
    mu_union_double_succ_le (F := F) (R₁ := R₁) (R₂ := R₂)
      (R := R) (h := h) hp₁ hp₂ hp₁R hp₂R hne hmem
  have hsucc : mu (n := n) F h (R₁ ∪ R₂) + 1 ≤ mu (n := n) F h R₁ := by
    have hstep : (1 : ℕ) ≤ 2 := by decide
    have := Nat.add_le_add_left hstep (mu (n := n) F h (R₁ ∪ R₂))
    exact this.trans hdrop
  exact Nat.lt_of_succ_le hsucc

/-!
`mu_union_triple_succ_le` extends `mu_union_double_succ_le` to the case of
three distinct uncovered pairs.  If some rectangle in `R₂` covers all three,
then taking the union with `R₂` decreases the measure by at least three.
-/
lemma mu_union_triple_succ_le {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁)
    (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₃ : p₃ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) + 3 ≤ mu (n := n) F h R₁ := by
  classical
  -- Taking the union with a larger set can only reduce the measure.
  have hsub : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hmem
  have hmono :=
    mu_mono_subset (F := F) (h := h) (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsub
  -- Covering the three pairs with `R` yields a drop of at least three.
  have htriple :=
    mu_union_singleton_triple_succ_le (F := F) (Rset := R₁) (R := R) (h := h)
      hp₁ hp₂ hp₃ hp₁R hp₂R hp₃R hne₁₂ hne₁₃ hne₂₃
  have := add_le_add_right hmono 3
  exact le_trans this htriple

/-- `mu_union_triple_lt` is the strict version of `mu_union_triple_succ_le`. -/
lemma mu_union_triple_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁)
    (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₃ : p₃ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) < mu (n := n) F h R₁ := by
  classical
  -- First obtain the additive inequality dropping by three.
  have hdrop :=
    mu_union_triple_succ_le (F := F) (R₁ := R₁) (R₂ := R₂)
      (R := R) (h := h) hp₁ hp₂ hp₃ hp₁R hp₂R hp₃R
      hne₁₂ hne₁₃ hne₂₃ hmem
  -- Convert it into a strict inequality.
  have hsucc : mu (n := n) F h (R₁ ∪ R₂) + 1 ≤ mu (n := n) F h R₁ := by
    have hstep : (1 : ℕ) ≤ 3 := by decide
    have := Nat.add_le_add_left hstep (mu (n := n) F h (R₁ ∪ R₂))
    exact this.trans hdrop
  exact Nat.lt_of_succ_le hsucc

/-!  If `firstUncovered` returns some pair, then the measure exceeds `2 * h`.
This witness guarantees that the uncovered set has positive cardinality. -/
lemma mu_gt_of_firstUncovered_some {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hfu : firstUncovered (n := n) F Rset ≠ none) :
    2 * h < mu (n := n) F h Rset := by
  classical
  -- If `firstUncovered` is nonempty, the uncovered set cannot be empty.
  have hne : uncovered (n := n) F Rset ≠
      (∅ : Set (Σ _ : BFunc n, Point n)) := by
    intro hempty
    have := (firstUncovered_none_iff (n := n) (F := F) (R := Rset)).2 hempty
    exact hfu this
  -- Obtain an explicit witness from the nonempty uncovered set.
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  -- This ensures the cardinality of the finset is positive.
  have hpos : 0 < (uncovered (n := n) F Rset).toFinset.card :=
    Finset.card_pos.mpr ⟨p, by simpa using hp⟩
  -- Conclude that `μ` exceeds `2 * h` by at least one.
  have := Nat.lt_add_of_pos_right (n := 2 * h) hpos
  simpa [mu] using this

/-! ### Coarse bound on the number of uncovered pairs -/

lemma uncovered_card_bound (F : Family n) (Rset : Finset (Subcube n)) :
    (uncovered (n := n) F Rset).toFinset.card ≤ F.card * 2 ^ n := by
  classical
  -- Each uncovered pair corresponds to a function from `F` and a cube point.
  have hsubset : (uncovered (n := n) F Rset).toFinset ⊆
      F.sigma (fun _ => (Finset.univ : Finset (Point n))) := by
    intro p hp
    have hp' : p ∈ uncovered (n := n) F Rset := by simpa using hp
    rcases hp' with ⟨hf, hx, _⟩
    have hx' : p.2 ∈ (Finset.univ : Finset (Point n)) := by simp
    exact Finset.mem_sigma.mpr ⟨hf, hx'⟩
  have hcard := Finset.card_le_card hsubset
  -- Cardinality of a sigma-type splits multiplicatively for a constant fiber.
  have hprod : (F.sigma fun _ => (Finset.univ : Finset (Point n))).card =
      F.card * (Finset.univ : Finset (Point n)).card := by
    classical
    simpa [Finset.card_sigma, Finset.sum_const, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc]
  -- The Boolean cube has size `2 ^ n`.
  have hcube : (Finset.univ : Finset (Point n)).card = 2 ^ n := by
    simpa using (Fintype.card_vector (α := Bool) (n := n))
  simpa [hprod, hcube] using hcard

/--
`uncovered_init_coarse_bound` specialises the coarse cardinality estimate
to the initial call of the cover construction where no rectangles are
present yet.  Even this simple bound is occasionally useful for quick
sanity checks.
-/
lemma uncovered_init_coarse_bound (F : Family n) :
    (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤
      F.card * 2 ^ n := by
  simpa using
    (uncovered_card_bound (n := n) (F := F)
      (Rset := (∅ : Finset (Subcube n))))

/--
If the family itself is empty, the set of initially uncovered pairs is
trivially empty.  In this case any numeric bound holds; we record a
simple instance with the dimension `n` for convenience.
-/
lemma uncovered_init_bound_empty (F : Family n) (hF : F = (∅ : Family n)) :
    (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤ n := by
  classical
  -- With an empty family no pairs are uncovered, so the cardinality is zero.
  have hcard :
      (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card = 0 := by
    simpa [uncovered, hF]
  -- Rewrite the goal using `hcard` and conclude with `Nat.zero_le`.
  have hgoal :
      (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤ n := by
    rw [hcard]
    exact Nat.zero_le n
  exact hgoal

/--
**Sunflower extraction.**  At the current stage of the migration this lemma is
still posed as an axiom.  It is a direct analogue of the classical
`sunflower_step` used in the original `cover` module: if all functions in `F`
share the same non‑zero support size `p` and the family of supports is large
enough, one can find a subcube `R` of positive dimension on which at least
`t` functions from the family are identically `true`.

The formal proof has not yet been ported to the simplified `Boolcube.Subcube`
structure.  The next lemma develops most of the combinatorial argument,
obtaining a sunflower of supports and turning its core into a candidate subcube.
The final step – establishing that every selected function evaluates to `true`
on that subcube – remains a `sorry`, but the surrounding reasoning mirrors the
original proof closely.
-/
lemma sunflower_step {n : ℕ} (F : Family n) (p t : ℕ)
    (hp : 0 < p) (ht : 2 ≤ t)
    (h_big : (t - 1).factorial * p ^ t < (Family.supports F).card)
    (h_support : ∀ f ∈ F, (BoolFunc.support f).card = p) :
    ∃ (R : Boolcube.Subcube n),
      ((F.filter fun f => ∀ x : Boolcube.Point n,
          Boolcube.Subcube.Mem R x → f x = true).card ≥ t) ∧
      1 ≤ Boolcube.Subcube.dim R := by
  classical
  -- Assemble the family of supports.
  let 𝓢 : Finset (Finset (Fin n)) := Family.supports F
  have h_sizes : ∀ s ∈ 𝓢, s.card = p := by
    intro s hs
    rcases Family.mem_supports.mp hs with ⟨f, hf, rfl⟩
    exact h_support f hf
  -- Extract a sunflower family from `𝓢`.
  obtain ⟨S, hSsub⟩ : ∃ S : SunflowerFam n t, S.petals ⊆ 𝓢 := by
    have hbig' : 𝓢.card > Nat.factorial (t - 1) * p ^ t := by
      simpa using h_big
    exact SunflowerFam.exists_of_large_family
      (F := 𝓢) (w := p) (t := t) hp ht h_sizes hbig'
  -- Select, for each petal, a function with exactly that support.
  have exists_f : ∀ A ∈ S.petals, ∃ f ∈ F, BoolFunc.support f = A := by
    intro A hA
    have hA' : A ∈ 𝓢 := hSsub hA
    rcases Family.mem_supports.mp hA' with ⟨f, hfF, hsup⟩
    exact ⟨f, hfF, hsup⟩
  classical
  choose f hfF hfSupp using exists_f
  -- Freeze the sunflower core to obtain a covering subcube.
  let x₀ : Boolcube.Point n := fun _ => false
  let R : Boolcube.Subcube n := Boolcube.Subcube.fromPoint x₀ S.core
  -- Bounding the cardinality and dimension is the intricate part of the argument.
  -- We leave the two key properties as placeholders for future work.
  have h_filter_ge :
      (F.filter fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true).card ≥ t := by
    -- We embed the `t` selected functions into the filtered family and count them.
    -- First build the image of the mapping from petals to their chosen functions.
    let im :=
      S.petals.attach.image (fun a : {A // A ∈ S.petals} => f a.1 a.2)
    -- This mapping is injective because different petals have different supports
    -- and each chosen function has support exactly its petal.
    have h_inj_aux :
        Function.Injective (fun a : {A // A ∈ S.petals} => f a.1 a.2) := by
      intro a₁ a₂ h_eq
      -- Equality of functions forces equality of their supports.
      have hsup := congrArg BoolFunc.support h_eq
      have hA : a₁.1 = a₂.1 := by
        simpa [hfSupp _ a₁.2, hfSupp _ a₂.2] using hsup
      -- Subtype equality follows from equality of the underlying sets.
      exact Subtype.ext hA
    -- Hence the image has cardinality `t`.
    have h_im_card : im.card = t := by
      have hcard :=
        Finset.card_image_of_injective
          (s := S.petals.attach)
          (f := fun a : {A // A ∈ S.petals} => f a.1 a.2)
          h_inj_aux
      -- Translate the cardinality of `attach` using `S.tsize`.
      simpa [im, Finset.card_attach, S.tsize] using hcard
    -- Show that every chosen function indeed belongs to the filter set.
    have h_sub :
        im ⊆ F.filter (fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true) := by
      intro g hg
      rcases Finset.mem_image.1 hg with ⟨a, ha, rfl⟩
      have hgF : f a.1 a.2 ∈ F := hfF _ a.2
      have htrue : ∀ x : Boolcube.Point n, R.Mem x → (f a.1 a.2) x = true := by
        -- Points of `R` agree with `x₀` on the sunflower core.  If the support of
        -- `f a.1 a.2` is contained in that core, then the evaluation on any `x ∈ R`
        -- coincides with the evaluation at `x₀`, which we will eventually show is
        -- `true` for these selected functions.
        intro x hx
        -- Agreement on the core coordinates provided by `hx`.
        have h_agree_core : ∀ i ∈ S.core, x i = x₀ i := by
          intro i hi
          -- Membership in `R` fixes the value on the sunflower core.
          have hx' := hx i
          simpa [R, Boolcube.Subcube.fromPoint, hi] using hx'
        -- Assume for now that the support of the chosen function lies inside
        -- the sunflower core.
        have h_support_core :
            BoolFunc.support (f a.1 a.2) ⊆ S.core := by
          -- TODO: deduce from the sunflower structure that the chosen function
          -- depends only on coordinates from the core.
          sorry
        -- Extend the agreement on the core to the full support of `f`.
        have h_agree : ∀ i ∈ BoolFunc.support (f a.1 a.2), x i = x₀ i := by
          intro i hi
          have hi_core : i ∈ S.core := h_support_core hi
          exact h_agree_core i hi_core
        -- With the agreement in hand, evaluations at `x` and `x₀` are equal.
        have hx_eq :=
          BoolFunc.eval_eq_of_agree_on_support
            (f := f a.1 a.2) (x := x) (y := x₀) h_agree
        -- The witness returned by `exists_true_on_support` will eventually
        -- establish the value at `x₀`.
        have hx0_true : (f a.1 a.2) x₀ = true := by
          -- TODO: prove that each chosen function evaluates to `true` on the
          -- base point `x₀` constructed above.
          sorry
        -- Combining the two facts yields the desired result.
        simpa [hx_eq] using hx0_true
      -- Package the membership proof for the filter.
      have : f a.1 a.2 ∈ F.filter
          (fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true) := by
        -- Membership in a filtered set amounts to membership in `F` and the property.
        have : f a.1 a.2 ∈ F ∧
            (∀ x : Boolcube.Point n, R.Mem x → (f a.1 a.2) x = true) :=
          ⟨hgF, htrue⟩
        simpa using this
      simpa using this
    -- The image has cardinality `t` and sits inside the filtered family.
    have h_le := Finset.card_le_card h_sub
    have :
        t ≤ (F.filter fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true).card := by
      simpa [im, h_im_card] using h_le
    -- Interpreting `≥` as `≤` yields the desired inequality.
    exact this
  have h_dim : 1 ≤ Boolcube.Subcube.dim R := by
    -- The sunflower guarantees at least two distinct petals of size `p`.
    -- This forces the common core to be strictly smaller than `p`.
    have hpet_card : ∀ P ∈ S.petals, P.card = p := by
      intro P hP; exact h_sizes P (hSsub hP)
    -- Choose two distinct petals to witness strict containment of the core.
    have h_one_lt : 1 < S.petals.card :=
      let htwo : 2 ≤ S.petals.card := by simpa [S.tsize] using ht
      lt_of_lt_of_le (by decide : 1 < 2) htwo
    obtain ⟨P₁, hP₁, P₂, hP₂, hP₁P₂⟩ := Finset.one_lt_card.mp h_one_lt
    -- The core is contained in each petal, so its size is at most `p`.
    have h_core_le_p : S.core.card ≤ p := by
      have := card_le_card (S.sub_core P₁ hP₁)
      simpa [hpet_card P₁ hP₁] using this
    -- Show the core cannot itself have size `p`; otherwise two petals coincide.
    have h_core_ne_p : S.core.card ≠ p := by
      intro h_eq
      have h1 : S.core = P₁ := by
        apply Finset.eq_of_subset_of_card_le (S.sub_core P₁ hP₁)
        have : P₁.card = S.core.card := by simpa [hpet_card P₁ hP₁, h_eq]
        exact le_of_eq this
      have h2 : S.core = P₂ := by
        apply Finset.eq_of_subset_of_card_le (S.sub_core P₂ hP₂)
        have : P₂.card = S.core.card := by simpa [hpet_card P₂ hP₂, h_eq]
        exact le_of_eq this
      have hcontr : P₁ = P₂ := h1.symm.trans h2
      exact hP₁P₂ hcontr
    have h_core_lt_p : S.core.card < p :=
      lt_of_le_of_ne' h_core_le_p (by simpa [eq_comm] using h_core_ne_p)
    -- Any petal lives inside the `n` coordinates, hence `p ≤ n`.
    have hp_le_n : p ≤ n := by
      have : P₁.card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_univ _
      simpa [hpet_card P₁ hP₁] using this
    -- Combine the two inequalities to deduce that the core leaves at least one free coordinate.
    have h_core_lt_n : S.core.card < n := lt_of_lt_of_le h_core_lt_p hp_le_n
    have hpos : 0 < n - S.core.card := Nat.sub_pos_of_lt h_core_lt_n
    -- Finally rewrite the dimension of `R` in terms of the core cardinality.
    have hdim' : 1 ≤ n - S.core.card := Nat.succ_le_of_lt hpos
    have hdim_eq : Boolcube.Subcube.dim R = n - S.core.card := by
      simpa [R] using (Boolcube.Subcube.dim_fromPoint (x := x₀) (K := S.core))
    exact hdim_eq.symm ▸ hdim'
  exact ⟨R, h_filter_ge, h_dim⟩

/-! ### Lifting monochromaticity from restricted families

If a subcube `R` fixes the `i`-th coordinate to `b`, then a family that is
monochromatic on the restricted version of `F` is also monochromatic on `F`
itself.  These helper lemmas mirror their counterparts in `cover.lean` and
will support the recursion once `buildCover` is fully ported. -/

lemma lift_mono_of_restrict
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily R F := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f hf x hx
  have hf0 : f.restrictCoord i b ∈ F.restrict i b :=
    (BoolFunc.Family.mem_restrict).2 ⟨f, hf, rfl⟩
  have hxib : x i = b := hfix x hx
  have hxupdate : BoolFunc.update x i b = x := by
    funext j; by_cases hji : j = i
    · subst hji; simp [BoolFunc.update, hxib]
    · simp [BoolFunc.update, hji]
  have htmp := hc (f.restrictCoord i b) hf0 x hx
  have : f x = c := by
    simpa [BFunc.restrictCoord, hxupdate] using htmp
  exact this

/--
When a subcube `R` already forces the `i`-th coordinate to be `b`,
monochromaticity for the restricted family lifts directly to the original
family.  This variant mirrors `lift_mono_of_restrict` but packages the
common situation where the fixed-coordinate condition is immediate. -/
lemma lift_mono_of_restrict_fixOne
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily R F :=
  lift_mono_of_restrict (F := F) (i := i) (b := b) (R := R) hfix hmono

/--
Monochromaticity is preserved when restricting to a subset of rectangles.
If every rectangle in `R₁` is monochromatic for `F` and `R₂ ⊆ R₁`, then every
rectangle in `R₂` remains monochromatic. -/
lemma mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (hsub : R₂ ⊆ R₁) :
    ∀ R ∈ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  exact h₁ R (hsub hR)

/--
The union of two collections of monochromatic rectangles is again a collection
of monochromatic rectangles. -/
lemma mono_union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (h₂ : ∀ R ∈ R₂, Subcube.monochromaticForFamily R F) :
    ∀ R ∈ R₁ ∪ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  rcases Finset.mem_union.mp hR with h | h
  · exact h₁ R h
  · exact h₂ R h

/--
A preliminary stub for the cover construction.  For now `buildCover` simply
returns the accumulated set of rectangles without performing any recursive
steps.  This suffices for basic cardinality lemmas while the full algorithm is
being ported from `cover.lean`.
-/
noncomputable def buildCover (F : Family n) (h : ℕ)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n) := ∅) : Finset (Subcube n) :=
  Rset

/--
If the search for an uncovered pair already fails (`firstUncovered = none`),
`buildCover` immediately returns the existing set of rectangles, whose size is
assumed to be bounded by `mBound`.
-/
lemma buildCover_card_bound_of_none {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {Rset : Finset (Subcube n)}
    (_hfu : firstUncovered (n := n) F Rset = none)
    (hcard : Rset.card ≤ mBound n h) :
    (buildCover (n := n) F h _hH Rset).card ≤ mBound n h := by
  simpa [buildCover] using hcard

/--
Base case of the size bound: if no uncovered pair exists initially, the
constructed cover is empty and trivially bounded by `mBound`.
-/
lemma buildCover_card_bound_base {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) = none) :
    (buildCover (n := n) F h _hH).card ≤ mBound n h := by
  have : (0 : ℕ) ≤ mBound n h := mBound_nonneg (n := n) (h := h)
  simpa [buildCover] using this

/--
A coarse numeric estimate that bounds the size of the cover directly by
`2 * h + n`.  With the current stub `buildCover`, the constructed set of
rectangles is empty, so the claim follows immediately.
-/
lemma buildCover_card_linear_bound_base {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) = none) :
    (buildCover (n := n) F h _hH).card ≤ 2 * h + n := by
  have hres : buildCover (n := n) F h _hH = (∅ : Finset (Subcube n)) := by
    simpa [buildCover, _hfu]
  have : (0 : ℕ) ≤ 2 * h + n := Nat.zero_le _
  simpa [hres] using this

/--
The linear bound holds without assuming that the search for uncovered pairs
fails initially.  Since the stub `buildCover` returns the empty set, the
result is immediate.
-/
lemma buildCover_card_linear_bound {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ 2 * h + n := by
  have : (0 : ℕ) ≤ 2 * h + n := Nat.zero_le _
  simpa [buildCover] using this

/--
Rewriting of `buildCover_card_linear_bound` emphasising the initial measure
`μ = 2 * h + n`.  This variant mirrors the legacy API.
-/
lemma buildCover_card_init_mu {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ 2 * h + n := by
  simpa using
    (buildCover_card_linear_bound (n := n) (F := F) (h := h) _hH)

/--
`buildCover` (with the current stub implementation) always returns the
empty set, so its cardinality trivially satisfies the `mBound` bound.
This lemma mirrors the API of the full development and allows downstream
files to rely on the bound even before the full recursion is ported. -/
lemma buildCover_card_bound {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ mBound n h := by
  have : (0 : ℕ) ≤ mBound n h := mBound_nonneg (n := n) (h := h)
  simpa [buildCover] using this

/--
`buildCover` always yields a set of rectangles whose cardinality is bounded by
the universal function `bound_function`.  This is a direct consequence of the
generic size bound for finite sets of subcubes and does not rely on the
internal construction of `buildCover`.
-/
lemma buildCover_card_univ_bound {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ bound_function n := by
  classical
  -- `size_bounds` provides the universal bound for any finite set of
  -- rectangles.  Instantiate it with the set produced by `buildCover`.
  have := size_bounds (n := n) (Rset := buildCover (n := n) F h _hH)
  simpa [size, bound_function] using this

/--
When all functions in the family have sensitivity below the logarithmic
threshold, the (stubbed) cover remains empty and hence satisfies the crude
exponential bound.  This lemma mirrors the statement from `cover.lean` while
the full algorithm is being ported. -/
lemma buildCover_card_lowSens {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n)) :
    (buildCover (n := n) F h _hH).card ≤
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) := by
  -- The stubbed `buildCover` returns the empty set, whose cardinality is `0`.
  have : (0 : ℕ) ≤
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    Nat.zero_le _
  simpa [buildCover] using this

/--
`buildCover_card_lowSens_with` extends `buildCover_card_lowSens` to the case
where an initial set of rectangles `Rset` is provided.  The stubbed
implementation of `buildCover` simply returns `Rset`, so the inequality reduces
to the trivial bound `Rset.card ≤ Rset.card + …`.
-/
lemma buildCover_card_lowSens_with {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n))
    (Rset : Finset (Subcube n)) :
    (buildCover (n := n) F h _hH Rset).card ≤
      Rset.card +
        Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) := by
  -- The right-hand side obviously dominates `Rset.card`.
  have : Rset.card ≤
      Rset.card +
        Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    Nat.le_add_right _ _
  simpa [buildCover] using this

/--
`buildCover_card_bound_lowSens` upgrades the crude exponential bound from
`buildCover_card_lowSens` to the standard `mBound` function whenever the
logarithmic threshold `Nat.log2 (n + 1)^2` is at most the entropy budget `h`.
This mirrors the corresponding lemma in `cover.lean` but is trivial for the
stubbed `buildCover`.
-/
lemma buildCover_card_bound_lowSens {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) :
    (buildCover (n := n) F h hH).card ≤ mBound n h := by
  classical
  -- Start with the exponential estimate from `buildCover_card_lowSens`.
  have hcard : (buildCover (n := n) F h hH).card ≤
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    buildCover_card_lowSens (n := n) (F := F) (h := h) hH hs
  -- Compare the exponents `10 * log₂(n+1)^2` and `10 * h`.
  have hexp_mul :
      10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ 10 * h := by
    have := Nat.mul_le_mul_left 10 hh
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) ≤
        Nat.pow 2 (10 * h) :=
    -- Use the modern lemma `pow_le_pow_right` for exponent monotonicity.
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp_mul
  -- Combine with the main bound `pow_le_mBound`.
  have hbig := hcard.trans hpow
  have hbound := hbig.trans (pow_le_mBound (n := n) (h := h) hn)
  simpa using hbound

/-!
`buildCover_card_bound_lowSens_with` upgrades the crude exponential bound from
`buildCover_card_lowSens_with` to the standard `mBound` function when an
initial set of rectangles `Rset` is provided.  Under the numeric hypothesis
`hh`, the additional rectangles introduced by the low-sensitivity cover already
fit inside `mBound n h`, allowing us to conclude that the final size stays below
`mBound n (h + 1)` using `two_mul_mBound_le_succ`.
-/
lemma buildCover_card_bound_lowSens_with {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) (Rset : Finset (Subcube n))
    (hcard : Rset.card ≤ mBound n h) :
    (buildCover (n := n) F h hH Rset).card ≤ mBound n (h + 1) := by
  classical
  -- Cardinality bound from the low-sensitivity cover.
  have hsize :
      (buildCover (n := n) F h hH Rset).card ≤
        Rset.card +
          Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    buildCover_card_lowSens_with (n := n) (F := F) (h := h) hH hs
      (Rset := Rset)
  -- Estimate the additional rectangles using `mBound`.
  have hexp_mul :
      10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ 10 * h := by
    have := Nat.mul_le_mul_left 10 hh
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) ≤
        mBound n h :=
    -- Apply monotonicity of exponentiation in a single step and then
    -- leverage the existing bound on `mBound`.
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp_mul).trans
      (pow_le_mBound (n := n) (h := h) hn)
  -- Combine with the existing rectangles.
  have hsum :
      (buildCover (n := n) F h hH Rset).card ≤ Rset.card + mBound n h :=
    hsize.trans <| Nat.add_le_add_left hpow _
  have hdouble : Rset.card + mBound n h ≤ 2 * mBound n h := by
    have := add_le_add hcard (le_rfl : mBound n h ≤ mBound n h)
    simpa [two_mul] using this
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hsum.trans (hdouble.trans hstep)

/--
`buildCover_card_bound_lowSens_or` partially bridges the gap towards the
full counting lemma `buildCover_card_bound`.  When the maximum sensitivity of
functions in the family falls below the logarithmic threshold we invoke the
low‑sensitivity bound.  Otherwise we fall back to the coarse measure argument
used in the general placeholder proof.  In the stubbed development the cover is
always empty, so the result reduces to the numeric inequality `0 ≤ mBound n h`.
-/
lemma buildCover_card_bound_lowSens_or {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (_hn : 0 < n) :
    (buildCover (n := n) F h hH).card ≤ mBound n h := by
  -- `buildCover` returns the empty set, so its cardinality is zero.
  have hzero : (buildCover (n := n) F h hH).card = 0 := by
    simp [buildCover]
  -- Numeric bound is immediate from `mBound_nonneg`.
  have hbound : 0 ≤ mBound n h := mBound_nonneg (n := n) (h := h)
  simpa [hzero] using hbound

/--
In the low-sensitivity regime, `buildCover` produces a collection of
monochromatic rectangles.  With the current stubbed implementation the
constructed cover is empty, so the claim holds vacuously.  This lemma mirrors
the statement from `cover.lean` and will gain substance once the recursive
construction is ported.
-/
lemma buildCover_mono_lowSens {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n)) :
    ∀ R ∈ buildCover (n := n) F h _hH,
      Subcube.monochromaticForFamily R F := by
  intro R hR
  -- No rectangles are produced by the stubbed `buildCover`.
  have : False := by simpa [buildCover] using hR
  exact this.elim

/--
Every rectangle produced by `buildCover` is monochromatic for the family `F`.
With the current stub implementation, the cover is empty and the claim holds
vacuously.  This lemma mirrors the API of the full development.
-/
lemma buildCover_mono {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover (n := n) F h _hH,
        Subcube.monochromaticForFamily R F := by
  intro R hR
  -- Membership in the empty cover yields a contradiction.
  have : False := by simpa [buildCover] using hR
  cases this

/--
If the starting set of rectangles already covers all `1`-inputs of the
family `F`, then adding the (currently empty) result of `buildCover`
preserves this property.  This weak variant mirrors the intended lemma
from `cover.lean` and will be strengthened once the full construction is
ported.
-/
lemma buildCover_covers_with {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) (Rset : Finset (Subcube n))
    (hcov : AllOnesCovered (n := n) F Rset) :
    AllOnesCovered (n := n) F
      (Rset ∪ buildCover (n := n) F h hH Rset) := by
  -- `buildCover` returns `Rset`, so the union does not change the set of
  -- rectangles.  The coverage hypothesis therefore transfers directly.
  simpa [buildCover] using hcov

/--
Special case of `buildCover_covers_with` starting from the empty set of
rectangles.
-/
lemma buildCover_covers {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by
  simpa [buildCover] using hcov

/--
`buildCover_mu` collapses the measure to `2 * h` when the empty set already
covers all `1`-inputs.  This mirrors the behaviour of the eventual cover
construction.
-/
lemma buildCover_mu {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    mu (n := n) F h (buildCover (n := n) F h hH) = 2 * h := by
  -- `buildCover` returns the empty set, so the coverage hypothesis transfers.
  have hcov' :
      AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by
    simpa [buildCover] using
      (buildCover_covers (n := n) (F := F) (h := h) hH hcov)
  -- Apply the general lemma characterising covers with measure `2 * h`.
  simpa [buildCover] using
    (mu_of_allCovered (n := n) (F := F)
      (Rset := buildCover (n := n) F h hH) (h := h) hcov')

/-!
`mu_union_buildCover_le` is a small helper lemma used in termination
arguments for `buildCover`.  Adding the rectangles produced by one
step of the construction can only decrease the measure `μ`, since the
set of uncovered pairs shrinks.  With the current stub implementation of
`buildCover` this is immediate.
-/
lemma mu_union_buildCover_le {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n)) :
    mu (n := n) F h (Rset ∪ buildCover F h hH Rset) ≤
      mu (n := n) F h Rset := by
  -- `buildCover` currently returns its input set of rectangles, so the union
  -- collapses to `Rset`.
  simp [buildCover, mu]

/--
`mu_buildCover_lt_start` is a weak variant of the legacy lemma with the same
name.  In the original development the cover construction strictly decreased
the measure whenever an uncovered pair existed.  The current stubbed
implementation leaves the rectangle set unchanged, so we can only conclude that
the measure does not increase.  The strict inequality will return once the full
algorithm is ported.
-/
lemma mu_buildCover_lt_start {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) ≠ none) :
    mu (n := n) F h (buildCover (n := n) F h hH) ≤
      mu (n := n) F h (∅ : Finset (Subcube n)) := by
  -- `buildCover` returns the empty set, so both measures coincide.
  simp [buildCover, mu]

/--
`mu_buildCover_le_start` is a convenient special case of
`mu_union_buildCover_le`: starting from the empty set of rectangles, running
`buildCover` cannot increase the measure `μ`.
-/
lemma mu_buildCover_le_start {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu (n := n) F h (buildCover (n := n) F h hH) ≤
      mu (n := n) F h (∅ : Finset (Subcube n)) := by
  -- Instantiate `mu_union_buildCover_le` with an empty starting set.
  have :=
    mu_union_buildCover_le (n := n) (F := F) (h := h) (hH := hH)
      (Rset := (∅ : Finset (Subcube n)))
  -- Simplify using the stub definition of `buildCover`.
  simpa [buildCover] using this

/--
`mu_union_buildCover_lt` mirrors the corresponding lemma from the
legacy `cover` module.  In the complete development the union with the
rectangles produced by `buildCover` would strictly decrease the measure
whenever `firstUncovered` returns a pair.  The current stubbed
implementation leaves the rectangle set unchanged, so we can only show
that the measure does not increase.  The strict version will return once
the full recursion is ported. -/
lemma mu_union_buildCover_lt {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {Rset : Finset (Subcube n)}
    (_hfu : firstUncovered (n := n) F Rset ≠ none) :
    mu (n := n) F h (Rset ∪ buildCover (n := n) F h hH Rset) ≤
      mu (n := n) F h Rset := by
  -- The stub `buildCover` leaves `Rset` unchanged, so the measures coincide.
  simpa using
    (mu_union_buildCover_le (n := n) (F := F) (h := h)
      (hH := hH) (Rset := Rset))

/--
`buildCover_measure_drop` bounds the initial measure by `2 * h`.  In the
current development `buildCover` does not alter the uncovered set, so the
general lower bound on `μ` suffices.  The statement matches the legacy API
for downstream compatibility.
-/
lemma buildCover_measure_drop {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    2 * h ≤ mu (n := n) F h (∅ : Finset (Subcube n)) := by
  -- The measure `μ` always dominates `2 * h`, even for the empty rectangle set.
  simpa using
    (mu_lower_bound (n := n) (F := F) (h := h)
      (Rset := (∅ : Finset (Subcube n))))

/--
`cover_exists` packages the properties of `buildCover` into an existence
statement.  When the starting family has no uncovered `1`‑inputs, the stub
implementation returns the empty cover, which trivially satisfies the required
bounds.  This lemma mirrors the API of the full development, making it easier
for downstream files to transition once the real construction is ported. -/
lemma cover_exists {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered (n := n) F Rset ∧
      Rset.card ≤ mBound n h := by
  classical
  refine ⟨buildCover (n := n) F h hH, ?_, ?_, ?_⟩
  · intro R hR
    exact buildCover_mono (n := n) (F := F) (h := h) hH R hR
  · exact buildCover_covers (n := n) (F := F) (h := h) hH hcov
  · exact buildCover_card_bound (n := n) (F := F) (h := h) hH

/-! ### Canonical cover family

`coverFamily` wraps the `buildCover` construction to provide a single
canonical set of rectangles.  With the current stubbed `buildCover` this
definition simply returns the same set, but the API mirrors the legacy
development to ease future porting. -/

noncomputable def coverFamily {n : ℕ} (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  buildCover (n := n) F h hH

@[simp] lemma coverFamily_eq_buildCover {n : ℕ} (F : Family n) {h : ℕ}
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    coverFamily (n := n) F h _hH = buildCover (n := n) F h _hH := rfl

lemma coverFamily_spec {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    (∀ R ∈ coverFamily (n := n) F h hH,
        Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) ∧
      (coverFamily (n := n) F h hH).card ≤ mBound n h := by
  classical
  refine ⟨?mono, ?cover, ?card⟩
  · -- Monochromaticity follows from the corresponding lemma for `buildCover`.
    simpa [coverFamily] using
      (buildCover_mono (n := n) (F := F) (h := h) hH)
  · -- Coverage relies on the hypothesis that the empty set already covers
    -- all `1`-inputs.  The stubbed `buildCover` returns this set unchanged.
    simpa [coverFamily] using
      (buildCover_covers (n := n) (F := F) (h := h) hH hcov)
  · -- Cardinality bound obtained from the corresponding `buildCover` lemma.
    simpa [coverFamily] using
      (buildCover_card_bound (n := n) (F := F) (h := h) hH)

lemma coverFamily_spec_cover {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) :=
  (coverFamily_spec (n := n) (F := F) (h := h) hH hcov).2.1

/-!  Every rectangle in the canonical cover is monochromatic for the family.
With the current stub `buildCover` the cover is empty, so the statement holds
vacuously.  This lemma mirrors the eventual behaviour of the full
construction. -/
lemma coverFamily_mono {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ coverFamily (n := n) F h hH,
      Subcube.monochromaticForFamily R F := by
  -- Unfold `coverFamily` and reuse the corresponding lemma for `buildCover`.
  simpa [coverFamily] using
    (buildCover_mono (n := n) (F := F) (h := h) hH)

lemma coverFamily_card_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) F h hH).card ≤ mBound n h := by
  simpa [coverFamily] using
    (buildCover_card_bound (n := n) (F := F) (h := h) hH)

lemma coverFamily_card_linear_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) F h hH).card ≤ 2 * h + n := by
  simpa [coverFamily] using
    (buildCover_card_linear_bound (n := n) (F := F) (h := h) hH)

lemma coverFamily_card_univ_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) F h hH).card ≤ bound_function n := by
  simpa [coverFamily] using
    (buildCover_card_univ_bound (n := n) (F := F) (h := h) hH)

end Cover2

