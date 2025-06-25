/-
cover.lean
===========

Top-level **cover construction** for the Family Collision-Entropy Lemma.

Interface
---------

* `mBound n h`         — the *numeric* bound
      `n·(h+2)·2^(10 h)` appearing in the spec;
* `cover_exists F h hH` — existential statement:
      a finite set `𝓡` of subcubes satisfying

  1.  every `R ∈ 𝓡` is **jointly monochromatic** for the whole family `F`;
  2.  for every function `f ∈ F`, every `1`-input of `f`
      lies in (at least) one rectangle of `𝓡`;
  3.  `|𝓡| ≤ mBound n h`.

* `coverFamily F h hH` — a *choice* of such a cover (`noncomputable`).

The proof of `cover_exists` follows the plan: alternate sunflower extraction
and entropy-drop steps until all 1-inputs covered, tracking rectangle count.
-/

import BoolFunc
import Entropy
import Sunflower
import Agreement
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic

open Classical
open BoolFunc
open Finset

namespace Cover

/-! ## Numeric bound taken from the specification -/

/-- `mBound n h = n·(h+2)·2^(10 h)` — the explicit rectangle bound. -/
def mBound (n h : ℕ) : ℕ :=
  n * (h + 2) * Nat.pow 2 (10 * h)

/-- Numeric bound: `2*h + n ≤ mBound n h`. -/
lemma numeric_bound (n h : ℕ) : 2 * h + n ≤ mBound n h := by
  -- since `2^(10*h) ≥ 1`, multiplying by it only increases the value
  have h1 : n * (h + 2) ≤ n * (h + 2) * 2 ^ (10 * h) := by
    have : 1 ≤ (2 : ℕ) ^ (10 * h) := by
      have := Nat.pow_pos (by decide : 0 < (2 : ℕ)) (10 * h)
      exact Nat.succ_le_of_lt this
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_left (n * (h + 2)) this
  -- and trivially `2*h + n ≤ n*(h+2)`
  have h2 : 2 * h + n ≤ n * (h + 2) := by linarith
  -- combine the inequalities
  have := le_trans h2 h1
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-! ## Existence of a good cover (statement and expanded proof skeleton) -/

variable {n h : ℕ} (F : Family n)

/--
**Existence lemma** — constructive core of the FCE-lemma.
Assume `H₂(F) ≤ h`. Then there exists a finite set `𝓡` of subcubes satisfying:

* **mono**: each `R ∈ 𝓡` is monochromatic for the entire family `F`;
* **cover**: any `1`-input of any `f ∈ F` lies in some `R ∈ 𝓡`;
* **bound**: `|𝓡| ≤ mBound n h`.
-/
lemma cover_exists
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ (𝓡 : Finset (Subcube n)),
      (∀ R, R ∈ 𝓡 → Subcube.monochromaticForFamily R F) ∧
      (∀ f, f ∈ F → ∀ x, f x = true → ∃ R, R ∈ 𝓡 ∧ x ∈ₛ R) ∧
      𝓡.card ≤ mBound n h := by
  -- We will construct `Rset` and prove properties by well-founded recursion
  have h_real : BoolFunc.H₂ F ≤ h := by simpa using hH
  /- Step 1: initialization -/
  let Rset_init : Finset (Subcube n) := ∅
  -- Auxiliary function: process uncovered points
  let rec buildCover (F_curr : Family n) (Rset : Finset (Subcube n)) : Finset (Subcube n) :=
    if ∃ f ∈ F_curr, ∃ x, f x = true ∧ ¬∃ R ∈ Rset, x ∈ₛ R then
      -- collect supports of uncovered inputs
      let S := (F_curr.bind fun f => { x.support | x ∈ BoolFunc.ones f ∧ ¬∃ R ∈ Rset, x ∈ₛ R })
      if S.card ≥ sunflower_bound n h then
        -- sunflower case: extract a core and build rectangle
        let I := (sunflower_exists S).some_core
        let R := (coreAgreement (F := F_curr) I).some_subcube
        buildCover F_curr (Rset.insert R)
      else
        -- entropy-drop case: restrict on some coordinate
        let (i, b) := EntropyDrop F_curr h_real
        let F_restr := F_curr.restrict i b
        let R_zero := Rset
        let R_one := Rset
        -- recursively cover restricted families
        let C0 := buildCover (F := F_restr) F_restr R_zero
        let C1 := buildCover (F := F_restr) F_restr R_one
        C0 ∪ C1
    else
      Rset
  -- Build final cover
  let R_final := buildCover F Rset_init
  use R_final
  split
  · -- mono: each rectangle added is monochromatic by construction
    intro R hR
    -- proof by cases on insertion origin
    sorry
  · split
    · -- cover: any 1-input will be handled by one of the cases
      intros f hf x hx
      sorry
    · -- bound: count insertions from two cases and sum
      have : R_final.card ≤ 2 * h + n := by
        -- at most 2h from entropy drops, at most n from sunflower steps
        sorry
      -- show final bound fits mBound
      calc R_final.card ≤ 2 * h + n := this
        _ ≤ mBound n h := by
          simpa [mBound] using numeric_bound n h

/-! ## Choice function returning a specific cover -/

/-- A concrete (noncomputable) cover obtained via `classical.choice`. -/
noncomputable
def coverFamily
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    Finset (Subcube n) :=
  Classical.choice (cover_exists (F := F) (h := h) hH)

@[simp] lemma coverFamily_spec_mono
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R, R ∈ coverFamily (n := _) (h := h) F hH →
      Subcube.monochromaticForFamily R F := by
  rcases Classical.choose_spec (cover_exists (F := F) (h := h) hH)
    with ⟨hmono, _, _⟩
  exact fun R => hmono R

@[simp] lemma coverFamily_spec_cover
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ f, f ∈ F → ∀ x, f x = true →
      ∃ R, R ∈ coverFamily (n := _) (h := h) F hH ∧ x ∈ₛ R := by
  rcases Classical.choose_spec (cover_exists (F := F) (h := h) hH)
    with ⟨_, hcover, _⟩
  exact hcover

@[simp] lemma coverFamily_card_bound
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := _) (h := h) F hH).card ≤ mBound n h := by
  rcases Classical.choose_spec (cover_exists (F := F) (h := h) hH)
    with ⟨_, _, hbound⟩
  exact hbound

end Cover
