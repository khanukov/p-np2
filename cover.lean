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
  n * (h + 2) * 2 ^ (10 * h)

/-- Numeric bound: `2*h + n ≤ mBound n h`. -/
lemma numeric_bound (n h : ℕ) : 2 * h + n ≤ mBound n h := by
  have pow_ge_one : 1 ≤ 2 ^ (10 * h) :=
    Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ))
  calc
    2 * h + n ≤ n * (h + 2) := by linarith
    _ = n * (h + 2) * 1 := by simp
    _ ≤ n * (h + 2) * 2 ^ (10 * h) := by
      exact Nat.mul_le_mul_left _ pow_ge_one

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
    ∃ (Rset : Finset (Subcube n)),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ mBound n h := by
  -- We will construct `Rset` and prove properties by well-founded recursion
  have h_real : BoolFunc.H₂ F ≤ h := by simpa using hH
  -- initialization
  let Rset_init : Finset (Subcube n) := ∅
  -- recursive construction
  let rec buildCover : Family n → Finset (Subcube n) → Finset (Subcube n)
  | F_curr, Rset :=
    if h_uncovered : ∃ f ∈ F_curr, ∃ x, f x = true ∧ ¬ ∃ R ∈ Rset, x ∈ₛ R then
      let S := F_curr.bind fun f =>
        { x.support |
          x ∈ BoolFunc.ones f ∧ ¬ ∃ R ∈ Rset, x ∈ₛ R }
      if S.card ≥ sunflower_bound n h then
        -- sunflower extraction
        let core := (sunflower_exists S).some_core
        let R := (coreAgreement (F := F_curr) core).some_subcube
        buildCover F_curr (Rset.insert R)
      else
        -- entropy-drop split
        let ⟨i, b, drop_prop⟩ := EntropyDrop F_curr h_real
        let F₀ := F_curr.restrict i b
        let F₁ := F_curr.restrict i b.not
        let C₀ := buildCover F₀ Rset
        let C₁ := buildCover F₁ Rset
        C₀ ∪ C₁
    else
      Rset
  -- Build final cover
  let R_final := buildCover F Rset_init
  use R_final
  split
  · -- mono: any R inserted is monochromatic
    intro R hR
    induction hR using Finset.induction_on with
    | empty =>
        contradiction
    | @insert R₀ S hS ih =>
        by_cases hmem : R = R₀
        · subst hmem
          exact (coreAgreement (F := F) _).some_spec.1
        · exact ih hmem
  · split
    · -- cover: every 1-input is eventually covered
      intros f hf x hx
      have : ∃ R ∈ R_final, x ∈ₛ R := by
        -- by induction on buildCover, each branch either inserts a rectangle covering x, or recurses
        admit
      exact this
    · -- bound: count inserts from both cases
      have count_le : R_final.card ≤ 2 * h + n := by
        -- Each entropy-drop reduces H₂ by ≥1, so ≤2*h drop steps;
        -- Each sunflower step inserts ≤1 subcube per coordinate, ≤n overall.
        admit
      calc
        R_final.card ≤ 2 * h + n := count_le
        _ ≤ mBound n h := by simpa using numeric_bound n h

/-! ## Choice function returning a specific cover -/

/-- A concrete (noncomputable) cover obtained via `classical.choice`. -/
noncomputable
def coverFamily
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    Finset (Subcube n) :=
  Classical.choice (cover_exists (F := F) (h := h) hH)

@[simp] lemma coverFamily_mono
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ coverFamily (n := _) (h := h) F hH,
      Subcube.monochromaticForFamily R F := by
  rcases Classical.choose_spec (cover_exists (F := F) (h := h) hH)
    with ⟨hmono, _, _⟩
  exact fun R => hmono R

@[simp] lemma coverFamily_cover
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ f ∈ F → ∀ x, f x = true →
      ∃ R ∈ coverFamily (n := _) (h := h) F hH, x ∈ₛ R := by
  rcases Classical.choose_spec (cover_exists (F := F) (h := h) hH)
    with ⟨_, hcover, _⟩
  exact hcover

@[simp] lemma coverFamily_card
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := _) (h := h) F hH).card ≤ mBound n h := by
  rcases Classical.choose_spec (cover_exists (F := F) (h := h) hH)
    with ⟨_, _, hbound⟩
  exact hbound

lemma coverFamily_card_bound
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) (h := h) F hH).card ≤ mBound n h :=
  coverFamily_card (F := F) (h := h) hH

end Cover
