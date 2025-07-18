/-
bool_func.lean
==============

Foundational definitions for working with Boolean functions on the `n`‑dimensional
Boolean cube `𝔹ⁿ ≃ Fin n → Bool`.

This file is completely *self‑contained* and makes **no assumptions** about later
lemmas (entropy, sunflowers, …).  It provides the basic objects and operations
that all subsequent modules (`entropy.lean`, `sunflower.lean`, `cover.lean`, …)
re‑use.

Main contents
-------------

* `Point  n`      – a vertex of the Boolean cube `𝔹ⁿ`.
* `BFunc  n`      – a Boolean function `𝔹ⁿ → Bool`.
* `Family n`      – a (finite) family of Boolean functions.
* `Subcube n`     – a (partial) assignment of coordinates, i.e. a rectangular
                    subcube of `𝔹ⁿ`.
* Basic operations:
  * `Point.update`        – replace the value of one coordinate.
  * `BFunc.restrictCoord` – fix one input bit of a Boolean function.
  * `Subcube.mem`         – membership of a point in a subcube.
  * `Subcube.dimension`   – dimension (= number of *free* coordinates).
  * `Subcube.monochromaticFor` / `…ForFamily` – (joint) monochromaticity
    predicates.

The code is *purely definitional* — no theorems are proved here except simple
helper facts that the later files rely on (all proofs are by `simp` /
`aesop`‑style automation).
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

noncomputable section

open Classical
open Finset

namespace BoolFunc

/-- **A point of the Boolean `n`‑cube**.  We represent it as a function
`Fin n → Bool`.  Using `Fin n` (rather than `Nat`) keeps all indices
in‑range by construction. -/
abbrev Point (n : ℕ) : Type := Fin n → Bool

/-- **A Boolean function** on `n` input bits. -/
abbrev BFunc (n : ℕ) : Type := Point n → Bool

/-- A *family* (finite set) of Boolean functions on `n` bits.  We use
`Finset` rather than `Set` so that cardinalities are definable.  Lean does
not have decidable equality for function types by default, so we work in
the classical (`noncomputable`) universe and add an explicit `DecidableEq`
instance via *choice*.  This is sufficient for all counting arguments in the
subsequent modules (no algorithmic use of equality is needed). -/
noncomputable
abbrev Family (n : ℕ) : Type := Finset (BFunc n)

instance {n : ℕ} : DecidableEq (BFunc n) := by
  classical
  exact fun f g =>
    if h : (∀ x, f x = g x) then isTrue (by
      have := funext (fun x => (h x))
      exact this)
    else isFalse (by
      intro hfg; apply h; intro x; rw [hfg])

/-! ### Subcubes (rectangles) -/

/-- A **subcube** (a.k.a. rectangle) of the Boolean cube `𝔹ⁿ`.
It is specified by

* `idx` – a finite set `I ⊆ {0, …, n−1}` of fixed coordinates;
* `val` – for each `i ∈ I`, the Boolean value to which that
          coordinate is frozen.

All other coordinates are *free*. -/
structure Subcube (n : ℕ) where
  idx : Finset (Fin n)
  val : (i : Fin n) → (h : i ∈ idx) → Bool
  deriving DecidableEq

namespace Subcube

variable {n : ℕ}

/-- **Membership** of a point in a subcube. -/
def mem (R : Subcube n) (x : Point n) : Prop :=
  ∀ (i : Fin n) (h : i ∈ R.idx), x i = R.val i h

-- local notation for subcube membership
notation x " ∈ₛ " R => Subcube.mem R x

/-- The *dimension* of a subcube = number of *free* coordinates. -/
def dimension (R : Subcube n) : ℕ :=
  n - R.idx.card

@[simp] lemma mem_of_not_fixed {R : Subcube n} {x : Point n} {i : Fin n}
    (_ : i ∉ R.idx) : R.mem x → True := by
  intro _; trivial

/-- **Monochromaticity for a single function**:
`R` is monochromatic for `f` if `f` is constant on `R`. -/
def monochromaticFor (R : Subcube n) (f : BFunc n) : Prop :=
  ∃ b : Bool, ∀ {x : Point n}, R.mem x → f x = b

/-- **Monochromaticity for a family**: `R` has one fixed colour
shared by *all* functions in `F`. -/
def monochromaticForFamily (R : Subcube n) (F : Family n) : Prop :=
  ∃ b : Bool, ∀ f, f ∈ F → ∀ {x : Point n}, R.mem x → f x = b

end Subcube

/-! ### Basic point and function operations -/

section PointOps

variable {n : ℕ}

/-- **Update** a single coordinate of a point. -/
def Point.update (x : Point n) (i : Fin n) (b : Bool) : Point n :=
  fun j => if j = i then b else x j

@[simp] lemma Point.update_eq (x : Point n) (i : Fin n) (b : Bool) :
    (Point.update x i b) i = b := by
  simp [Point.update]

@[simp] lemma Point.update_neq (x : Point n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    (Point.update x i b) j = x j := by
  simp [Point.update, h]

@[simp] lemma Point.update_idem (x : Point n) (i : Fin n) (b : Bool) :
    Point.update (Point.update x i b) i b = Point.update x i b := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Point.update]
  · simp [Point.update, hk]

@[simp] lemma Point.update_update (x : Point n) (i : Fin n) (b₁ b₂ : Bool) :
    Point.update (Point.update x i b₁) i b₂ = Point.update x i b₂ := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Point.update]
  · simp [Point.update, hk]

/-! ### Additional point update lemmas -/

@[simp] lemma Point.update_swap (x : Point n) {i j : Fin n} (h : i ≠ j)
    (b1 b2 : Bool) :
    Point.update (Point.update x i b1) j b2 =
      Point.update (Point.update x j b2) i b1 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Point.update, h]
  · by_cases hjk : k = j
    · subst hjk; simp [Point.update, hk, h]
    · simp [Point.update, hk, hjk]

/-- **A constant point** with the same Boolean value in every coordinate. -/
def Point.const (n : ℕ) (b : Bool) : Point n := fun _ => b

@[simp] lemma Point.const_apply (n : ℕ) (b : Bool) (i : Fin n) :
    (Point.const n b) i = b := rfl

end PointOps

section Restrict

variable {n : ℕ}

/-- **Restriction of a Boolean function** by *fixing one input bit*.
The resulting function still has arity `n`; it ignores its `j`‑th
argument and uses the constant value `b` instead.  This choice avoids
dimension bookkeeping burden elsewhere. -/
def BFunc.restrictCoord (f : BFunc n) (j : Fin n) (b : Bool) : BFunc n :=
  fun x => f (Point.update x j b)

/-! A few helper lemmas used later. -/

@[simp] lemma restrictCoord_fixed {f : BFunc n} {j : Fin n} {b : Bool}
    {x : Point n} :
    (BFunc.restrictCoord f j b) (Point.update x j b) = f (Point.update x j b) := by
  simp [BFunc.restrictCoord]

@[simp] lemma restrictCoord_agrees
    {f : BFunc n} {j : Fin n} {b : Bool} {x : Point n}
    (h : x j = b) :
    (BFunc.restrictCoord f j b) x = f x := by
  have : Point.update x j b = x := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [Point.update, h]
    · simp [Point.update, hk]
  simp [BFunc.restrictCoord, this]

end Restrict

/-- The set of inputs on which a Boolean function outputs `true`. -/
noncomputable
def ones {n : ℕ} [Fintype (Point n)] (f : BFunc n) : Finset (Point n) :=
  Finset.univ.filter fun x => f x = true

@[simp] lemma mem_ones {n : ℕ} [Fintype (Point n)] {f : BFunc n} {x : Point n} :
    x ∈ ones f ↔ f x = true := by
  classical
  simp [ones]

/-! ### Basic probability on the Boolean cube -/

/-- Probability that a Boolean function outputs `true` under the uniform
distribution. -/
noncomputable def prob {n : ℕ} [Fintype (Point n)] (f : BFunc n) : ℝ :=
  ((ones f).card : ℝ) / (Fintype.card (Point n))

lemma prob_nonneg {n : ℕ} [Fintype (Point n)] (f : BFunc n) :
    0 ≤ prob f := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card (Point n)) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hnum : 0 ≤ ((ones f).card : ℝ) := by exact_mod_cast Nat.zero_le _
  have hden : 0 ≤ (Fintype.card (Point n) : ℝ) := le_of_lt hpos
  simpa [prob] using div_nonneg hnum hden

lemma prob_le_one {n : ℕ} [Fintype (Point n)] (f : BFunc n) :
    prob f ≤ 1 := by
  classical
  have hsubset : (ones f).card ≤ Fintype.card (Point n) := by
    simpa using (Finset.card_le_univ (s := ones f))
  have hnum : ((ones f).card : ℝ) ≤ (Fintype.card (Point n) : ℝ) := by
    exact_mod_cast hsubset
  have hden : 0 ≤ (Fintype.card (Point n) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Point n))
  have h := div_le_one_of_le₀ hnum hden
  simpa [prob] using h

/-- Probability that `f` evaluates to `true` when the `i`-th input bit is fixed
to `false`. -/
noncomputable def prob_restrict_false {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) : ℝ :=
  prob (BFunc.restrictCoord f i false)

/-- Probability that `f` evaluates to `true` when the `i`-th input bit is fixed
to `true`. -/
noncomputable def prob_restrict_true {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) : ℝ :=
  prob (BFunc.restrictCoord f i true)

@[simp] lemma prob_restrict_false_eq_discrete {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) :
    prob_restrict_false f i =
      ((ones (BFunc.restrictCoord f i false)).card : ℝ) /
        (Fintype.card (Point n)) := rfl

@[simp] lemma prob_restrict_true_eq_discrete {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) :
    prob_restrict_true f i =
      ((ones (BFunc.restrictCoord f i true)).card : ℝ) /
        (Fintype.card (Point n)) := rfl

/-- Restrict every function in a family by fixing the `i`‑th input bit to `b`. -/
noncomputable
def Family.restrict {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) : Family n :=
  F.image fun f x => f (Point.update x i b)

/-! ### Essential coordinate support -/

/-- Set of coordinates on which `f` depends essentially.  A coordinate `i`
belongs to `support f` if flipping the `i`‑th bit of some input changes the
output. -/
noncomputable
def support {n : ℕ} (f : BFunc n) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x : Point n, f x ≠ f (Point.update x i (!x i))

@[simp] lemma mem_support_iff {n : ℕ} {f : BFunc n} {i : Fin n} :
    i ∈ support f ↔ ∃ x : Point n, f x ≠ f (Point.update x i (!x i)) := by
  classical
  simp [support]

/-! ### Families of supports -/

namespace Family

variable {n : ℕ}

/-/ The collection of essential supports of all functions in the family. -/
noncomputable
def supports (F : Family n) : Finset (Finset (Fin n)) :=
  F.image support

@[simp] lemma mem_supports {F : Family n} {s : Finset (Fin n)} :
    s ∈ supports F ↔ ∃ f ∈ F, support f = s := by
  classical
  unfold supports
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨f, hf, hfs⟩
    exact ⟨f, hf, hfs⟩
  · rintro ⟨f, hf, rfl⟩
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩

@[simp] lemma supports_card_le (F : Family n) :
    (supports F).card ≤ F.card := by
  classical
  simpa [supports] using
    (Finset.card_image_le (s := F) (f := support))

end Family

/-! ## Re‑exports to avoid long qualified names downstream -/
export Subcube (mem dimension monochromaticFor monochromaticForFamily)
export Point (update)

end BoolFunc

end
