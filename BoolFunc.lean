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

import Std.Data.Fin.Basic
import Std.Data.Finset
import Std.Logic

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

namespace Subcube

variable {n : ℕ}

/-- **Membership** of a point in a subcube. -/
def mem (R : Subcube n) (x : Point n) : Prop :=
  ∀ (i : Fin n) (h : i ∈ R.idx), x i = R.val i h

notation x " ∈ₛ " R => R.mem x

/-- The *dimension* of a subcube = number of *free* coordinates. -/
def dimension (R : Subcube n) : ℕ :=
  n - R.idx.card

@[simp] lemma mem_of_not_fixed {R : Subcube n} {x : Point n} {i : Fin n}
    (h : i ∉ R.idx) : (x ∈ₛ R) → True := by
  intro _; trivial

/-- **Monochromaticity for a single function**:
`R` is monochromatic for `f` if `f` is constant on `R`. -/
def monochromaticFor (R : Subcube n) (f : BFunc n) : Prop :=
  ∃ b : Bool, ∀ {x : Point n}, x ∈ₛ R → f x = b

/-- **Monochromaticity for a family**: `R` has one fixed colour
shared by *all* functions in `F`. -/
def monochromaticForFamily (R : Subcube n) (F : Family n) : Prop :=
  ∃ b : Bool, ∀ f, f ∈ F → ∀ {x : Point n}, x ∈ₛ R → f x = b

end Subcube

/-! ### Basic point and function operations -/

section PointOps

variable {n : ℕ}

/-- **Update** a single coordinate of a point. -/
def Point.update (x : Point n) (i : Fin n) (b : Bool) : Point n :=
  fun j => if h : j = i then b else x j

@[simp] lemma Point.update_eq (x : Point n) (i : Fin n) (b : Bool) :
    (Point.update x i b) i = b := by
  simp [Point.update]

@[simp] lemma Point.update_neq (x : Point n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    (Point.update x i b) j = x j := by
  simp [Point.update, h, decide]

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
  rfl

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

/-! ## Re‑exports to avoid long qualified names downstream -/
export Subcube (mem dimension monochromaticFor monochromaticForFamily)
export Point (update)

end BoolFunc
