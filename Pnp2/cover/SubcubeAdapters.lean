--! This module provides lightweight adapter utilities for working with subcubes.
--!
--! The project currently uses two different representations for subcubes of the
--! Boolean cube:
--! * `Boolcube.Subcube` --- a minimal structure that indexes each coordinate by
--!   either `some b` (the coordinate is fixed to the Boolean value `b`) or
--!   `none` (the coordinate is free).
--! * `BoolFunc.Subcube` --- an older representation used in the original cover
--!   implementation where a cube is specified by a set of fixed coordinates and
--!   a function returning the value at those coordinates.
--!
--! The definitions in this file bridge these two views.  They are used by
--! `Pnp2.cover2` to port lemmas and constructions from the legacy development to
--! the simplified setting.  Placing them in their own module keeps `cover2`
--! focused on the covering argument itself and makes the adapter code reusable
--! in future files.

import Pnp2.BoolFunc
import Pnp2.Boolcube
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

-- Local notation for membership in a subcube of the Boolean cube.
notation x " ∈ₛ " R => Boolcube.Subcube.Mem R x

namespace Boolcube.Subcube

/-- `R` is jointly monochromatic for the family `F` if every function shares a
constant value on all points of `R`.  This lightweight wrapper mirrors the
original definition in `BoolFunc.lean` for the simplified subcube structure used
in `cover2`. -/
def monochromaticForFamily {n : ℕ} (R : Subcube n) (F : BoolFunc.Family n) : Prop :=
  ∃ b : Bool, ∀ f ∈ F, ∀ x, R.Mem x → f x = b

/-- Construct a subcube by freezing the coordinates in `K` to match the base
point `x`.

In the simplified `Boolcube.Subcube` representation a subcube is specified by
assigning to each coordinate either a Boolean value (the coordinate is fixed) or
`none` (the coordinate is left free).  The constructor below freezes exactly the
coordinates from the set `K` to match a given base point `x`. -/
def fromPoint {n : ℕ} (x : Point n) (K : Finset (Fin n)) : Subcube n :=
  ⟨fun i => if _ : i ∈ K then some (x i) else none⟩

@[simp] lemma mem_fromPoint {n : ℕ} {x : Point n} {K : Finset (Fin n)} {y : Point n} :
    Mem (fromPoint (n := n) x K) y ↔ ∀ i ∈ K, y i = x i := by
  classical
  unfold fromPoint Mem
  constructor
  · intro h i hi
    have := h i
    simpa [hi] using this
  · intro h i
    by_cases hiK : i ∈ K
    · have hx := h i hiK
      -- Expand the definition of the cube and reduce using the assumed equality.
      simpa [hiK] using hx
    · simp [hiK]

@[simp] lemma self_mem_fromPoint {n : ℕ} {x : Point n} {K : Finset (Fin n)} :
    x ∈ₛ fromPoint (n := n) x K := by
  classical
  -- Each coordinate in `K` obviously matches the corresponding bit of `x`.
  refine (mem_fromPoint (x := x) (K := K) (y := x)).2 ?_
  intro i hi; rfl

@[simp] lemma dim_fromPoint {n : ℕ} {x : Point n} {K : Finset (Fin n)} :
    (fromPoint (n := n) x K).dim = n - K.card := by
  classical
  unfold fromPoint dim support
  have hset :
      Finset.univ.filter (fun i : Fin n =>
        (if h : i ∈ K then some (x i) else none).isSome) = K := by
    -- Membership in the filtered set coincides with membership in `K`.
    ext i; by_cases hi : i ∈ K <;> simp [hi]
  -- The dimension is simply the number of unfixed coordinates.
  -- The filtered set is exactly `K`, so the dimension drops by `K.card`.
  simp [hset]

@[simp] lemma mem_fromPoint_subset {n : ℕ} {x : Point n}
    {K L : Finset (Fin n)} {y : Point n}
    (hKL : K ⊆ L)
    (hy : y ∈ₛ fromPoint (n := n) x L) :
    y ∈ₛ fromPoint (n := n) x K := by
  classical
  -- Expand membership of `hy` and restrict it along the subset relation.
  have hL : ∀ i ∈ L, y i = x i :=
    (mem_fromPoint (x := x) (K := L) (y := y)).1 hy
  -- Show membership in the smaller cube using the specialised equality.
  exact
    (mem_fromPoint (x := x) (K := K) (y := y)).2
      (by intro i hiK; exact hL i (hKL hiK))

end Boolcube.Subcube

/-! ### Bridging the legacy `BoolFunc.Subcube` with the simplified `Boolcube.Subcube` -/

namespace BoolFunc.Subcube

/-- Convert an old-style subcube (specified by a set of fixed coordinates and
their Boolean values) into the simplified `Boolcube.Subcube` representation used
in `cover2`.  Each coordinate in `idx` becomes a fixed bit in the resulting
cube, while all other coordinates remain free. -/
def toCube {n : ℕ} (R : Subcube n) : Boolcube.Subcube n :=
  ⟨fun i => if h : i ∈ R.idx then some (R.val i h) else none⟩

/-- Membership in the converted cube coincides with membership in the original
subcube. -/
lemma mem_toCube {n : ℕ} (R : Subcube n) (x : Boolcube.Point n) :
    Boolcube.Subcube.Mem (toCube (n := n) R) x ↔ Subcube.mem (n := n) R x := by
  classical
  unfold toCube Boolcube.Subcube.Mem Subcube.mem
  constructor
  · intro h i hi
    have hx := h i
    -- The `if` branch collapses using the membership assumption `hi`.
    -- Simplify the hypothesis using the fact that `i ∈ R.idx`.
    simp [hi] at hx
    -- The goal now reduces to a trivial equality on coordinates.
    simp [hi, hx]
  · intro h i
    by_cases hi : i ∈ R.idx
    · have hx := h i hi
      -- In the fixed coordinates, `toCube` and `R` agree by definition.
      simp [hi, hx]
    · -- Outside the fixed coordinates the membership predicate is trivially satisfied.
      simp [hi]

/-- The dimension of the converted cube matches that of the original subcube. -/
lemma dim_toCube {n : ℕ} (R : Subcube n) :
    (toCube (n := n) R).dim = Subcube.dimension (n := n) R := by
  classical
  unfold toCube Boolcube.Subcube.dim Boolcube.Subcube.support
  unfold Subcube.dimension
  -- The support of `toCube R` is exactly the set of fixed coordinates `R.idx`.
  have hset :
      Finset.univ.filter
          (fun i : Fin n =>
            (if h : i ∈ R.idx then some (R.val i h) else none).isSome)
          = R.idx := by
    -- Again we unfold the filtered set and identify it with `R.idx`.
    ext i; by_cases hi : i ∈ R.idx <;> simp [hi]
  -- The dimension of the cube produced by `toCube` matches that of `R`.
  simp [hset]

end BoolFunc.Subcube

end -- of file

