import OldAttempts.BoolFunc
import OldAttempts.BoolFunc.Support
import OldAttempts.Boolcube
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

/--
Local notation for membership in a subcube of the Boolean cube.
The notation `x ∈ₛ R` should be read as “the point `x` belongs to the
subcube `R`”.  This mirrors the notation used for the legacy subcube
structure defined in `BoolFunc`.
-/
notation x " ∈ₛ " R => Boolcube.Subcube.Mem R x

namespace Boolcube.Subcube

/--
`R` is monochromatic for the function `f` if `f` takes a constant Boolean
value on all points of the subcube.  This mirrors the corresponding definition
for the legacy subcube representation used in other parts of the repository.
-/
def monochromaticFor {n : ℕ} (R : Subcube n) (f : BoolFunc.BFunc n) : Prop :=
  ∃ b : Bool, ∀ x, R.Mem x → f x = b

/--
`R` is jointly monochromatic for the family `F` if every function in `F`
assumes the same Boolean value on all points of `R`.
This lightweight wrapper mirrors the corresponding definition for the
simplified subcube structure used throughout the `cover2` development.
-/
def monochromaticForFamily {n : ℕ} (R : Subcube n) (F : BoolFunc.Family n) : Prop :=
  ∃ b : Bool, ∀ f ∈ F, ∀ x, R.Mem x → f x = b

/--
Construct a subcube by *freezing* the coordinates in `K` to match the values
of a base point `x`.

In our simplified representation a subcube is described by a function that
assigns to each coordinate either `none` (meaning the coordinate is free) or
`some b` (meaning the coordinate is fixed to the Boolean value `b`).
The constructor below freezes exactly the coordinates from the set `K`.
-/
def fromPoint {n : ℕ} (x : Point n) (K : Finset (Fin n)) : Subcube n :=
  ⟨fun i => if _ : i ∈ K then some (x i) else none⟩

/--
A point `y` belongs to `fromPoint x K` iff it agrees with `x` on every index in `K`.
-/
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

/--
The base point `x` always lies in the subcube obtained by freezing `K`.
-/
@[simp] lemma self_mem_fromPoint {n : ℕ} {x : Point n} {K : Finset (Fin n)} :
    x ∈ₛ fromPoint (n := n) x K := by
  classical
  -- Each coordinate in `K` obviously matches the corresponding bit of `x`.
  refine (mem_fromPoint (x := x) (K := K) (y := x)).2 ?_
  intro i hi; rfl

/--
The dimension of `fromPoint x K` is `n - |K|` because each frozen coordinate
reduces the number of degrees of freedom by one.
-/
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
  simp

/--
Membership in larger frozen sets implies membership in smaller ones.
If `L` freezes at least the coordinates of `K` and `y` belongs to `fromPoint x L`
then `y` also belongs to `fromPoint x K`.
-/
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

/-!
### Bridging the legacy `BoolFunc.Subcube` with the simplified `Boolcube.Subcube`

The original development represents subcubes via a pair `(idx, val)` where `idx`
collects the fixed coordinates and `val` records their Boolean values.  The
newer `Boolcube.Subcube` structure instead uses an option-valued function and is
more convenient for constructive manipulations.  The following helpers convert
between the two representations and establish basic properties.
-/
namespace BoolFunc.Subcube

/--
Convert an old-style subcube (specified by a set of fixed coordinates and their
Boolean values) into the simplified `Boolcube.Subcube` representation used in
`cover2`.  Each coordinate in `idx` becomes a fixed bit in the resulting cube,
while all other coordinates remain free.
-/
def toCube {n : ℕ} (R : Subcube n) : Boolcube.Subcube n :=
  ⟨fun i => if h : i ∈ R.idx then some (R.val i h) else none⟩

/--
Membership in the converted cube coincides with membership in the original
subcube.
-/
lemma mem_toCube {n : ℕ} (R : Subcube n) (x : Boolcube.Point n) :
    Boolcube.Subcube.Mem (toCube (n := n) R) x ↔ Subcube.mem (n := n) R x := by
  classical
  unfold toCube Boolcube.Subcube.Mem Subcube.mem
  constructor
  · intro h i hi
    have hx := h i
    -- The `if` branch collapses using the membership assumption `hi`
    -- and directly yields the desired equality.
    simpa [hi] using hx
  · intro h i
    by_cases hi : i ∈ R.idx
    · have hx := h i hi
      -- In the fixed coordinates, `toCube` and `R` agree by definition.
      simpa [hi] using hx
    · -- Outside the fixed coordinates the membership predicate is trivially
      -- satisfied.
      simp [hi]

/--
The dimension of the converted cube matches that of the original subcube.
-/
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
  simp

end BoolFunc.Subcube

