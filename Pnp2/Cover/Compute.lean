import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.SubcubeAdapters
import Pnp2.Cover.Uncovered
import Pnp2.cover2

-- Silence linter suggestions about using `simp` instead of `simpa` in this file.
set_option linter.unnecessarySimpa false

/-!
This module provides a **lightweight executable wrapper** around the
non‑computable cover construction in `cover2.lean`.

The main development constructs a finite set of monochromatic subcubes via the
function `Cover2.buildCover`.  That definition lives in a classical world and
returns a `Finset`.  For experimentation it is convenient to obtain an actual
`List` of rectangles, hence the function `buildCoverCompute` below simply
enumerates the set produced by `Cover2.buildCover`.

The current implementation does not attempt to be efficient—the heavy lifting
is delegated to `Cover2.buildCover` which itself is still a placeholder in this
repository.  Nevertheless, providing this wrapper keeps the interface stable
while the constructive algorithm is being developed.

`Cover.Bounds` exposes the auxiliary function `mBound` together with several
useful arithmetic lemmas.  We re-export the most common ones so that users of
this module can reason about bounds without importing the full development.
-/

open Cover2

namespace Cover

-- Re-export the numeric bounds from `Cover2` for convenience.
export Cover2 (mBound mBound_pos mBound_zero two_le_mBound mBound_mono_left)

-- Basic Boolean-cube objects and Boolean-function families.
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)
open Boolcube.Subcube

variable {n : ℕ}

/--
`buildCoverNaive` is a tiny executable baseline for the cover construction.
It scans all points of the Boolean cube and records those on which **every**
function in the family evaluates to `true`.  Each such point becomes a
zero‑dimensional subcube.  The procedure is exponentially slow in `n` but keeps
the code entirely constructive and provides a convenient playground while the
efficient algorithm is being developed.
-/
noncomputable def buildCoverNaive (F : Family n) : List (Subcube n) :=
  ((Finset.univ.filter (fun x : Point n => ∀ f ∈ F, f x = true)).image
      (fun x => Subcube.point (n := n) x)).toList

/--
Basic specification for `buildCoverNaive`.
The resulting list has no duplicates, every listed cube is monochromatic for
the family (with colour `true`) and the length never exceeds the number of
available subcubes.
-/
lemma buildCoverNaive_spec (F : Family n) :
    (buildCoverNaive (n := n) (F := F)).Nodup ∧
    (∀ R ∈ (buildCoverNaive (n := n) (F := F)).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverNaive (n := n) (F := F)).length ≤
      Fintype.card (Subcube n) := by
  classical
  -- Abbreviate the underlying finite set of subcubes.
  set S :=
    (Finset.univ.filter (fun x : Point n => ∀ f ∈ F, f x = true)).image
      (fun x => Subcube.point (n := n) x) with hS
  have hlist : buildCoverNaive (n := n) (F := F) = S.toList := by
    simpa [buildCoverNaive, hS]
  have hnodup : (buildCoverNaive (n := n) (F := F)).Nodup := by
    simpa [hlist] using (Finset.nodup_toList S)
  refine And.intro hnodup ?_
  -- Establish monochromaticity and the cardinality bound.
  refine And.intro ?mono ?bound
  · -- Each element stems from a point where all functions evaluate to `true`.
    intro R hR
    have hR' : R ∈ S := by
      simpa [hlist] using hR
    rcases Finset.mem_image.mp hR' with ⟨x, hx, rfl⟩
    have hx' : ∀ f ∈ F, f x = true :=
      (Finset.mem_filter.mp hx).2
    refine ⟨true, ?_⟩
    intro f hf y hy
    have hy' : x = y :=
      (Subcube.mem_point_iff (x := x) (y := y)).1 hy
    simpa [hy'] using hx' f hf
  · -- The list enumerates a subset of all subcubes.
    have hcard : S.card ≤ Fintype.card (Subcube n) :=
      Finset.card_le_univ _
    have hlen : (buildCoverNaive (n := n) (F := F)).length = S.card := by
      simpa [hlist] using (Finset.length_toList S)
    simpa [hlen]

/--
`buildCoverCompute` enumerates the finite set of rectangles produced by
`Cover2.buildCover` as a list.  The construction itself is non‑computable but
results in a concrete `List` which is convenient for experimentation.
-/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  (Cover2.buildCover (n := n) F h hH).toList

/--
Specification for `buildCoverCompute`.  The returned list contains no duplicates,
its elements are precisely the rectangles produced by `Cover2.buildCover` and
its length is bounded by `mBound`.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).Nodup ∧
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        R ∈ Cover2.buildCover (n := n) F h hH) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤ mBound n h := by
  classical
  unfold buildCoverCompute
  -- Abbreviate the underlying set of rectangles.
  set Rset := Cover2.buildCover (n := n) F h hH with hRset
  -- Basic properties of `toList`.
  have hnodup : Rset.toList.Nodup := Finset.nodup_toList _
  have hmem : ∀ R ∈ Rset.toList.toFinset, R ∈ Rset := by
    intro R hR
    have hR_list : R ∈ Rset.toList := by
      simpa using (List.mem_toFinset.mp hR)
    simpa using (Finset.mem_toList.mp hR_list)
  -- Cardinality bound transfers to the length of the list.
  have hcard : Rset.card ≤ mBound n h :=
    Cover2.buildCover_card_bound (n := n) (F := F) (h := h) hH
  have hlen : Rset.toList.length ≤ mBound n h := by
    simpa [Finset.length_toList] using hcard
  -- Assemble the specification.
  refine And.intro ?_ (And.intro ?_ ?_)
  · simpa [hRset] using hnodup
  · intro R hR
    have hR' : R ∈ Rset := hmem R (by simpa [hRset] using hR)
    simpa [hRset] using hR'
  · simpa [hRset] using hlen

end Cover
