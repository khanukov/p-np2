import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.SubcubeAdapters
import Pnp2.cover2

-- Silence linter suggestions about using `simp` instead of `simpa` in this file.
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
This module provides a small **executable interface** for the cover
construction.  The long‑term goal of the project is an efficient algorithm that
enumerates a modest collection of monochromatic subcubes covering all
`1`‑inputs of a family of Boolean functions.  The sophisticated machinery for
that algorithm lives in `cover2.lean` and its companion files and is still
under active development.

Historically this file exposed a tiny enumerator `buildCoverNaive` that scanned
the entire Boolean cube and recorded every point on which *all* functions
evaluate to `true`.  Each such point became a zero‑dimensional subcube.  While
simple, this approach is exponentially slow and therefore only suitable as a
temporary stand‑in.

We now define `buildCoverCompute` as a thin wrapper around the (currently
stubbed) recursive construction `Cover2.buildCover`.  Once the latter is fully
implemented, `buildCoverCompute` will automatically pick up the improved
behaviour while keeping a compact API for external users.

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
`buildCoverCompute` exposes a small executable interface for the cover
construction.  It delegates the heavy lifting to `Cover2.buildCover`, which
constructs a finite set of monochromatic subcubes.  We simply convert that
`Finset` to a list.  At the moment `Cover2.buildCover` is still a stub that
returns the empty set, but once the recursive algorithm in `cover2.lean` is
implemented this definition will automatically pick up the improved behaviour
without requiring changes to downstream code.

The arguments `h` and `hH` provide an upper bound on the collision entropy of
the family and are threaded through so that the future implementation can rely
on them.
-/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  (Cover2.buildCover (n := n) F h hH).toList

/--
Specification for `buildCoverCompute`.  The resulting list has no duplicates,
every listed subcube is monochromatic for the family and the length never
exceeds the number of available subcubes.  The statement mirrors
`buildCoverNaive_spec` but keeps the interface in terms of the entropy budget.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).Nodup ∧
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤
      Fintype.card (Subcube n) := by
  classical
  -- Abbreviate the underlying set of rectangles produced by `Cover2.buildCover`.
  set Rset := Cover2.buildCover (n := n) F h hH with hRset
  have hnodup : (buildCoverCompute (F := F) (h := h) hH).Nodup := by
    -- Converting a `Finset` to a list yields a `Nodup` list.
    simpa [buildCoverCompute, hRset] using (Finset.nodup_toList Rset)
  refine And.intro hnodup ?_
  -- Establish monochromaticity and the cardinality bound.
  refine And.intro ?mono ?bound
  · -- Every rectangle in the result originates from `Rset`.
    intro R hR
    -- Convert membership in the list to membership in the `Finset`.
    have hR_list : R ∈ Rset.toList := by
      -- Reduce the membership goal to the underlying list.
      have hmem : R ∈ (Rset.toList).toFinset := by
        simpa [buildCoverCompute, hRset] using hR
      exact (List.mem_toFinset).1 hmem
    have hR' : R ∈ Rset := (Finset.mem_toList (s := Rset)).1 hR_list
    -- Apply the monochromaticity lemma for `Cover2.buildCover`.
    exact Cover2.buildCover_mono (n := n) (F := F) (h := h) hH R hR'
  · -- Bounding the length reduces to bounding the cardinality of `Rset`.
    have hcard : Rset.card ≤ Fintype.card (Subcube n) :=
      Cover2.buildCover_card_univ_bound (n := n) (F := F) (h := h) hH
    have hlen : (buildCoverCompute (F := F) (h := h) hH).length = Rset.card := by
      simpa [buildCoverCompute, hRset] using (Finset.length_toList Rset)
    simpa [hlen]

end Cover
