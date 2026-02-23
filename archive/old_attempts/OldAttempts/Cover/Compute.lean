import OldAttempts.Boolcube
import OldAttempts.BoolFunc
import OldAttempts.entropy
import OldAttempts.Cover.Bounds
import OldAttempts.Cover.SubcubeAdapters
import OldAttempts.Cover.Uncovered
import OldAttempts.cover2 -- numeric bounds and helpers

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

In addition to this baseline enumerator we expose `buildCoverCompute`, a
small executable interface used throughout the project.  The long‑term goal is
an efficient recursive algorithm, but for now we provide a simple constructive
baseline: we scan the entire Boolean cube and record every point on which *some*
function from the family evaluates to `true`.  Each such point becomes a
zero‑dimensional subcube.  While exponentially slow in `n`, this procedure is
easy to reason about and suffices for experimentation.  Future improvements to
the recursive construction can replace this definition without affecting
callers.

`Cover.Bounds` exposes the auxiliary function `mBound` together with several
useful arithmetic lemmas.  We re-export the most common ones so that users of
this module can reason about bounds without importing the full development.
-/

namespace Cover

-- Re-export the numeric bounds for convenience.
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
`buildCoverCompute` enumerates all points of the Boolean cube on which at least
one function from the family evaluates to `true` and converts each such point
into a zero‑dimensional subcube.  This produces a trivial cover of all `1`
inputs of the family.
-/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  ((Finset.univ.filter (fun x : Point n => ∃ f ∈ F, f x = true)).image
      (fun x => Subcube.point (n := n) x)).toList

/--
Specification for `buildCoverCompute`.  The resulting list has no duplicates,
covers every `1`‑input of the family and its length never exceeds the number of
available subcubes.  This is immediate from the explicit construction above.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).Nodup ∧
    (Cover2.AllOnesCovered (n := n) F
        (buildCoverCompute (F := F) (h := h) hH).toFinset) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤
      Fintype.card (Subcube n) := by
  classical
  -- Abbreviate the underlying finite set of subcubes.
  set S : Finset (Subcube n) :=
    (Finset.univ.filter (fun x : Point n => ∃ f ∈ F, f x = true)).image
      (fun x => Subcube.point (n := n) x) with hS
  -- The produced list is `S.toList`.
  have hlist : buildCoverCompute (F := F) (h := h) hH = S.toList := by
    simpa [buildCoverCompute, hS]
  -- Establish duplicate freedom.
  have hnodup : (buildCoverCompute (F := F) (h := h) hH).Nodup := by
    simpa [hlist] using (Finset.nodup_toList S)
  refine And.intro hnodup ?_
  -- Remaining obligations: coverage and size bound.
  refine And.intro ?cover ?bound
  · -- Every `1`‑input is covered by the point subcube at the corresponding point.
    intro f hf x hx
    -- The point `x` appears in the filtered set of points.
    have hxfilter : x ∈
        (Finset.univ.filter fun y : Point n => ∃ f ∈ F, f y = true) := by
      refine Finset.mem_filter.mpr ?_
      exact ⟨Finset.mem_univ _, ⟨f, hf, hx⟩⟩
    -- Hence the corresponding point subcube belongs to `S`.
    have hxS : Subcube.point (n := n) x ∈ S := by
      exact Finset.mem_image.mpr ⟨x, hxfilter, rfl⟩
    -- Convert membership in `S` to membership in the produced list.
    have hxlist : Subcube.point (n := n) x ∈
        (buildCoverCompute (F := F) (h := h) hH).toFinset := by
      simpa [hlist] using hxS
    -- Finally `x` is obviously contained in its point subcube.
    have hxmem : x ∈ₛ Subcube.point (n := n) x :=
      (Subcube.mem_point_iff (x := x) (y := x)).2 rfl
    exact ⟨_, hxlist, hxmem⟩
  · -- The list enumerates a subset of all subcubes.
    have hcard : S.card ≤ Fintype.card (Subcube n) :=
      Finset.card_le_univ _
    have hlen : (buildCoverCompute (F := F) (h := h) hH).length = S.card := by
      simpa [hlist] using (Finset.length_toList S)
    simpa [hlen] using hcard

end Cover

