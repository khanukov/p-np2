import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.SubcubeAdapters

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
small executable interface used throughout the project.  The long‑term plan is
to hook it up to the efficient recursive construction developed in
`cover2.lean`.  As that algorithm is still under construction we currently
reuse the simple enumerator `buildCoverNaive` defined below.  Once the recursive
procedure is available this definition can seamlessly switch to it without
affecting external callers.

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
`buildCoverCompute` exposes a small executable interface for the cover
construction.  For the time being it simply delegates to `buildCoverNaive`,
which enumerates all points of the Boolean cube and records those on which all
functions evaluate to `true`.  Despite its exponential cost this implementation
is entirely constructive and suffices for experimentation.  Once the recursive
algorithm in `cover2.lean` is available this definition can switch to it without
affecting callers.

The parameters `h` and `hH` provide an upper bound on the collision entropy of
the family.  They are currently unused but are included so that the future
entropy‑aware implementation can rely on them without altering the interface.
-/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  buildCoverNaive (n := n) (F := F)

/--
Specification for `buildCoverCompute`.  The resulting list has no duplicates,
every listed subcube is monochromatic for the family and the length never
exceeds the number of available subcubes.  This follows directly from
`buildCoverNaive_spec`.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).Nodup ∧
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤
      Fintype.card (Subcube n) := by
  classical
  simpa [buildCoverCompute] using
    (buildCoverNaive_spec (n := n) (F := F))

end Cover

