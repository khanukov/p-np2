import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.SubcubeAdapters
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
Enumerate the rectangles returned by `Cover2.buildCover` as a list.  The list is
free of duplicates and its cardinality agrees with that of the underlying
`Finset`.

At the moment `Cover2.buildCover` itself is a stub which always produces the
empty set, so this function merely returns `[]`.  Once the full construction is
ported, this wrapper will automatically expose the computed rectangles as a
list.
--/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  -- Convert the finite set of rectangles into an explicit list.
  (Cover2.buildCover (n := n) F h hH).toList

@[simp] lemma buildCoverCompute_empty (h : ℕ)
    (hH : BoolFunc.H₂ (∅ : Family n) ≤ (h : ℝ)) :
    buildCoverCompute (F := (∅ : Family n)) (h := h) hH = [] := by
  classical
  -- `buildCover` returns the empty set, whose list enumeration is `[]`.
  have hres := Cover2.buildCover_eq_Rset
    (n := n) (F := (∅ : Family n)) (h := h) (_hH := hH)
    (Rset := (∅ : Finset (Subcube n)))
  -- Rewrite using the characterisation of `buildCover` on the empty family.
  simpa [buildCoverCompute, hres]

/--
The length of the list produced by `buildCoverCompute` coincides with the
cardinality of the underlying set returned by `Cover2.buildCover`.
-/
@[simp] lemma buildCoverCompute_length (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).length =
      (Cover2.buildCover (n := n) F h hH).card := by
  -- Finsets enumerate to lists without repetition and of matching size.
  classical
  simpa [buildCoverCompute] using
    (Finset.length_toList (Cover2.buildCover (n := n) F h hH))

/--
The list produced by `buildCoverCompute` contains each rectangle at most once.
This is a direct consequence of enumerating a `Finset` via `toList`.
-/
@[simp] lemma buildCoverCompute_nodup (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).Nodup := by
  classical
  -- `Finset.toList` yields a list without duplicates.
  simpa [buildCoverCompute] using
    (Finset.nodup_toList (Cover2.buildCover (n := n) F h hH))

/--
The `Finset` of rectangles enumerated by `buildCoverCompute` agrees with
`Cover2.buildCover`.  This convenience lemma allows translating membership
statements between the list and the underlying set without manual rewrites.
-/
@[simp] lemma buildCoverCompute_toFinset (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).toFinset =
      Cover2.buildCover (n := n) F h hH := by
  classical
  -- `Finset.toList` followed by `List.toFinset` yields the original set.
  ext R
  simp [buildCoverCompute]

/--
The list produced by `buildCoverCompute` is empty if and only if the
underlying set of rectangles from `Cover2.buildCover` is empty.  This
lemma is handy when reasoning about trivial families where the cover
vanishes entirely.
-/
@[simp] lemma buildCoverCompute_nil_iff (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    buildCoverCompute (F := F) (h := h) hH = [] ↔
      Cover2.buildCover (n := n) F h hH = (∅ : Finset (Subcube n)) := by
  classical
  constructor
  · intro hlist
    -- Convert the hypothesis to a statement about cardinalities and use it
    -- to deduce that the underlying `Finset` has zero elements.
    have hlen : (buildCoverCompute (F := F) (h := h) hH).length = 0 := by
      simpa [hlist]
    -- The length of the enumeration agrees with the cardinality of the
    -- original set of rectangles.
    have hcard : (Cover2.buildCover (n := n) F h hH).card = 0 := by
      -- Rewrite the above length in terms of the cardinality.
      have := (buildCoverCompute_length (F := F) (h := h) hH).symm
      simpa [hlen] using this
    -- A finite set with zero elements is equal to `∅`.
    exact Finset.card_eq_zero.mp hcard
  · intro hset
    -- Start from the assumption that the set of rectangles is empty and
    -- translate it to the list enumeration.
    have hcard : (Cover2.buildCover (n := n) F h hH).card = 0 := by
      simpa [hset]
    -- The list has matching length, hence it must also be empty.
    have hlen : (buildCoverCompute (F := F) (h := h) hH).length = 0 := by
      -- Use the length/cardinality correspondence.
      have := buildCoverCompute_length (F := F) (h := h) hH
      simpa [hcard] using this
    -- Lists of length zero are definitionally empty.
    exact List.length_eq_zero_iff.mp hlen

/--
Basic specification for the stub `buildCoverCompute`: all listed rectangles are
monochromatic for the family (vacuously, since the list is empty) and the
enumeration length satisfies the global bound `mBound`.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).Nodup ∧
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤ mBound n h := by
  refine And.intro ?nodup ?mono_bound
  ·
    -- `buildCoverCompute` enumerates a `Finset`, hence no duplicates occur.
    simpa using
      (buildCoverCompute_nodup (F := F) (h := h) hH)
  ·
    -- Split the remaining obligations: monochromaticity and cardinality bound.
    refine And.intro ?mono ?bound
    · intro R hR
      -- Translate membership in the enumerated list back to the underlying set
      -- of rectangles and reuse `buildCover_mono`.
      have hR' : R ∈ Cover2.buildCover (n := n) F h hH := by
        -- The conversion from list to set is handled by
        -- `buildCoverCompute_toFinset`.
        simpa [buildCoverCompute_toFinset] using hR
      exact Cover2.buildCover_mono (n := n) (F := F) (h := h) hH R hR'
    ·
      -- The length of the list equals the cardinality of the set, which is
      -- bounded by `mBound` via `buildCover_card_bound`.
      have hcard := Cover2.buildCover_card_bound
        (n := n) (F := F) (h := h) hH
      -- Rewrite the goal using the length/cardinality equality.
      simpa [buildCoverCompute_length] using hcard

end Cover

