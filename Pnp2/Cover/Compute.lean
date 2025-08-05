import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.Canonical

-- The full cover construction lives in `cover2.lean`.  For the
-- computational wrapper we only need access to the *resulting* cover
-- packaged by `Cover2.coverFamily`, so we avoid importing the heavy
-- machinery directly and instead delegate to this canonical wrapper.
/-!
This lightweight module provides a purely constructive wrapper around the
heavy `cover` development.  To keep the test suite compiling we include only
the definitions needed by `Algorithms.SatCover` and postpone the actual proof
details.  The implementation will eventually mirror `Cover.buildCover`, but
for now we expose a stub version accompanied by admitted specifications.

`Cover.Bounds` exposes the auxiliary function `mBound` together with several
useful arithmetic lemmas.  We simply re-export those facts here so that the
computational wrapper can use them without depending on the full cover file.
-/

open Cover2

namespace Cover

-- Re-export the numeric bounds from `Cover2` for convenience.
export Cover2 (mBound mBound_pos mBound_zero two_le_mBound mBound_mono_left)

-- We pull in the basic Boolean-cube objects and Boolean-function families.
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)
open Boolcube.Subcube

variable {n : ℕ}

/--
`buildCoverCompute` enumerates the rectangles of the canonical cover.

It simply turns the finite set `Cover2.coverFamily F h hH` into a list.
This is a thin wrapper whose purpose is to expose a fully constructive
interface: downstream algorithms can iterate over the list without
opening the underlying `Finset`.
-/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  (Cover2.coverFamily (n := n) (F := F) (h := h) hH).toList

@[simp] lemma buildCoverCompute_empty (h : ℕ)
    (hH : BoolFunc.H₂ (∅ : Family n) ≤ (h : ℝ)) :
    buildCoverCompute (F := (∅ : Family n)) (h := h) hH = [] := by
  classical
  -- `coverFamily` reduces to the underlying `buildCover`, which returns the
  -- supplied rectangle set `Rset`.  With the default `Rset = ∅` we obtain an
  -- empty list.
  have hcov : Cover2.coverFamily (n := n) (F := (∅ : Family n))
      (h := h) hH = (∅ : Finset (Subcube n)) := by
    simpa [Cover2.coverFamily] using
      (Cover2.buildCover_eq_Rset (n := n) (F := (∅ : Family n))
        (h := h) hH (Rset := (∅ : Finset (Subcube n))))
  simpa [buildCoverCompute, hcov]

/-- The length of the enumeration coincides with the cardinality of the
underlying canonical cover. -/
@[simp] lemma buildCoverCompute_length (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).length =
      (Cover2.coverFamily (n := n) (F := F) (h := h) hH).card := by
  classical
  -- `Finset.length_toList` converts the equality between list length and
  -- set cardinality.
  simpa [buildCoverCompute] using
    (Finset.length_toList (Cover2.coverFamily (n := n) (F := F) (h := h) hH))
/--
Basic specification for `buildCoverCompute`. It simply expands `Cover.coverFamily` into a list,
so the rectangles remain monochromatic and the length bound follows from `coverFamily_card_bound`.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤ mBound n h := by
  classical
  -- The list is obtained from `coverFamily`, hence its `toFinset` is the
  -- same set and all properties transfer from the canonical cover.
  refine And.intro ?mono ?bound
  · intro R hR
    -- Unfold `buildCoverCompute` and reduce membership to the canonical
    -- cover set, then apply `coverFamily_mono`.
    have hmem' : R ∈
        ((Cover2.coverFamily (n := n) (F := F) (h := h) hH).toList).toFinset := by
      simpa [buildCoverCompute] using hR
    have hmem : R ∈ Cover2.coverFamily (n := n) (F := F) (h := h) hH := by
      simpa [Finset.toList_toFinset] using hmem'
    exact Cover2.coverFamily_mono (n := n) (F := F) (h := h) hH R hmem
  ·
    -- The length bound follows from the corresponding cardinality bound.
    have hcard := Cover2.coverFamily_card_bound
      (n := n) (F := F) (h := h) hH
    -- Replace the list length by the set cardinality via the previous lemma.
    simpa [buildCoverCompute, buildCoverCompute_length] using hcard

end Cover
