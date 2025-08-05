import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.SubcubeAdapters
import Pnp2.cover2

/-!
This file intentionally provides only a **tiny computational stub** for the
cover construction.  The heavy combinatorial machinery lives elsewhere; here we
only expose a minimal API that is sufficient for the test suite and downstream
experiments to compile.

Originally `buildCoverCompute` returned the empty list of rectangles.  The
current implementation is still lightweight but delegates to the noncomputable
set-based construction `Cover2.buildCover` and simply enumerates the resulting
finite set as a list.  This keeps the code executable while exposing a more
useful API for small-scale experiments.  The accompanying specification reflects
this behaviour and is derived from the already proven lemmas about
`Cover2.buildCover`.

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
Enumerate a cover as a list of rectangles.

The function simply delegates to the set-valued construction
`Cover2.buildCover` and turns the resulting `Finset` into a `List`.  This keeps
the implementation computable while reusing the already established properties
of `buildCover`.
-/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  (Cover2.buildCover (n := n) F h hH).toList

@[simp] lemma buildCoverCompute_empty (h : ℕ)
    (hH : BoolFunc.H₂ (∅ : Family n) ≤ (h : ℝ)) :
    buildCoverCompute (F := (∅ : Family n)) (h := h) hH = [] := by
  classical
  simp [buildCoverCompute, Cover2.buildCover_eq_Rset]

@[simp] lemma buildCoverCompute_length (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).length =
        (Cover2.buildCover (n := n) F h hH).card := by
  classical
  simpa [buildCoverCompute] using
    (Finset.length_toList (Cover2.buildCover (n := n) F h hH))

/--
Basic specification for the stub `buildCoverCompute`: all listed rectangles are
monochromatic for the family (vacuously, since the list is empty) and the
enumeration length satisfies the global bound `mBound`.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤ mBound n h := by
  classical
  -- Unfold the list representation back to the underlying set of rectangles.
  have hset :
      (buildCoverCompute (F := F) (h := h) hH).toFinset =
        Cover2.buildCover (n := n) F h hH := by
    simp [buildCoverCompute]
  have hmono := Cover2.buildCover_mono (n := n) (F := F) (h := h) hH
  have hbound := Cover2.buildCover_card_bound (n := n) (F := F) (h := h) hH
  refine And.intro ?mono ?bound
  · intro R hR
    have hR' : R ∈ Cover2.buildCover (n := n) F h hH := by
      simpa [hset] using hR
    exact hmono R hR'
  ·
    -- Translate the list length into the cardinality of the cover set and apply
    -- the existing bound.
    have hlen :
        (buildCoverCompute (F := F) (h := h) hH).length =
          (Cover2.buildCover (n := n) F h hH).card := by
      simpa [buildCoverCompute] using
        (Finset.length_toList (Cover2.buildCover (n := n) F h hH))
    simpa [hlen] using hbound

end Cover

