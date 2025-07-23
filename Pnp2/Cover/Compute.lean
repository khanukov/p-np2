import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy

/-!
This lightweight module provides a purely constructive wrapper around the
heavy `cover` development.  To keep the test suite compiling we include only
the definitions needed by `Algorithms.SatCover` and postpone the actual proof
details.  The implementation will eventually mirror `Cover.buildCover`, but
for now we expose a stub version accompanied by admitted specifications.
-/
-- Basic definitions reproduced here to avoid depending on the full cover file.
@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

namespace Cover

open BoolFunc

variable {n : ℕ}

/--
`buildCoverCompute` is a constructive cover enumerator used by the SAT
procedure.  The current implementation is a placeholder that returns an
empty list; the full algorithm will mirror `Cover.buildCover`.
-/
/-!  Constructive cover enumerator used by the SAT algorithm.  We simply
convert the existing `coverFamily` from `Cover` into a list.  This keeps the
implementation executable while reusing the proven specifications of
`coverFamily`. -/
noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  (Cover.coverFamily (F := F) (h := h) hH).toList

/--
Specification of `buildCoverCompute`.  The rectangles cover all positive
inputs of the family, are monochromatic, and the list length is bounded by
`mBound`.  These properties are admitted for now.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ f ∈ F, ∀ x, f x = true →
        ∃ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset, x ∈ₛ R) ∧
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤ mBound n h := by
  classical
  -- Abbreviate the underlying set of rectangles from `coverFamily`.
  set Rset := Cover.coverFamily (F := F) (h := h) hH
  have hcov := Cover.coverFamily_spec_cover (F := F) (h := h) hH
  have hmono := Cover.coverFamily_mono (F := F) (h := h) hH
  have hcard := Cover.coverFamily_card_bound (F := F) (h := h) hH
  constructor
  · intro f hf x hx
    rcases hcov f hf x hx with ⟨R, hR, hxR⟩
    refine ⟨R, ?_, hxR⟩
    -- Convert membership of `R` from the finset to the list.
    have hmem_list : R ∈ Rset.toList := (Finset.mem_toList).2 hR
    have hmem_fin : R ∈ Rset.toList.toFinset := by
      simpa using (List.mem_toFinset).2 hmem_list
    simpa [buildCoverCompute, Rset] using hmem_fin
  constructor
  · intro R hR
    -- Translate membership back to the finset to reuse `hmono`.
    have hR' : R ∈ Rset := by
      have hlist : R ∈ Rset.toList := (List.mem_toFinset).1 (by simpa [buildCoverCompute, Rset] using hR)
      simpa using (Finset.mem_toList).1 hlist
    exact hmono R hR'
  -- Length of the list equals the cardinality of the finset.
  have hlen : (buildCoverCompute (F := F) (h := h) hH).length = Rset.card := by
    simp [buildCoverCompute, Rset, Finset.length_toList]
  simpa [hlen, Rset] using hcard

end Cover
