import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Uncovered
import Pnp2.Cover.Measure
import Pnp2.Cover.Bounds

/-!
This file supplies the recursive core of the covering construction.  The
original development used a trivial stub for `buildCover` that merely
performed a single call to `extendCover`.  Rewriting the function using a
well‑founded recursion on the measure `μ` avoids difficult termination issues
for the accompanying lemmas.

The actual correctness proofs are substantial and remain works in progress.
We nevertheless expose the intended API so that other parts of the repository
can already rely on the interface.  Lemmas that still await a complete proof
are marked with `sorry`.  They can be filled in once the missing arguments
have been formalised.
-/

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

namespace Cover2

variable {n : ℕ}

/--  Auxiliary relation stating that one rectangle set has a smaller measure
than another.  This relation is well‑founded because the measure takes values
in the natural numbers. -/
def μRel (F : Family n) (h : ℕ) :
    Finset (Subcube n) → Finset (Subcube n) → Prop :=
  fun R₁ R₂ => mu (n := n) F h R₁ < mu (n := n) F h R₂

/--  `μRel` is a well‑founded relation, enabling recursion on the measure. -/
lemma μRel_wf (F : Family n) (h : ℕ) :
    WellFounded (μRel (n := n) (F := F) h) := by
  -- The relation `μRel` is the inverse image of `<` on `ℕ` under the measure
  -- `μ`.  Well‑foundedness therefore follows from the well‑foundedness of
  -- `<` on the natural numbers.
  simpa [μRel] using
    (InvImage.wf (f := fun Rset : Finset (Subcube n) => mu (n := n) F h Rset)
      Nat.lt_wfRel.wf)

/-!
### Recursive cover construction

`buildCoverAux` implements the recursion directly via `WellFounded.fix`.
The function searches for an uncovered pair.  If none exists we return the
current rectangle set.  Otherwise we extend the set using `extendCover` and
recurse on the strictly smaller measure.
-/

noncomputable def buildCoverAux (F : Family n) (h : ℕ)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (Rset : Finset (Subcube n)) → Finset (Subcube n) :=
  (μRel_wf (n := n) (F := F) h).fix
    (fun Rset rec =>
      match hfu : firstUncovered (n := n) F Rset with
      | none      => Rset
      | some _    =>
          let R' := extendCover (n := n) F Rset
          -- Establish the recursive call on a strictly smaller measure.
          have hdrop : μRel (n := n) (F := F) h R' Rset := by
            have hne : firstUncovered (n := n) F Rset ≠ none := by
              simpa [hfu]
            simpa [μRel, R'] using
              (mu_extendCover_lt (n := n) (F := F)
                (Rset := Rset) (h := h) hne)
          rec R' hdrop)

/--  Top‑level wrapper starting the recursion from the empty set. -/
noncomputable def buildCover (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) ∅

/-!
### Specification lemmas

The following results summarise the expected behaviour of `buildCover`.  Their
current proofs are placeholders; replacing the `sorry` markers with complete
arguments is future work.
-/

/-- Every rectangle returned by `buildCover` is monochromatic for the family. -/
lemma buildCover_mono (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover (n := n) F h hH,
      Subcube.monochromaticForFamily R F := by
  -- To be completed.
  intro R hR
  exact sorry

/-- All `1`‑inputs of the family are covered by the rectangles from `buildCover`. -/
lemma buildCover_covers (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by
  -- To be completed.
  exact sorry

/-- The number of rectangles produced by `buildCover` is bounded by `mBound`. -/
lemma buildCover_card_bound (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h hH).card ≤ mBound n h := by
  -- To be completed.
  exact sorry

/-- If an uncovered pair exists initially, `buildCover` drops the measure. -/
lemma mu_buildCover_lt_start (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) ≠ none) :
    mu (n := n) F h (buildCover (n := n) F h hH) <
      mu (n := n) F h (∅ : Finset (Subcube n)) := by
  -- To be completed.
  exact sorry

end Cover2

