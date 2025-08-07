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

/--  Unfolding equation for `buildCoverAux`.  It exposes the first recursive
    step and is useful for subsequent reasoning.  The proof is currently a
    placeholder. -/
lemma buildCoverAux_unfold (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) (Rset : Finset (Subcube n)) :
    buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset =
      match firstUncovered (n := n) F Rset with
      | none => Rset
      | some _ =>
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH)
            (extendCover (n := n) F Rset) := by
  -- Proving this lemma amounts to unfolding the underlying well-founded
  -- fixpoint once.  A future version will invoke `WellFounded.fix_eq` and
  -- simplify the resulting expression so that the recursive call is exposed
  -- explicitly as `buildCoverAux (extendCover F Rset)`.  The technical details
  -- of that argument are still being worked out, hence the placeholder below.
  exact sorry

/--  If `firstUncovered` finds no witness, the recursive auxiliary function
    `buildCoverAux` leaves the current rectangle set unchanged.  This lemma
    exposes the base case of the recursion explicitly and will serve as a
    building block for more elaborate correctness proofs. -/
lemma buildCoverAux_none (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) {Rset : Finset (Subcube n)}
    (hfu : firstUncovered (n := n) F Rset = none) :
    buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset = Rset := by
  classical
  -- Apply the unfolding lemma and simplify using the hypothesis.
  simpa [hfu] using
    (buildCoverAux_unfold (n := n) (F := F) (h := h)
      (hH := hH) (Rset := Rset))

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

/-!
### Monochromaticity helper

To keep the repository building we provide a skeleton for the main
monochromaticity argument.  The following auxiliary lemma will eventually be
proved by a well‑founded induction over the measure `μ`.  Starting from a set of
monochromatic rectangles, the recursive call `buildCoverAux` should only insert
new rectangles that are again monochromatic.  Formalising the inductive step is
fairly involved and is left as future work.
-/

/--  Auxiliary lemma: assuming that all rectangles in `Rset` are monochromatic
    for `F`, any rectangle produced by the recursive call `buildCoverAux` is
    also monochromatic.  The proof is unfinished and currently represented by a
    `sorry`. -/
lemma buildCoverAux_mono (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ Rset,
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) →
        ∀ R ∈ buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset,
          Subcube.monochromaticForFamily R F := by
  classical
  intro Rset hMono
  -- Case distinction on whether an uncovered witness remains.  When the search
  -- fails, `buildCoverAux` returns the set unchanged and the conclusion follows
  -- directly from `hMono`.
  cases hfu : firstUncovered (n := n) F Rset with
  | none =>
      intro R hR
      -- Unfold the recursion using the helper lemma and reduce the goal.
      have hbase :=
        buildCoverAux_none (n := n) (F := F) (h := h)
          (hH := hH) (Rset := Rset) hfu
      have hRset : R ∈ Rset := by simpa [hbase] using hR
      -- Monochromaticity follows from the hypothesis on the initial set.
      simpa [hbase] using hMono R hRset
  | some p =>
      -- The inductive step will extend the rectangle set and invoke the
      -- recursive hypothesis on a strictly smaller measure.  Formalising this
      -- argument is non-trivial and remains future work.
      intro R hR
      exact sorry

/-- Every rectangle returned by `buildCover` is monochromatic for the family.
    The proof delegates to `buildCoverAux_mono`, instantiated at the empty
    starting set. -/
lemma buildCover_mono (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover (n := n) F h hH,
      Subcube.monochromaticForFamily R F := by
  classical
  -- Apply the auxiliary lemma to the empty starting set.  The initial
  -- collection contains no rectangles, hence the monochromaticity assumption is
  -- satisfied trivially.
  have haux :
      ∀ R ∈ buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) ∅,
        Subcube.monochromaticForFamily R F :=
    buildCoverAux_mono (n := n) (F := F) (h := h) (hH := hH) ∅ (by
      intro R hR; cases hR)
  -- The top-level `buildCover` simply invokes `buildCoverAux` on the empty set.
  simpa [buildCover] using haux

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

