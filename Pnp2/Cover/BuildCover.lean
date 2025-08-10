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

/--  A rectangle set cannot have a strictly smaller measure than itself. -/
lemma μRel_irrefl (F : Family n) (h : ℕ) (Rset : Finset (Subcube n)) :
    ¬ μRel (n := n) (F := F) h Rset Rset := by
  intro hlt
  -- The measure `μ` takes values in `ℕ`, where `<` is irreflexive.
  exact lt_irrefl _ hlt

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

  set_option linter.unusedSimpArgs false in
  /-- Technical unfolding with an equation binder:
      this matches exactly what `WellFounded.fix_eq` produces. -/
  lemma buildCoverAux_unfold_eq (F : Family n) (h : ℕ)
      (hH : BoolFunc.H₂ F ≤ (h : ℝ)) (Rset : Finset (Subcube n)) :
    buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset =
      match _hfc : firstUncovered (n := n) F Rset with
      | none   => Rset
      | some _ =>
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH)
            (extendCover (n := n) F Rset) := by
    classical
    -- Use `fix_eq` with exactly the same functional as in the `def` above.
    simpa [buildCoverAux] using
      (WellFounded.fix_eq
        (C := fun _ => Finset (Subcube n))
        (μRel_wf (n := n) (F := F) h)
        (fun Rset rec =>
          match _hfc : firstUncovered (n := n) F Rset with
          | none   => Rset
          | some _ =>
              let R' := extendCover (n := n) F Rset
              -- Establish the recursive call on a strictly smaller measure.
              have hdrop : μRel (n := n) (F := F) h R' Rset := by
                have hne : firstUncovered (n := n) F Rset ≠ none := by
                  simpa [_hfc]
                simpa [μRel, R'] using
                  (mu_extendCover_lt (n := n) (F := F)
                    (Rset := Rset) (h := h) hne)
              rec R' hdrop)
        Rset)

  set_option linter.unusedSimpArgs false in
  /--  Unfolding equation for `buildCoverAux`.  It exposes the first recursive
      step and is useful for subsequent reasoning. -/
  lemma buildCoverAux_unfold (F : Family n) (h : ℕ)
      (hH : BoolFunc.H₂ F ≤ (h : ℝ)) (Rset : Finset (Subcube n)) :
    buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset =
      match firstUncovered (n := n) F Rset with
      | none   => Rset
      | some _ =>
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH)
            (extendCover (n := n) F Rset) := by
    classical
    -- Reduce to the technical version and discharge the binder by case splitting.
    cases hfu : firstUncovered (n := n) F Rset with
    | none   =>
        have h' :=
          buildCoverAux_unfold_eq (n := n) (F := F) (h := h) (hH := hH)
            (Rset := Rset)
        -- Simplify the technical equation using the case hypothesis.
        -- Specialise the technical lemma and simplify using the hypothesis.
        -- A direct rewrite removes the `match` binder produced by `fix_eq`.
        rw [hfu] at h'
        simpa using h'
    | some _ =>
        have h' :=
          buildCoverAux_unfold_eq (n := n) (F := F) (h := h) (hH := hH)
            (Rset := Rset)
        -- Again simplify with the case hypothesis to expose the recursive call.
        -- In the recursive case the same rewrite exposes the recursive call.
        rw [hfu] at h'
        simpa using h'

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

/--  If the initial search finds no uncovered pair, `buildCover` returns the
    empty rectangle set.  This is an immediate consequence of the base case for
    `buildCoverAux`. -/
lemma buildCover_empty_of_none (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) = none) :
    buildCover (n := n) F h hH = (∅ : Finset (Subcube n)) := by
  classical
  -- Expand the definition and apply the auxiliary lemma specialised to the
  -- empty starting set.
  unfold buildCover
  simpa using
    (buildCoverAux_none (n := n) (F := F) (h := h)
      (hH := hH) (Rset := (∅ : Finset (Subcube n))) hfu)

/-!
### Pointwise monochromatic cover

In this section we establish that the cover construction preserves the weaker
invariant that each rectangle is monochromatic for every function of the family
individually.  The colours may differ between functions, but each function is
constant on every rectangle produced by the algorithm.
-/

/--
Pointwise monochromaticity for the auxiliary recursion.  Starting from a set
`Rset` where every rectangle is monochromatic for each `g ∈ F`, the result of
`buildCoverAux` enjoys the same property.
-/
lemma buildCoverAux_pointwiseMono (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ Rset,
      (∀ R ∈ Rset, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g) →
        ∀ R ∈ buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset,
          ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g := by
  classical
  intro Rset
  -- We prove the statement by well-founded induction over `μRel`.
  refine (μRel_wf (n := n) (F := F) h).induction Rset
    (C := fun Rset =>
      (∀ R ∈ Rset, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g) →
        ∀ R ∈ buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset,
          ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g) ?step
  intro Rset IH hMono R hR
  -- Unfold the recursion to inspect the first step.
  cases hfu : firstUncovered (n := n) F Rset with
  | none =>
      -- Base case: no uncovered pairs remain and the result equals `Rset`.
      have hbase :=
        buildCoverAux_none (n := n) (F := F) (h := h)
          (hH := hH) (Rset := Rset) hfu
      have hRset : R ∈ Rset := by simpa [hbase] using hR
      intro g hg
      simpa [hbase] using hMono R hRset g hg
  | some p =>
      -- Recursive case: extend the cover and apply the inductive hypothesis.
      have hrec :=
        buildCoverAux_unfold (n := n) (F := F) (h := h)
          (hH := hH) (Rset := Rset)
      have hR' : R ∈
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH)
            (extendCover (n := n) F Rset) := by
        simpa [hrec, hfu] using hR
      -- The measure drops strictly after adding the new rectangle.
      have hdrop : μRel (n := n) (F := F) h
          (extendCover (n := n) F Rset) Rset := by
        have hne : firstUncovered (n := n) F Rset ≠ none := by
          simpa [hfu]
        simpa [μRel] using
          mu_extendCover_lt (n := n) (F := F) (Rset := Rset) (h := h) hne
      -- The extended set retains pointwise monochromaticity.
      have hMono' :
          ∀ R ∈ extendCover (n := n) F Rset, ∀ g ∈ F,
            Boolcube.Subcube.monochromaticFor R g :=
        extendCover_pointwiseMono (n := n) (F := F) (Rset := Rset) hMono
      -- Apply the inductive hypothesis to the smaller measure.
      have hIH := IH (extendCover (n := n) F Rset) hdrop hMono' R hR'
      intro g hg
      exact hIH g hg

/--
Pointwise monochromaticity for the top-level cover.  Every rectangle produced by
`buildCover` is constant for each function of the family.
-/
lemma buildCover_pointwiseMono (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover (n := n) F h hH, ∀ g ∈ F,
      Boolcube.Subcube.monochromaticFor R g := by
  classical
  -- Specialise the auxiliary lemma to the empty starting set.
  have haux :
      ∀ R ∈ buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) ∅,
        ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g :=
    buildCoverAux_pointwiseMono (n := n) (F := F) (h := h) (hH := hH) ∅ (by
      intro R hR g hg; cases hR)
  simpa [buildCover] using haux

/-!
### Specification lemmas

The following results summarise the expected behaviour of `buildCover`.  Their
current proofs are placeholders; replacing the `sorry` markers with complete
arguments is future work.
-/


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

