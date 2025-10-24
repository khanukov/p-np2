import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Uncovered
import Pnp2.Cover.Measure
import Pnp2.Cover.Bounds

/-!
This file supplies the recursive core of the covering construction.  Earlier
drafts contained only a stub for `buildCover` and postponed the termination
argument.  We now run the recursion on the augmented lexicographic measure from
`Measure.lean`.  Its components track the number of uncovered supports, the
entropy surplus, and a final tie-breaker given by the raw count of uncovered
witnesses.  The lemmas below show that each recursive step strictly decreases
this measure, yielding a fully formalised recursion without appealing to any
axioms.  The implementation stays close to the blueprint outlined in the
documentation and exposes the intended API for downstream developments.
-/

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

namespace Cover2

variable {n : ℕ}

/--  Auxiliary relation stating that one rectangle set has a smaller augmented
measure than another. -/
def μRel (F : Family n) (h : ℕ) :
    Finset (Subcube n) → Finset (Subcube n) → Prop :=
  fun R₁ R₂ =>
    muLexTripleOrder (muLexTriple (n := n) (F := F) (h := h) R₁)
      (muLexTriple (n := n) (F := F) (h := h) R₂)

/--  `μRel` is a well‑founded relation, enabling recursion on the lexicographic
measure. -/
lemma μRel_wf (F : Family n) (h : ℕ) :
    WellFounded (μRel (n := n) (F := F) h) := by
  -- This is an `InvImage` of the well-founded lexicographic order on `ℕ³`.
  change
      WellFounded fun R₁ R₂ : Finset (Subcube n) =>
        muLexTripleOrder (muLexTriple (n := n) (F := F) (h := h) R₁)
          (muLexTriple (n := n) (F := F) (h := h) R₂)
  simpa [muLexTriple] using muLexTriple_wf (n := n) (F := F) (h := h)

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
              -- The first uncovered point is `some _`, so the option is nonempty.
              -- `simp` suffices; no rewrite is required after the computation.
              simp [hfu]
            simpa [μRel, R'] using
              (muLexTriple_extendCover_lt (n := n) (F := F)
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
                  -- From the assumption that `firstUncovered` returns `some _`.
                  simp [_hfc]
                simpa [μRel, R'] using
                  (muLexTriple_extendCover_lt (n := n) (F := F)
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
individually.  Earlier drafts aimed for the stronger predicate
`Subcube.monochromaticForFamily`, but the current algorithm only guarantees the
pointwise version: the colours may differ between functions, yet each function is
constant on every rectangle produced by the construction.
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
        simp [hrec, hfu] at hR
        exact hR
      -- The measure drops strictly after adding the new rectangle.
      have hdrop : μRel (n := n) (F := F) h
          (extendCover (n := n) F Rset) Rset := by
        have hne : firstUncovered (n := n) F Rset ≠ none := by
          -- Under hypothesis `hfu`, the result is `some _`, hence `≠ none`.
          simp [hfu]
        simpa [μRel] using
          muLexTriple_extendCover_lt (n := n) (F := F)
            (Rset := Rset) (h := h) hne
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

/--
Every `1`-input of every `f ∈ F` is eventually covered by the rectangles
returned by `buildCoverAux`.  This lemma establishes the coverage invariant for
the recursive construction.
-/
lemma buildCoverAux_covers (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ Rset,
      AllOnesCovered (n := n) F
        (buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset) := by
  classical
  intro Rset
  -- We prove the statement by well-founded induction over the lexicographic
  -- measure introduced above.
  refine (μRel_wf (n := n) (F := F) h).induction Rset
    (C := fun Rset =>
      AllOnesCovered (n := n) F
        (buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset)) ?step
  intro Rset IH
  -- Unfold the recursion to inspect the first branch.
  cases hfu : firstUncovered (n := n) F Rset with
  | none =>
      -- Base case: no uncovered pairs remain.  The result equals `Rset` and the
      -- desired property follows directly from `firstUncovered_none_iff`.
      have hcov :
          AllOnesCovered (n := n) F Rset :=
        (firstUncovered_none_iff_AllOnesCovered (n := n) (F := F)
          (Rset := Rset)).1 hfu
      have hbase :
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset = Rset :=
        buildCoverAux_none (n := n) (F := F) (h := h)
          (hH := hH) (Rset := Rset) hfu
      simpa [hbase] using hcov
  | some _ =>
      -- Recursive case: extend the cover and apply the inductive hypothesis on
      -- the strictly smaller measure.
      -- In this branch `firstUncovered` produced a witness, so `extendCover`
      -- indeed removes at least that point and therefore decreases the measure.
      have h1 : buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset =
          match firstUncovered (n := n) F Rset with
          | none   => Rset
          | some _ => buildCoverAux (n := n) (F := F) (h := h) (_hH := hH)
              (extendCover (n := n) F Rset) :=
        buildCoverAux_unfold (n := n) (F := F) (h := h)
          (hH := hH) (Rset := Rset)
      have hrec :
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset =
            buildCoverAux (n := n) (F := F) (h := h) (_hH := hH)
              (extendCover (n := n) F Rset) := by
        simpa [hfu] using h1
      -- The measure strictly decreases after `extendCover`.
      have hdrop : μRel (n := n) (F := F) h
          (extendCover (n := n) F Rset) Rset := by
        have hne : firstUncovered (n := n) F Rset ≠ none := by
          -- The uncovered point is present, so the option is not `none`.
          simp [hfu]
        simpa [μRel] using
          muLexTriple_extendCover_lt (n := n) (F := F)
            (Rset := Rset) (h := h) hne
      -- Apply the inductive hypothesis to the strictly smaller measure.
      have hIH := IH (extendCover (n := n) F Rset) hdrop
      -- Rewrite using the unfolding equation to obtain the desired result.
      simpa [hrec] using hIH

/-!
### Specification lemma

The following result records the key property of `buildCover`: every `1`‑input
of the family appears in at least one rectangle produced by the construction.
This statement suffices for downstream developments; quantitative bounds on the
size of the cover are provided by separate APIs.
-/


/-- All `1`‑inputs of the family are covered by the rectangles from `buildCover`. -/
lemma buildCover_covers (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by
  classical
  -- Specialise the auxiliary coverage lemma to the empty starting set.
  have haux :=
    buildCoverAux_covers (n := n) (F := F) (h := h) (hH := hH) (Rset := (∅))
  -- The definition of `buildCover` unfolds to a call to `buildCoverAux` on `∅`.
  simpa [buildCover] using haux



/-!
Quantitative bounds for the cover are now derived from the explicit catalogue of
rectangles that `extendCover` may insert.  Every step freezes the coordinates
from `supportUnion F`, hence there are at most `2^n` distinct candidates.
-/

/-- Catalogue of rectangles reachable by the cover construction. -/
noncomputable def coverUniverse (F : Family n) : Finset (Subcube n) :=
  (Finset.univ.image fun x : Boolcube.Point n =>
    Boolcube.Subcube.fromPoint (n := n) x (supportUnion (n := n) F))

/-- `extendCover` never leaves the catalogue `coverUniverse`. -/
lemma extendCover_subset_coverUniverse (F : Family n)
    (Rset : Finset (Subcube n))
    (hsubset : Rset ⊆ coverUniverse (n := n) F) :
    extendCover (n := n) F Rset ⊆ coverUniverse (n := n) F := by
  classical
  intro R hR
  cases hfu : firstUncovered (n := n) F Rset with
  | none =>
      have hmem : R ∈ Rset := by
        simp [extendCover, hfu] at hR
        exact hR
      exact hsubset hmem
  | some p =>
      have hmem : R ∈ Rset ∪
          {Boolcube.Subcube.fromPoint (n := n) p.2 (supportUnion (n := n) F)} := by
        simpa [extendCover, hfu] using hR
      rcases Finset.mem_union.mp hmem with hRset | hnew
      · exact hsubset hRset
      · have hsingle : R =
            Boolcube.Subcube.fromPoint (n := n) p.2 (supportUnion (n := n) F) :=
          Finset.mem_singleton.mp hnew
        subst hsingle
        refine Finset.mem_image.mpr ?_
        refine ⟨p.2, ?_, rfl⟩
        exact Finset.mem_univ _

/-- `buildCoverAux` remains inside `coverUniverse` provided the starting set does. -/
lemma buildCoverAux_subset_coverUniverse (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ Rset,
      Rset ⊆ coverUniverse (n := n) F →
        buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset ⊆
          coverUniverse (n := n) F := by
  classical
  intro Rset
  refine (μRel_wf (n := n) (F := F) h).induction Rset
    (C := fun Rset =>
      Rset ⊆ coverUniverse (n := n) F →
        buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset ⊆
          coverUniverse (n := n) F) ?step
  intro Rset IH hsubset R hR
  cases hfu : firstUncovered (n := n) F Rset with
  | none =>
      have hbase :
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH) Rset = Rset :=
        buildCoverAux_none (n := n) (F := F) (h := h) (hH := hH)
          (Rset := Rset) hfu
      have hmem : R ∈ Rset := by
        simp [hbase] at hR
        exact hR
      exact hsubset hmem
  | some p =>
      have hrec :=
        buildCoverAux_unfold (n := n) (F := F) (h := h)
          (hH := hH) (Rset := Rset)
      have hR' : R ∈
          buildCoverAux (n := n) (F := F) (h := h) (_hH := hH)
            (extendCover (n := n) F Rset) := by
        simp [hrec, hfu] at hR
        exact hR
      have hdrop : μRel (n := n) (F := F) h
          (extendCover (n := n) F Rset) Rset := by
        have hne : firstUncovered (n := n) F Rset ≠ none := by simp [hfu]
        simpa [μRel] using
          muLexTriple_extendCover_lt (n := n) (F := F)
            (Rset := Rset) (h := h) hne
      have hsubset' : extendCover (n := n) F Rset ⊆ coverUniverse (n := n) F :=
        extendCover_subset_coverUniverse (F := F) (Rset := Rset) hsubset
      exact (IH (extendCover (n := n) F Rset) hdrop hsubset') hR'

/-- The final cover is contained in the catalogue of admissible rectangles. -/
lemma buildCover_subset_coverUniverse (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    buildCover (n := n) F h hH ⊆ coverUniverse (n := n) F := by
  classical
  have haux := buildCoverAux_subset_coverUniverse
    (n := n) (F := F) (h := h) (hH := hH) (Rset := (∅ : Finset (Subcube n)))
  have hsubset : (∅ : Finset (Subcube n)) ⊆ coverUniverse (n := n) F := by
    intro R hR; cases hR
  have := haux hsubset
  simpa [buildCover] using this

/-- The catalogue contains at most `2^n` rectangles. -/
lemma coverUniverse_card_le (F : Family n) :
    (coverUniverse (n := n) F).card ≤ 2 ^ n := by
  classical
  have hcard := Finset.card_image_le
    (s := (Finset.univ : Finset (Boolcube.Point n)))
    (f := fun x : Boolcube.Point n =>
      Boolcube.Subcube.fromPoint (n := n) x (supportUnion (n := n) F))
  simpa [coverUniverse] using hcard

/--
The catalogue bound `mBound` dominates the number of rectangles reachable by
the cover construction once the dimension is positive.  This simple lemma
bridges the purely combinatorial catalogue bound `coverUniverse_card_le` with
the arithmetic estimates in `Cover.Bounds`.  Bundling the inequality here keeps
later proofs short and avoids threading the intermediate `2^n` estimate through
multiple files.
-/
lemma coverUniverse_card_le_mBound (F : Family n) (h : ℕ)
    (hn : 0 < n) :
    (coverUniverse (n := n) F).card ≤ mBound n h := by
  have hcat := coverUniverse_card_le (n := n) (F := F)
  have hbound := two_pow_le_mBound (n := n) (h := h) hn
  exact hcat.trans hbound

/-- Quantitative bound: the cover contains at most `2^n` rectangles. -/
lemma buildCover_card_bound (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h hH).card ≤ 2 ^ n := by
  classical
  have hsubset := buildCover_subset_coverUniverse (n := n) (F := F)
    (h := h) (hH := hH)
  have hcard := Finset.card_le_card hsubset
  exact hcard.trans (coverUniverse_card_le (n := n) (F := F))

/--
Combining `coverUniverse_card_le_mBound` with the subset property shows that
the recursion never produces more than `mBound n h` rectangles, provided the
standard entropy guard holds.  This lemma is the canonical source for the
`mBound` bound used throughout the remainder of the development.
-/
lemma buildCover_card_le_mBound (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) (hn : 0 < n) :
    (buildCover (n := n) F h hH).card ≤ mBound n h := by
  classical
  have hsubset := buildCover_subset_coverUniverse (n := n) (F := F)
    (h := h) (hH := hH)
  have hcard := Finset.card_le_card hsubset
  exact hcard.trans
    (coverUniverse_card_le_mBound (n := n) (F := F) (h := h) hn)


end Cover2

