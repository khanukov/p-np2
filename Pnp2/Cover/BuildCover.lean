import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Uncovered
import Pnp2.Cover.Measure
import Pnp2.Cover.Bounds
import Pnp2.low_sensitivity_cover -- for `BoolFunc.coverConst`

/-!
This file supplies the recursive core of the covering construction.  The
original development used a trivial stub for `buildCover` that merely
performed a single call to `extendCover`.  Rewriting the function using a
well‑founded recursion on the measure `μ` avoids difficult termination issues
for the accompanying lemmas.

The actual correctness proofs are substantial and remain works in progress.
We nevertheless expose the intended API so that other parts of the repository
can already rely on the interface.  Lemmas that still await a complete proof
are currently stated as axioms.  They can be filled in once the missing
arguments have been formalised.
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
              -- The first uncovered point is `some _`, so the option is nonempty.
              -- `simp` suffices; no rewrite is required after the computation.
              simp [hfu]
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
                  -- From the assumption that `firstUncovered` returns `some _`.
                  simp [_hfc]
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
        simpa [hrec, hfu] using hR
      -- The measure drops strictly after adding the new rectangle.
      have hdrop : μRel (n := n) (F := F) h
          (extendCover (n := n) F Rset) Rset := by
        have hne : firstUncovered (n := n) F Rset ≠ none := by
          -- Under hypothesis `hfu`, the result is `some _`, hence `≠ none`.
          simp [hfu]
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
  -- We prove the statement by well-founded induction over the measure `μ`.
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
      -- indeed removes at least that point and therefore decreases `μ`.
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
          mu_extendCover_lt (n := n) (F := F) (Rset := Rset) (h := h) hne
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
Quantitative bounds on the size of the cover were previously postulated via an
axiom.  For the purposes of the current development we only require a very
coarse estimate: the number of rectangles produced by `buildCover` can never
exceed the total number of subcubes.  This observation is completely
elementary but removes the remaining axiom and keeps the API usable.  A future
refinement may replace this lemma with a sharper bound that depends on the
entropy budget `h`.
-/
/--
Cardinality bound for the cover constructed by `buildCover`.
The returned set is a finset of subcubes, hence its cardinality is bounded by
the size of the ambient type `Subcube n`.
-/
lemma buildCover_card_bound (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h hH).card ≤ Fintype.card (Subcube n) := by
  classical
  -- `card_le_univ` provides the required inequality for any finite set.
  have hbound :=
    (Finset.card_le_univ (s := buildCover (n := n) F h hH) :
      (buildCover (n := n) F h hH).card ≤ Fintype.card (Subcube n))
  simpa using hbound

end Cover2

