import Magnification.Facts_Magnification_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces
import Mathlib.Tactic

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ComplexityInterfaces

/-- Any strict formula has syntactic size at least `1`. -/
private lemma formula_size_pos {n : Nat} (c : ComplexityInterfaces.FormulaCircuit n) :
    1 ≤ ComplexityInterfaces.FormulaCircuit.size c := by
  induction c with
  | const _ =>
      simp [ComplexityInterfaces.FormulaCircuit.size]
  | input _ =>
      simp [ComplexityInterfaces.FormulaCircuit.size]
  | not c ih =>
      exact Nat.succ_le_succ (Nat.zero_le _)
  | and c₁ c₂ ih₁ ih₂ =>
      exact Nat.succ_le_succ (Nat.zero_le _)
  | or c₁ c₂ ih₁ ih₂ =>
      exact Nat.succ_le_succ (Nat.zero_le _)

/--
Fixed-slice formula collapse:
for a fixed parameter package `p`, any `PpolyFormula` witness for
`gapPartialMCSP_Language p` yields a contradiction, provided we have the
structured locality provider and the Step-C lower-bound hypothesis.
-/
theorem fixed_formula_collapse_of_provider
    (hProvider : StructuredLocalityProviderPartial)
    {p : GapPartialMCSPParams} {δ : Rat}
    (hHyp : FormulaLowerBoundHypothesisPartial p δ) :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) → False := by
  intro hFormula
  obtain ⟨_T, loc, _hT, _hℓ⟩ := hProvider p δ hHyp hFormula
  exact noSmallLocalCircuitSolver_partial_v2 loc

/--
Asymptotic collapse through an explicit slice bridge.

This theorem isolates the exact remaining bridge obligation used by the current
route: turning an asymptotic formula witness into a fixed-slice one.
-/
theorem asymptotic_formula_collapse_of_slice_bridge
    (spec : GapPartialMCSPAsymptoticSpec)
    (p : GapPartialMCSPParams)
    (hCollapseFixed :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) → False)
    (hSliceBridge :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) →
        ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False := by
  intro hAsymFormula
  exact hCollapseFixed (hSliceBridge hAsymFormula)

/--
Constructive asymptotic-to-fixed bridge from pointwise slice agreement at the
target length `partialInputLen p`.
-/
theorem ppolyFormula_fixed_of_asymptotic_slice
    (spec : GapPartialMCSPAsymptoticSpec)
    (p : GapPartialMCSPParams)
    (hSliceEq :
      ∀ x : Core.BitVec (partialInputLen p),
        gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
          gapPartialMCSP_Language p (partialInputLen p) x) :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) := by
  intro hAsym
  rcases hAsym with ⟨w, _⟩
  refine ⟨{
    polyBound := w.polyBound
    polyBound_poly := w.polyBound_poly
    family := fun m =>
      if hm : m = partialInputLen p then
        w.family m
      else
        ComplexityInterfaces.FormulaCircuit.const false
    family_size_le := ?_
    correct := ?_
  }, trivial⟩
  · intro m
    by_cases hm : m = partialInputLen p
    · simpa [hm] using w.family_size_le m
    · simp [hm]
      exact le_trans (formula_size_pos (w.family m)) (w.family_size_le m)
  · intro m x
    by_cases hm : m = partialInputLen p
    · cases hm
      have hAsymCorrect :
          ComplexityInterfaces.FormulaCircuit.eval
              (w.family (partialInputLen p)) x =
            gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x :=
        w.correct (partialInputLen p) x
      have hEq :
          gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
            gapPartialMCSP_Language p (partialInputLen p) x :=
        hSliceEq x
      simpa using Eq.trans hAsymCorrect hEq
    · simp [hm, ComplexityInterfaces.FormulaCircuit.eval, gapPartialMCSP_Language]

/--
Asymptotic collapse from fixed-slice collapse plus explicit slice agreement.
-/
theorem asymptotic_formula_collapse_of_slice_agreement
    (spec : GapPartialMCSPAsymptoticSpec)
    (p : GapPartialMCSPParams)
    (hCollapseFixed :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) → False)
    (hSliceEq :
      ∀ x : Core.BitVec (partialInputLen p),
        gapPartialMCSP_AsymptoticLanguage spec (partialInputLen p) x =
          gapPartialMCSP_Language p (partialInputLen p) x) :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False := by
  apply asymptotic_formula_collapse_of_slice_bridge (spec := spec) (p := p) hCollapseFixed
  exact ppolyFormula_fixed_of_asymptotic_slice (spec := spec) (p := p) hSliceEq

/--
Convenient strict-NP to canonical separation wrapper from fixed-slice collapse.
-/
theorem NP_not_subset_PpolyFormula_of_fixed_formula_collapse
    {p : GapPartialMCSPParams}
    (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
    (hCollapse : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) → False) :
    ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hContra :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP_strict L → ComplexityInterfaces.PpolyFormula L) → False := by
    intro hAll
    exact hCollapse (hAll (gapPartialMCSP_Language p) hNPstrict)
  exact
    ComplexityInterfaces.NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula
      (ComplexityInterfaces.NP_strict_not_subset_PpolyFormula_of_contra hContra)

/--
Convenient strict-NP to canonical separation wrapper from asymptotic collapse.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse
    (spec : GapPartialMCSPAsymptoticSpec)
    (hNPstrict : ComplexityInterfaces.NP_strict
      (gapPartialMCSP_AsymptoticLanguage spec))
    (hCollapse :
      ComplexityInterfaces.PpolyFormula
        (gapPartialMCSP_AsymptoticLanguage spec) → False) :
    ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hContra :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP_strict L → ComplexityInterfaces.PpolyFormula L) → False := by
    intro hAll
    exact hCollapse (hAll (gapPartialMCSP_AsymptoticLanguage spec) hNPstrict)
  exact
    ComplexityInterfaces.NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula
      (ComplexityInterfaces.NP_strict_not_subset_PpolyFormula_of_contra hContra)

end Magnification
end Pnp3
