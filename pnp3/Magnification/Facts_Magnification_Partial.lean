import Models.Model_PartialMCSP
import LowerBounds.LB_GeneralFromLocal_Partial
import Magnification.LocalityInterfaces_Partial
import Magnification.LocalityLift_Partial
import Magnification.PipelineStatements_Partial
import Complexity.Interfaces

/-!
  pnp3/Magnification/Facts_Magnification_Partial.lean

  Partial‑версия OPS‑триггеров для формульного (AC⁰) трека.

  Мы копируем минимальную конструктивную часть из legacy‑файла, но теперь
  работаем с языком `gapPartialMCSP_Language` и partial‑оболочками решателей.
-/

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ComplexityInterfaces

/-!
  ### General lower‑bound hypothesis (partial)
-/

def GeneralLowerBoundHypothesisPartial
    (_p : GapPartialMCSPParams) (ε : Rat) (statement : Prop) : Prop :=
  (0 : Rat) < ε ∧ statement

/-!
  ### P/poly → general solver (partial)
-/

noncomputable def generalCircuitSolver_of_Ppoly_partial
    (p : GapPartialMCSPParams)
    (h : ComplexityInterfaces.Ppoly (gapPartialMCSP_Language p)) :
    SmallGeneralCircuitSolver_Partial p := by
  classical
  let w : Facts.PsubsetPpoly.Complexity.InPpoly (gapPartialMCSP_Language p) :=
    Classical.choice h
  refine
    { params :=
        { params :=
            { n := Models.partialInputLen p
              size := w.polyBound (Models.partialInputLen p)
              depth := 1 }
          same_n := rfl }
      decide := w.circuits (Models.partialInputLen p)
      correct := by
        refine And.intro ?yes ?no
        · intro x hx
          have hLang : w.circuits (Models.partialInputLen p) x =
              gapPartialMCSP_Language p (Models.partialInputLen p) x :=
            w.correct _ _
          simpa [hLang] using hx
        · intro x hx
          have hLang : w.circuits (Models.partialInputLen p) x =
              gapPartialMCSP_Language p (Models.partialInputLen p) x :=
            w.correct _ _
          have hNo : gapPartialMCSP_Language p (Models.partialInputLen p) x = false := hx
          simp [hLang, hNo] }

/-!
  ### OPS trigger (partial, formulas)
-/

/--
  Realized variant of the general OPS trigger.
-/
theorem OPS_trigger_general_contra_partial_realized
  {p : GapPartialMCSPParams} {ε : Rat} (statement : Prop)
  (hLocalized : LowerBounds.LocalizedFamilyWitnessHypothesis_partial_realized p) :
  GeneralLowerBoundHypothesisPartial p ε statement →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) := by
  intro hHyp hAll
  have hPpoly : ComplexityInterfaces.Ppoly (gapPartialMCSP_Language p) :=
    hAll _ (Models.gapPartialMCSP_in_NP p)
  let solver : SmallGeneralCircuitSolver_Partial p :=
    generalCircuitSolver_of_Ppoly_partial (p := p) hPpoly
  let solverR : RealizedSmallGeneralCircuitSolver_Partial p :=
    { base := solver
      impl := Models.Circuit.ofFunction (Models.partialInputLen p) solver.decide
      decide_eq_impl := by
        intro x
        simpa using (Models.Circuit.eval_ofFunction solver.decide x).symm }
  exact
    LowerBounds.LB_GeneralFromLocal_partial_realized
      (p := p) (solver := solverR) hLocalized

/--
  Realized variant of the formulas OPS trigger.
-/
theorem OPS_trigger_formulas_contra_partial_realized
  {p : GapPartialMCSPParams} {δ : Rat}
  (hLocalized : LowerBounds.LocalizedFamilyWitnessHypothesis_partial_realized p) :
  FormulaLowerBoundHypothesisPartial p δ →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) := by
  intro hHyp hAll
  have hGeneral :
      GeneralLowerBoundHypothesisPartial p δ
        (AC0BoundedStatementPartial p δ) := by
    simpa [FormulaLowerBoundHypothesisPartial, GeneralLowerBoundHypothesisPartial] using hHyp
  exact OPS_trigger_general_contra_partial_realized (p := p) (ε := δ)
    (statement := AC0BoundedStatementPartial p δ)
    hLocalized hGeneral hAll

/--
  Realized variant of `OPS_trigger_formulas_partial`.
-/
theorem OPS_trigger_formulas_partial_realized
  {p : GapPartialMCSPParams} {δ : Rat}
  (hLocalized : LowerBounds.LocalizedFamilyWitnessHypothesis_partial_realized p) :
  FormulaLowerBoundHypothesisPartial p δ → NP_not_subset_Ppoly := by
  intro hHyp
  have hContra :=
    OPS_trigger_formulas_contra_partial_realized
      (p := p) (δ := δ) hLocalized hHyp
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

end Magnification
end Pnp3
