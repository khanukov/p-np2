import Models.Model_PartialMCSP
import LowerBounds.LB_GeneralFromLocal_Partial
import Magnification.LocalityInterfaces_Partial
import Magnification.LocalityLift_Partial
import Magnification.PipelineStatements_Partial
import Complexity.Interfaces
import ThirdPartyFacts.PpolyFormula

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
    Classical.choose h
  let N := Models.partialInputLen p
  -- Extract locality from the P/poly hypothesis via ppoly_circuit_locality
  let localityWitness :=
    ThirdPartyFacts.ppoly_circuit_locality
      (gapPartialMCSP_Language p) h N
  let alive := Classical.choose localityWitness
  have h_spec := Classical.choose_spec localityWitness
  let h_card : alive.card ≤ N / 4 := h_spec.1
  let h_local := h_spec.2
  exact
    { params :=
        { params :=
            { n := N
              size := w.polyBound N
              depth := 1 }
          same_n := rfl }
      decide := w.circuits N
      correct := by
        refine And.intro ?yes ?no
        · intro x hx
          have hLang : w.circuits N x =
              gapPartialMCSP_Language p N x :=
            w.correct _ _
          simpa [hLang] using hx
        · intro x hx
          have hLang : w.circuits N x =
              gapPartialMCSP_Language p N x :=
            w.correct _ _
          have hNo : gapPartialMCSP_Language p N x = false := hx
          simp [hLang, hNo]
      decideLocal := by
        refine ⟨alive, h_card, ?_⟩
        intro x y h_agree
        -- Transfer locality from the language to w.circuits
        have hx_eq : w.circuits N x = gapPartialMCSP_Language p N x :=
          w.correct N x
        have hy_eq : w.circuits N y = gapPartialMCSP_Language p N y :=
          w.correct N y
        rw [hx_eq, hy_eq]
        exact h_local x y h_agree }

/-!
  ### OPS trigger (partial, formulas)
-/

theorem OPS_trigger_general_contra_partial
  {p : GapPartialMCSPParams} {ε : Rat} (statement : Prop) :
  GeneralLowerBoundHypothesisPartial p ε statement →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) := by
  intro hHyp hAll
  have hPpoly : ComplexityInterfaces.Ppoly (gapPartialMCSP_Language p) :=
    hAll _ (Models.gapPartialMCSP_in_NP p)
  have solver : SmallGeneralCircuitSolver_Partial p :=
    generalCircuitSolver_of_Ppoly_partial (p := p) hPpoly
  exact LowerBounds.LB_GeneralFromLocal_partial (p := p) (solver := solver)

theorem OPS_trigger_formulas_contra_partial
  {p : GapPartialMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) := by
  intro hHyp hAll
  have hGeneral :
      GeneralLowerBoundHypothesisPartial p δ
        (AC0BoundedStatementPartial p δ) := by
    simpa [FormulaLowerBoundHypothesisPartial, GeneralLowerBoundHypothesisPartial] using hHyp
  exact OPS_trigger_general_contra_partial (p := p) (ε := δ)
    (statement := AC0BoundedStatementPartial p δ)
    hGeneral hAll

theorem OPS_trigger_formulas_partial
  {p : GapPartialMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ → NP_not_subset_Ppoly := by
  intro hHyp
  have hContra := OPS_trigger_formulas_contra_partial (p := p) (δ := δ) hHyp
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

end Magnification
end Pnp3
