import Models.Model_PartialMCSP
import LowerBounds.AntiChecker_Partial
import Magnification.PipelineStatements_Partial
import Complexity.Interfaces

/-!
  pnp3/Magnification/Facts_Magnification_Partial.lean

  Partial‑версия OPS‑триггеров для формульного (AC⁰) трека.

  В этой версии мы используем restriction-style witness:
  provider возвращает не «глобальную junta-локальность языка», а
  локальный решатель вместе с polylog-тестсетом и числовыми bounds.
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

/--
Restriction-style locality witness used by the partial magnification bridge.

It packages:
* a polylog test set `T`,
* a local solver `loc` for the partial GapMCSP promise,
* numerical bounds matching the locality-lift shape.
-/
def RestrictionLocalityPartial (p : GapPartialMCSPParams) : Prop :=
  ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
    (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
      T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
      loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p)

/--
Structured provider: from a strict structured `P/poly` witness for
`gapPartialMCSP_Language p` we can extract a restriction-locality witness.
-/
def StructuredLocalityProviderPartial : Prop :=
  ∀ (p : GapPartialMCSPParams) (δ : Rat),
    FormulaLowerBoundHypothesisPartial p δ →
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) →
      RestrictionLocalityPartial p

/-!
  ### OPS trigger (partial, formulas)
-/

theorem OPS_trigger_general_contra_structured_with_provider_partial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat} :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  FormulaLowerBoundHypothesisPartial p δ →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP_strict L → ComplexityInterfaces.PpolyFormula L) → False) := by
  intro hNPstrict hHyp hAll
  have hPpolyFormula :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
    hAll _ hNPstrict
  obtain ⟨T, loc, hT, hℓ⟩ := hProvider p δ hHyp hPpolyFormula
  exact noSmallLocalCircuitSolver_partial_v2 loc

theorem OPS_trigger_formulas_contra_structured_with_provider_partial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat} :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  FormulaLowerBoundHypothesisPartial p δ →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP_strict L → ComplexityInterfaces.PpolyFormula L) → False) := by
  intro hNPstrict hHyp hAll
  exact OPS_trigger_general_contra_structured_with_provider_partial
    (hProvider := hProvider) (hNPstrict := hNPstrict) (p := p) (δ := δ) hHyp hAll

theorem OPS_trigger_formulas_partial_of_provider
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams}
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hGapEmbed :
    ComplexityInterfaces.PpolyReal (gapPartialMCSP_Language p) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
  {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ →
    NP_not_subset_PpolyReal := by
  intro hHyp
  have hContra :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP_strict L → ComplexityInterfaces.PpolyReal L) → False := by
    intro hAll
    have hPpoly : ComplexityInterfaces.PpolyReal (gapPartialMCSP_Language p) :=
      hAll _ hNPstrict
    have hPpolyFormula :
        ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
      hGapEmbed hPpoly
    obtain ⟨T, loc, hT, hℓ⟩ := hProvider p δ hHyp hPpolyFormula
    exact noSmallLocalCircuitSolver_partial_v2 loc
  exact ComplexityInterfaces.NP_not_subset_PpolyReal_of_NP_strict_not_subset_PpolyReal
    (ComplexityInterfaces.NP_strict_not_subset_PpolyReal_of_contra hContra)

theorem OPS_trigger_formulas_partial_of_provider_global_embed
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat} :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  (hEmbed : ∀ L : ComplexityInterfaces.Language,
    ComplexityInterfaces.PpolyReal L → ComplexityInterfaces.PpolyFormula L) →
  FormulaLowerBoundHypothesisPartial p δ →
    NP_not_subset_PpolyReal := by
  intro hNPstrict hEmbed
  exact OPS_trigger_formulas_partial_of_provider
    (hProvider := hProvider)
    (hNPstrict := hNPstrict)
    (p := p)
    (hGapEmbed := hEmbed (gapPartialMCSP_Language p))

theorem OPS_trigger_formulas_partial_of_provider_formula_separation
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat} :
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) →
  FormulaLowerBoundHypothesisPartial p δ →
    ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPstrict hHyp
  have hContraStructured :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP_strict L → ComplexityInterfaces.PpolyFormula L) → False :=
    OPS_trigger_formulas_contra_structured_with_provider_partial
      (hProvider := hProvider) (hNPstrict := hNPstrict) (p := p) (δ := δ) hHyp
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula
    (ComplexityInterfaces.NP_strict_not_subset_PpolyFormula_of_contra hContraStructured)

/--
TM-strict counterpart of the formula-track trigger.

This variant avoids the lightweight `NP` interface in the contra step and
works directly with `NP_strict = NP_TM`, provided by an explicit witness for
the target language.
-/
theorem OPS_trigger_formulas_partial_of_provider_formula_separation_strict
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat}
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
  FormulaLowerBoundHypothesisPartial p δ →
    ComplexityInterfaces.NP_strict_not_subset_PpolyFormula := by
  intro hHyp
  have hContraStructured :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP_strict L → ComplexityInterfaces.PpolyFormula L) → False := by
    intro hAll
    have hPpolyFormula :
        ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
      hAll _ hNPstrict
    obtain ⟨T, loc, hT, hℓ⟩ := hProvider p δ hHyp hPpolyFormula
    exact noSmallLocalCircuitSolver_partial_v2 loc
  exact ComplexityInterfaces.NP_strict_not_subset_PpolyFormula_of_contra hContraStructured

end Magnification
end Pnp3
