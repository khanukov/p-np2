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

def LanguageLocalityPartial (p : GapPartialMCSPParams) : Prop :=
  ∃ (alive : Finset (Fin (Models.partialInputLen p))),
    alive.card ≤ Models.partialInputLen p / 4 ∧
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      (∀ i ∈ alive, x i = y i) →
        gapPartialMCSP_Language p (Models.partialInputLen p) x =
        gapPartialMCSP_Language p (Models.partialInputLen p) y

def StructuredLocalityProviderPartial : Prop :=
  ∀ (p : GapPartialMCSPParams),
    ComplexityInterfaces.PpolyStructured (gapPartialMCSP_Language p) →
      LanguageLocalityPartial p

def StructuredFamilyLocalityPartial
    (p : GapPartialMCSPParams)
    (w : Facts.PsubsetPpoly.Complexity.InPpolyStructured.{0}
      (gapPartialMCSP_Language p)) : Prop :=
  ∃ (alive : Finset (Fin (Models.partialInputLen p))),
    alive.card ≤ Models.partialInputLen p / 4 ∧
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      (∀ i ∈ alive, x i = y i) →
        w.eval (Models.partialInputLen p) (w.family (Models.partialInputLen p)) x =
        w.eval (Models.partialInputLen p) (w.family (Models.partialInputLen p)) y

theorem language_locality_of_structuredFamilyLocality
    (p : GapPartialMCSPParams)
    (w : Facts.PsubsetPpoly.Complexity.InPpolyStructured.{0}
      (gapPartialMCSP_Language p))
    (hLocal : StructuredFamilyLocalityPartial p w) :
    ∃ (alive : Finset (Fin (Models.partialInputLen p))),
      alive.card ≤ Models.partialInputLen p / 4 ∧
      ∀ x y : Core.BitVec (Models.partialInputLen p),
        (∀ i ∈ alive, x i = y i) →
          gapPartialMCSP_Language p (Models.partialInputLen p) x =
          gapPartialMCSP_Language p (Models.partialInputLen p) y := by
  rcases hLocal with ⟨alive, h_card, h_loc_w⟩
  refine ⟨alive, h_card, ?_⟩
  intro x y h_agree
  have hx : w.eval (Models.partialInputLen p) (w.family (Models.partialInputLen p)) x =
      gapPartialMCSP_Language p (Models.partialInputLen p) x := w.correct _ _
  have hy : w.eval (Models.partialInputLen p) (w.family (Models.partialInputLen p)) y =
      gapPartialMCSP_Language p (Models.partialInputLen p) y := w.correct _ _
  have hxy := h_loc_w x y h_agree
  simpa [hx, hy] using hxy

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

/--
Structured-interface variant of `generalCircuitSolver_of_Ppoly_partial`.
Core constructor parameterized by an explicit locality hypothesis for the
language itself.  This keeps the proof path independent of how locality was
obtained (axiom, imported theorem, or future internal proof).
-/
noncomputable def generalCircuitSolver_of_PpolyStructured_partial_of_locality
    (p : GapPartialMCSPParams)
    (h : ComplexityInterfaces.PpolyStructured (gapPartialMCSP_Language p)) :
    LanguageLocalityPartial p →
    SmallGeneralCircuitSolver_Partial p := by
  intro hLocalityLang
  classical
  let w : Facts.PsubsetPpoly.Complexity.InPpolyStructured.{0}
      (gapPartialMCSP_Language p) := Classical.choose h
  let N := Models.partialInputLen p
  let alive := Classical.choose hLocalityLang
  have h_spec := Classical.choose_spec hLocalityLang
  let h_card : alive.card ≤ N / 4 := h_spec.1
  let h_local := h_spec.2
  exact
    { params :=
        { params :=
            { n := N
              size := w.polyBound N
              depth := 1 }
          same_n := rfl }
      decide := fun x => w.eval N (w.family N) x
      correct := by
        refine And.intro ?yes ?no
        · intro x hx
          have hLang :
              w.eval N (w.family N) x = gapPartialMCSP_Language p N x :=
            w.correct _ _
          simpa [hLang] using hx
        · intro x hx
          have hLang :
              w.eval N (w.family N) x = gapPartialMCSP_Language p N x :=
            w.correct _ _
          have hNo : gapPartialMCSP_Language p N x = false := hx
          simp [hLang, hNo]
      decideLocal := by
        refine ⟨alive, h_card, ?_⟩
        intro x y h_agree
        have hx_eq : w.eval N (w.family N) x = gapPartialMCSP_Language p N x :=
          w.correct N x
        have hy_eq : w.eval N (w.family N) y = gapPartialMCSP_Language p N y :=
          w.correct N y
        rw [hx_eq, hy_eq]
        exact h_local x y h_agree }

/--
Direct constructor from a concrete structured witness and its own locality
statement.  This is the closest non-axiomatic entry point for future
carrier-specific locality theorems.
-/
noncomputable def generalCircuitSolver_of_structuredWitness_partial
    (p : GapPartialMCSPParams)
    (w : Facts.PsubsetPpoly.Complexity.InPpolyStructured.{0}
      (gapPartialMCSP_Language p))
    (hLocal : StructuredFamilyLocalityPartial p w) :
    SmallGeneralCircuitSolver_Partial p :=
  generalCircuitSolver_of_PpolyStructured_partial_of_locality
    (p := p)
    (h := ⟨w, trivial⟩)
    (language_locality_of_structuredFamilyLocality (p := p) (w := w) hLocal)

/--
Structured-interface variant of `generalCircuitSolver_of_Ppoly_partial`.
Currently instantiated from the external locality axiom, but now factored
through `generalCircuitSolver_of_PpolyStructured_partial_of_locality`.
-/
noncomputable def generalCircuitSolver_of_PpolyStructured_partial
    (p : GapPartialMCSPParams)
    (h : ComplexityInterfaces.PpolyStructured (gapPartialMCSP_Language p)) :
    SmallGeneralCircuitSolver_Partial p :=
  generalCircuitSolver_of_PpolyStructured_partial_of_locality
    (p := p) (h := h)
    (ThirdPartyFacts.ppolyStructured_circuit_locality
      (gapPartialMCSP_Language p) h (Models.partialInputLen p))

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

/--
Structured-interface variant of the OPS contradiction trigger.
This keeps the downstream conclusion unchanged (`NP_not_subset_Ppoly`), while
allowing upstream hypotheses to be phrased via `PpolyStructured`.
-/
theorem OPS_trigger_general_contra_structured_partial
  {p : GapPartialMCSPParams} {ε : Rat} (statement : Prop) :
  GeneralLowerBoundHypothesisPartial p ε statement →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L) → False) := by
  intro hHyp hAll
  have hPpolyStructured :
      ComplexityInterfaces.PpolyStructured (gapPartialMCSP_Language p) :=
    hAll _ (Models.gapPartialMCSP_in_NP p)
  have solver : SmallGeneralCircuitSolver_Partial p :=
    generalCircuitSolver_of_PpolyStructured_partial (p := p) hPpolyStructured
  exact LowerBounds.LB_GeneralFromLocal_partial (p := p) (solver := solver)

theorem OPS_trigger_general_contra_structured_with_provider_partial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {ε : Rat} (statement : Prop) :
  GeneralLowerBoundHypothesisPartial p ε statement →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L) → False) := by
  intro hHyp hAll
  have hPpolyStructured :
      ComplexityInterfaces.PpolyStructured (gapPartialMCSP_Language p) :=
    hAll _ (Models.gapPartialMCSP_in_NP p)
  have hLocality : LanguageLocalityPartial p :=
    hProvider p hPpolyStructured
  have solver : SmallGeneralCircuitSolver_Partial p :=
    generalCircuitSolver_of_PpolyStructured_partial_of_locality
      (p := p) (h := hPpolyStructured) hLocality
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

theorem OPS_trigger_formulas_contra_structured_partial
  {p : GapPartialMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L) → False) := by
  intro hHyp hAll
  have hGeneral :
      GeneralLowerBoundHypothesisPartial p δ
        (AC0BoundedStatementPartial p δ) := by
    simpa [FormulaLowerBoundHypothesisPartial, GeneralLowerBoundHypothesisPartial] using hHyp
  exact OPS_trigger_general_contra_structured_partial (p := p) (ε := δ)
    (statement := AC0BoundedStatementPartial p δ)
    hGeneral hAll

theorem OPS_trigger_formulas_contra_structured_with_provider_partial
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L) → False) := by
  intro hHyp hAll
  have hGeneral :
      GeneralLowerBoundHypothesisPartial p δ
        (AC0BoundedStatementPartial p δ) := by
    simpa [FormulaLowerBoundHypothesisPartial, GeneralLowerBoundHypothesisPartial] using hHyp
  exact OPS_trigger_general_contra_structured_with_provider_partial
    (hProvider := hProvider) (p := p) (ε := δ)
    (statement := AC0BoundedStatementPartial p δ)
    hGeneral hAll

theorem OPS_trigger_formulas_partial
  {p : GapPartialMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ → NP_not_subset_Ppoly := by
  intro hHyp
  have hContra := OPS_trigger_formulas_contra_partial (p := p) (δ := δ) hHyp
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

theorem OPS_trigger_formulas_partial_of_structured_contra
  {p : GapPartialMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ →
    NP_not_subset_Ppoly := by
  intro hHyp
  have hContraStructured :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L) → False :=
    OPS_trigger_formulas_contra_structured_partial (p := p) (δ := δ) hHyp
  have hContra :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False := by
    intro hAll
    have hAllStructured :
        ∀ L : ComplexityInterfaces.Language,
          ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L := by
      intro L hNP
      exact ComplexityInterfaces.PpolyStructured_of_Ppoly (hAll L hNP)
    exact hContraStructured hAllStructured
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

theorem OPS_trigger_formulas_partial_of_provider
  (hProvider : StructuredLocalityProviderPartial)
  {p : GapPartialMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesisPartial p δ →
    NP_not_subset_Ppoly := by
  intro hHyp
  have hContraStructured :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L) → False :=
    OPS_trigger_formulas_contra_structured_with_provider_partial
      (hProvider := hProvider) (p := p) (δ := δ) hHyp
  have hContra :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False := by
    intro hAll
    have hAllStructured :
        ∀ L : ComplexityInterfaces.Language,
          ComplexityInterfaces.NP L → ComplexityInterfaces.PpolyStructured L := by
      intro L hNP
      exact ComplexityInterfaces.PpolyStructured_of_Ppoly (hAll L hNP)
    exact hContraStructured hAllStructured
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

end Magnification
end Pnp3
