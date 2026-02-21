import Magnification.Facts_Magnification_Partial
import Magnification.LocalityLift_Partial
import ThirdPartyFacts.PartialLocalityLift

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/--
Constructive extraction of a general solver from a strict formula witness for
`gapPartialMCSP_Language p`.
-/
noncomputable def generalSolverOfFormula
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    SmallGeneralCircuitSolver_Partial p := by
  classical
  let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
    Classical.choose hFormula
  refine
    { params :=
        { params :=
            { n := Models.partialInputLen p
              size :=
                ComplexityInterfaces.FormulaCircuit.size
                  (wf.family (Models.partialInputLen p))
              depth := 0 }
          same_n := rfl }
      sem := ComplexityInterfaces.SemanticDecider.ofFunction (Models.partialInputLen p)
      witness := fun x =>
        ComplexityInterfaces.FormulaCircuit.eval
          (wf.family (Models.partialInputLen p)) x
      correct := ?_ }
  refine (Models.solvesPromise_gapPartialMCSP_iff (p := p)).2 ?_
  intro x
  simpa using wf.correct (Models.partialInputLen p) x

/--
Stable-restriction witness from an explicit support-cardinality bound for the
formula extracted at length `partialInputLen p`.
-/
theorem stableWitness_of_formula_supportBound
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (hSupport :
      (ComplexityInterfaces.FormulaCircuit.support
        ((Classical.choose hFormula).family (Models.partialInputLen p))).card
        ≤ Models.Partial.tableLen p.n / 2) :
    let solver := generalSolverOfFormula hFormula
    ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
      r.alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x := by
  classical
  let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
    Classical.choose hFormula
  let c := wf.family (Models.partialInputLen p)
  let alive : Finset (Fin (Models.partialInputLen p)) :=
    ComplexityInterfaces.FormulaCircuit.support c
  let r : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
  refine ⟨r, ?_, ?_⟩
  · simpa [r, alive, c] using hSupport
  · intro x
    change
      ComplexityInterfaces.FormulaCircuit.eval c (r.apply x) =
        ComplexityInterfaces.FormulaCircuit.eval c x
    apply ComplexityInterfaces.FormulaCircuit.eval_eq_of_eq_on_support
    intro i hi
    exact Facts.LocalityLift.Restriction.apply_alive r x hi

/--
Stable-restriction witness from a size bound for the extracted formula.
-/
theorem stableWitness_of_formula_sizeBound
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (hSize :
      ComplexityInterfaces.FormulaCircuit.size
        ((Classical.choose hFormula).family (Models.partialInputLen p))
        ≤ Models.Partial.tableLen p.n / 2) :
    let solver := generalSolverOfFormula hFormula
    ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
      r.alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x := by
  classical
  let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
    Classical.choose hFormula
  let c := wf.family (Models.partialInputLen p)
  have hSupport :
      (ComplexityInterfaces.FormulaCircuit.support c).card ≤
        Models.Partial.tableLen p.n / 2 := by
    exact le_trans (ComplexityInterfaces.FormulaCircuit.support_card_le_size c) hSize
  simpa [c, wf] using stableWitness_of_formula_supportBound (p := p) hFormula hSupport

/--
Constructive engine for deriving a structured locality provider from
`PpolyFormula` witnesses of `gapPartialMCSP_Language`.

This packages the three ingredients required by `locality_lift_partial`:
1) extraction of a general solver from a formula witness,
2) stability under some restriction of half-table alive size,
3) a shrinkage provider for the extracted general solver.
-/
structure ConstructiveLocalityEnginePartial where
  generalOfFormula :
    ∀ {p : GapPartialMCSPParams},
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) →
        SmallGeneralCircuitSolver_Partial p
  stable :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let solver := generalOfFormula hFormula
      ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
        r.alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
        ∀ x : Core.BitVec (Models.partialInputLen p),
          solver.decide (r.apply x) = solver.decide x
  provider :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let solver := generalOfFormula hFormula
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver)

/--
Data bundle for the remaining locality ingredients after formula-to-general
solver extraction is fixed to `generalSolverOfFormula`.
-/
structure FormulaToGeneralLocalityDataPartial where
  stable :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let solver := generalSolverOfFormula hFormula
      ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
        r.alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
        ∀ x : Core.BitVec (Models.partialInputLen p),
          solver.decide (r.apply x) = solver.decide x

/--
Uniform half-size condition for extracted strict formula witnesses at the
target length `partialInputLen p`.

Research status:
this is currently an explicit assumption interface, not an internal theorem.
Deriving it from existing in-repo lemmas is open; see
`pnp3/Docs/RESEARCH_BLOCKER_FormulaHalfSizeBoundPartial.md`.
-/
def FormulaHalfSizeBoundPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    ComplexityInterfaces.FormulaCircuit.size
      ((Classical.choose hFormula).family (Models.partialInputLen p))
      ≤ Models.Partial.tableLen p.n / 2

/--
Default-availability flag for the uniform half-size condition.
-/
def hasDefaultFormulaHalfSizeBoundPartial : Prop :=
  Nonempty FormulaHalfSizeBoundPartial

/-- Extract a concrete half-size witness from its default flag. -/
theorem defaultFormulaHalfSizeBoundPartial
    (h : hasDefaultFormulaHalfSizeBoundPartial) :
    FormulaHalfSizeBoundPartial := by
  rcases h with ⟨hHalf⟩
  exact hHalf

/--
Direct `stable` witness under the uniform half-size assumption.
-/
theorem stableWitness_of_formula_halfSize
    (hHalf : FormulaHalfSizeBoundPartial)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let solver := generalSolverOfFormula hFormula
    ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
      r.alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x := by
  simpa [generalSolverOfFormula] using
    stableWitness_of_formula_sizeBound (p := p) hFormula (hHalf hFormula)

/--
Build the remaining locality data from the uniform half-size condition.
-/
noncomputable def formulaToGeneralLocalityData_of_halfSize
    (hHalf : FormulaHalfSizeBoundPartial) :
    FormulaToGeneralLocalityDataPartial where
  stable := by
    intro p hFormula
    simpa [generalSolverOfFormula] using
      stableWitness_of_formula_halfSize (hHalf := hHalf) (p := p) hFormula

/--
Build a constructive locality engine from the fixed formula-to-general
extraction and explicit locality/shrinkage data.
-/
noncomputable def constructiveLocalityEnginePartial_of_formulaData
    (D : FormulaToGeneralLocalityDataPartial) :
    ConstructiveLocalityEnginePartial where
  generalOfFormula := by
    intro p hFormula
    exact generalSolverOfFormula hFormula
  stable := by
    intro p hFormula
    simpa [generalSolverOfFormula] using D.stable hFormula
  provider := by
    intro p hFormula
    let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
    change Facts.LocalityLift.ShrinkageWitness.Provider
      (p := ThirdPartyFacts.toFactsParamsPartial p)
      (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
    refine ⟨Facts.LocalityLift.ShrinkageWitness.canonical
      (general := ThirdPartyFacts.toFactsGeneralSolverPartial solver)⟩

/--
Any constructive locality engine yields the structured locality provider
required by the magnification bridge.
-/
theorem structuredLocalityProviderPartial_of_engine
    (E : ConstructiveLocalityEnginePartial) :
    StructuredLocalityProviderPartial := by
  intro p δ hHyp hFormula
  let solver : SmallGeneralCircuitSolver_Partial p := E.generalOfFormula hFormula
  have hStable :
      ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
        r.alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
        ∀ x : Core.BitVec (Models.partialInputLen p),
          solver.decide (r.apply x) = solver.decide x := by
    simpa [solver] using E.stable hFormula
  have hProvider :
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver) := by
    simpa [solver] using E.provider hFormula
  obtain ⟨T, loc, hT, hM, hℓ, hDepth⟩ :=
    locality_lift_partial (p := p) (solver := solver) hStable hProvider
  exact ⟨T, loc, hT, hℓ⟩

/--
Default-availability flag for a constructive locality engine.
-/
def hasDefaultStructuredLocalityProviderPartial : Prop :=
  Nonempty ConstructiveLocalityEnginePartial

/-- Any explicit constructive engine provides the default-engine flag. -/
theorem hasDefaultStructuredLocalityProviderPartial_of_engine
    (E : ConstructiveLocalityEnginePartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  ⟨E⟩

/--
Any explicit formula-locality data package yields the default-engine flag.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_formulaData
    (D : FormulaToGeneralLocalityDataPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  ⟨constructiveLocalityEnginePartial_of_formulaData D⟩

/--
Default-engine flag from a uniform half-size condition.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_halfSize
    (hHalf : FormulaHalfSizeBoundPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_formulaData
    (formulaToGeneralLocalityData_of_halfSize hHalf)

/--
Default structured provider from the default half-size flag.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_default_halfSize
    (hHalf : hasDefaultFormulaHalfSizeBoundPartial) :
    hasDefaultStructuredLocalityProviderPartial := by
  exact
    hasDefaultStructuredLocalityProviderPartial_of_halfSize
      (defaultFormulaHalfSizeBoundPartial hHalf)

/-- Extract a structured locality provider from the default engine flag. -/
theorem defaultStructuredLocalityProviderPartial
    (h : hasDefaultStructuredLocalityProviderPartial) :
    StructuredLocalityProviderPartial := by
  rcases h with ⟨E⟩
  exact structuredLocalityProviderPartial_of_engine E

end Magnification
end Pnp3
