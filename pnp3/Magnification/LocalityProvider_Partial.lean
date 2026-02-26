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
Constructive data package sufficient to build `FormulaCertificateProviderPartial`.

For each extracted formula solver we assume an explicit stabilizing restriction,
plus the numeric side-conditions required by
`Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.ofRestriction`.
-/
structure FormulaRestrictionCertificateDataPartial where
  restrictionData :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let solver := generalSolverOfFormula hFormula
      ∃ (r : Facts.LocalityLift.Restriction
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))),
        r.alive.card ≤
          Facts.LocalityLift.polylogBudget
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
        Facts.LocalityLift.LocalCircuitSmallEnough
          { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
            , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
                * r.alive.card.succ
            , ℓ := r.alive.card
            , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } ∧
        r.alive.card ≤
          Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 ∧
        ∀ x : Facts.LocalityLift.BitVec
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
          ThirdPartyFacts.solverDecideFacts (p := p) solver (r.apply x) =
            ThirdPartyFacts.solverDecideFacts (p := p) solver x

/--
Support-based numeric assumptions sufficient to construct
`FormulaRestrictionCertificateDataPartial` for formula-extracted solvers.

For each strict formula witness at length `partialInputLen p`, we require:
1) polylog bound on syntactic support,
2) `LocalCircuitSmallEnough` for the induced locality parameters,
3) half-table bound on support size.
-/
def FormulaSupportRestrictionBoundsPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    let solver := generalSolverOfFormula hFormula
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    let alive := ComplexityInterfaces.FormulaCircuit.support c
    let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
      Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
    let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
      ThirdPartyFacts.inputLen_toFactsPartial p
    let rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) :=
      ThirdPartyFacts.castRestriction hlen.symm rPartial
    rFacts.alive.card ≤
      Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
      Facts.LocalityLift.LocalCircuitSmallEnough
        { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
          , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
              * rFacts.alive.card.succ
          , ℓ := rFacts.alive.card
          , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } ∧
      rFacts.alive.card ≤
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4

/--
Named closure hook for I-4:
once multi-switching/counting establishes support-based bounds, this theorem is
the exact bridge expected by the magnification interface.
-/
theorem formula_support_bounds_from_multiswitching
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    FormulaSupportRestrictionBoundsPartial :=
  hBounds

/--
Default-flag wrapper for `formula_support_bounds_from_multiswitching`.
-/
theorem hasDefaultFormulaSupportRestrictionBoundsPartial_from_multiswitching
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    Nonempty FormulaSupportRestrictionBoundsPartial :=
  ⟨formula_support_bounds_from_multiswitching hBounds⟩

/--
Constructive support-based builder of `FormulaRestrictionCertificateDataPartial`.
-/
noncomputable def formulaRestrictionCertificateData_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    FormulaRestrictionCertificateDataPartial where
  restrictionData := by
    intro p hFormula
    let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    let alive : Finset (Fin (Models.partialInputLen p)) :=
      ComplexityInterfaces.FormulaCircuit.support c
    let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
      Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
    let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
      ThirdPartyFacts.inputLen_toFactsPartial p
    let rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) :=
      ThirdPartyFacts.castRestriction hlen.symm rPartial
    have hB :
        rFacts.alive.card ≤
          Facts.LocalityLift.polylogBudget
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
          Facts.LocalityLift.LocalCircuitSmallEnough
            { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
              , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
                  * rFacts.alive.card.succ
              , ℓ := rFacts.alive.card
              , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } ∧
          rFacts.alive.card ≤
            Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 := by
      simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using
        hBounds (p := p) hFormula
    have hpoly :
        rFacts.alive.card ≤
          Facts.LocalityLift.polylogBudget
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) := hB.1
    have hsmall :
        Facts.LocalityLift.LocalCircuitSmallEnough
          { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
            , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
                * rFacts.alive.card.succ
            , ℓ := rFacts.alive.card
            , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } := hB.2.1
    have hhalf :
        rFacts.alive.card ≤
          Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 := hB.2.2
    have hstablePartial :
        ∀ x : Core.BitVec (Models.partialInputLen p),
          solver.decide (rPartial.apply x) = solver.decide x := by
      intro x
      change
        ComplexityInterfaces.FormulaCircuit.eval c (rPartial.apply x) =
          ComplexityInterfaces.FormulaCircuit.eval c x
      apply ComplexityInterfaces.FormulaCircuit.eval_eq_of_eq_on_support
      intro i hi
      exact Facts.LocalityLift.Restriction.apply_alive rPartial x hi
    have hstableFacts :
        ∀ x : Facts.LocalityLift.BitVec
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
          ThirdPartyFacts.solverDecideFacts (p := p) solver (rFacts.apply x) =
            ThirdPartyFacts.solverDecideFacts (p := p) solver x := by
      have hstableCast :
          ∀ x0 : Core.BitVec (Models.partialInputLen p),
            ThirdPartyFacts.solverDecideFacts (p := p) solver
                (ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply x0)) =
              ThirdPartyFacts.solverDecideFacts (p := p) solver
                (ThirdPartyFacts.castBitVec hlen.symm x0) := by
        intro x0
        change
          solver.decide
              (ThirdPartyFacts.castBitVec hlen
                (ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply x0))) =
            solver.decide
              (ThirdPartyFacts.castBitVec hlen
                (ThirdPartyFacts.castBitVec hlen.symm x0))
        simpa [ThirdPartyFacts.castBitVec_castBitVec_symm] using hstablePartial x0
      have hstableRaw :=
        ThirdPartyFacts.stable_of_stable_cast
          (h := hlen.symm)
          (decide := ThirdPartyFacts.solverDecideFacts (p := p) solver)
          (r := rPartial)
          hstableCast
      intro x
      simpa [rFacts] using hstableRaw x
    refine ⟨rFacts, ?_, ?_, ?_, hstableFacts⟩
    · exact hpoly
    · exact hsmall
    · exact hhalf

/-- Default-availability flag for restriction-level certificate data. -/
def hasDefaultFormulaRestrictionCertificateDataPartial : Prop :=
  Nonempty FormulaRestrictionCertificateDataPartial

/-- Extract concrete restriction-level data from its default flag. -/
noncomputable def defaultFormulaRestrictionCertificateDataPartial
    (h : hasDefaultFormulaRestrictionCertificateDataPartial) :
    FormulaRestrictionCertificateDataPartial := by
  exact Classical.choice h

/--
Default restriction-level data from support-based numeric assumptions.
-/
theorem hasDefaultFormulaRestrictionCertificateDataPartial_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    hasDefaultFormulaRestrictionCertificateDataPartial :=
  ⟨formulaRestrictionCertificateData_of_supportBounds hBounds⟩

/-- Default support-bounds flag for the support-based restriction route. -/
def hasDefaultFormulaSupportRestrictionBoundsPartial : Prop :=
  Nonempty FormulaSupportRestrictionBoundsPartial

/-- Extract concrete support-based bounds from their default flag. -/
theorem defaultFormulaSupportRestrictionBoundsPartial
    (h : hasDefaultFormulaSupportRestrictionBoundsPartial) :
    FormulaSupportRestrictionBoundsPartial := by
  rcases h with ⟨hB⟩
  exact hB

/--
Default restriction-level data from the default support-bounds flag.
-/
theorem hasDefaultFormulaRestrictionCertificateDataPartial_of_default_supportBounds
    (h : hasDefaultFormulaSupportRestrictionBoundsPartial) :
    hasDefaultFormulaRestrictionCertificateDataPartial :=
  hasDefaultFormulaRestrictionCertificateDataPartial_of_supportBounds
    (defaultFormulaSupportRestrictionBoundsPartial h)

/--
Certificate-first provider data for the fixed extraction
`generalSolverOfFormula`.

This is the I-4 target interface at the magnification boundary: once
multi-switching/depth-induction can construct these certificates for formula
witnesses, the structured locality provider is obtained without half-size
assumptions.
-/
structure FormulaCertificateProviderPartial where
  cert :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
        (ThirdPartyFacts.solverDecideFacts (p := p) solver)

/--
Build a formula-certificate provider from explicit restriction-level data.

This is a constructive bridge:
`restrictionData` gives stability + numeric bounds on the Partial side, and we
transport them to the Facts-side certificate expected by the locality-lift API.
-/
noncomputable def formulaCertificateProvider_of_restrictionData
    (D : FormulaRestrictionCertificateDataPartial) :
    FormulaCertificateProviderPartial where
  cert := by
    intro p hFormula
    let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
    have hData :
        ∃ (r : Facts.LocalityLift.Restriction
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))),
          r.alive.card ≤
            Facts.LocalityLift.polylogBudget
              (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
          Facts.LocalityLift.LocalCircuitSmallEnough
            { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
              , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
                  * r.alive.card.succ
              , ℓ := r.alive.card
              , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } ∧
          r.alive.card ≤
            Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 ∧
          ∀ x : Facts.LocalityLift.BitVec
              (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
            ThirdPartyFacts.solverDecideFacts (p := p) solver (r.apply x) =
              ThirdPartyFacts.solverDecideFacts (p := p) solver x := by
      simpa [solver] using D.restrictionData (p := p) hFormula
    let r : Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) :=
      Classical.choose hData
    have hDataSpec := Classical.choose_spec hData
    have hpoly :
        r.alive.card ≤
          Facts.LocalityLift.polylogBudget
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) :=
      hDataSpec.1
    have hsmall :
        Facts.LocalityLift.LocalCircuitSmallEnough
          { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
            , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
                * r.alive.card.succ
            , ℓ := r.alive.card
            , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } :=
      hDataSpec.2.1
    have hhalf :
        r.alive.card ≤
          Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 :=
      hDataSpec.2.2.1
    have hstable :
        ∀ x : Facts.LocalityLift.BitVec
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
          ThirdPartyFacts.solverDecideFacts (p := p) solver (r.apply x) =
            ThirdPartyFacts.solverDecideFacts (p := p) solver x :=
      hDataSpec.2.2.2
    exact
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.ofRestriction
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (general := ThirdPartyFacts.toFactsGeneralSolverPartial solver)
        (generalEval := ThirdPartyFacts.solverDecideFacts (p := p) solver)
        (restriction := r)
        hpoly
        hsmall
        hhalf
        hstable

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
Build a constructive locality engine from certificate-first provider data.

This route is the intended constructive endpoint after I-4: stability is
extracted from the certificate itself (via
`stableRestriction_of_certificate`), and shrinkage witness provider is derived
from the same certificate.
-/
noncomputable def constructiveLocalityEnginePartial_of_formulaCertificate
    (hCert : FormulaCertificateProviderPartial) :
    ConstructiveLocalityEnginePartial where
  generalOfFormula := by
    intro p hFormula
    exact generalSolverOfFormula hFormula
  stable := by
    intro p hFormula
    let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
    let cert :
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
        (ThirdPartyFacts.solverDecideFacts (p := p) solver) :=
      hCert.cert hFormula
    letI :
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
        (ThirdPartyFacts.solverDecideFacts (p := p) solver) := ⟨cert⟩
    have hHalf :
        (Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
            (p := ThirdPartyFacts.toFactsParamsPartial p)
            (general := ThirdPartyFacts.toFactsGeneralSolverPartial solver)
            (generalEval := ThirdPartyFacts.solverDecideFacts (p := p) solver)).restriction.alive.card
          ≤ Models.Partial.tableLen p.n / 2 :=
      (inferInstance :
        ThirdPartyFacts.HalfTableCertificateBound (p := p) solver).half_bound
    have hStable :=
      ThirdPartyFacts.stableRestriction_of_certificate
        (p := p) solver hHalf
    simpa [solver] using hStable
  provider := by
    intro p hFormula
    let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
    let cert :
      Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
        (ThirdPartyFacts.solverDecideFacts (p := p) solver) :=
      hCert.cert hFormula
    change Facts.LocalityLift.ShrinkageWitness.Provider
      (p := ThirdPartyFacts.toFactsParamsPartial p)
      (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
    exact ⟨cert.toShrinkageWitness⟩

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
Direct structured-provider constructor from an explicit formula-certificate
provider package.
-/
theorem structuredLocalityProviderPartial_of_formulaCertificate
    (hCert : FormulaCertificateProviderPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_engine
    (constructiveLocalityEnginePartial_of_formulaCertificate hCert)

/--
Direct structured-provider constructor from explicit restriction-level
certificate data.
-/
theorem structuredLocalityProviderPartial_of_restrictionData
    (D : FormulaRestrictionCertificateDataPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_formulaCertificate
    (formulaCertificateProvider_of_restrictionData D)

/--
Direct structured-provider constructor from support-based numeric assumptions.
-/
theorem structuredLocalityProviderPartial_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_restrictionData
    (formulaRestrictionCertificateData_of_supportBounds hBounds)

/--
I-2 direct closure contract: explicit certificate-first data sufficient to
construct a structured locality provider without default `Nonempty` wrappers.
-/
structure DirectStructuredLocalityProviderContract where
  certificateProvider : FormulaCertificateProviderPartial

/-- Build a structured locality provider from the direct I-2 contract. -/
theorem structuredLocalityProviderPartial_of_contract
    (h : DirectStructuredLocalityProviderContract) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_formulaCertificate h.certificateProvider

/--
Build the direct I-2 contract from explicit restriction-level certificate data.
-/
noncomputable def directStructuredLocalityProviderContract_of_restrictionData
    (D : FormulaRestrictionCertificateDataPartial) :
    DirectStructuredLocalityProviderContract :=
  ⟨formulaCertificateProvider_of_restrictionData D⟩

/--
Build the direct I-2 contract from support-based numeric assumptions.
-/
noncomputable def directStructuredLocalityProviderContract_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    DirectStructuredLocalityProviderContract :=
  directStructuredLocalityProviderContract_of_restrictionData
    (formulaRestrictionCertificateData_of_supportBounds hBounds)

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

/-- Default-engine flag from a certificate-first provider package. -/
theorem hasDefaultStructuredLocalityProviderPartial_of_formulaCertificate
    (hCert : FormulaCertificateProviderPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  ⟨constructiveLocalityEnginePartial_of_formulaCertificate hCert⟩

/-- Default-availability flag for a formula-certificate provider package. -/
def hasDefaultFormulaCertificateProviderPartial : Prop :=
  Nonempty FormulaCertificateProviderPartial

/-- Extract a concrete formula-certificate provider from its default flag. -/
noncomputable def defaultFormulaCertificateProviderPartial
    (h : hasDefaultFormulaCertificateProviderPartial) :
    FormulaCertificateProviderPartial := by
  exact Classical.choice h

/--
Any explicit restriction-level certificate data package yields a default
formula-certificate provider.
-/
theorem hasDefaultFormulaCertificateProviderPartial_of_restrictionData
    (D : FormulaRestrictionCertificateDataPartial) :
    hasDefaultFormulaCertificateProviderPartial :=
  ⟨formulaCertificateProvider_of_restrictionData D⟩

/--
Default formula-certificate provider from default restriction-level data.
-/
theorem hasDefaultFormulaCertificateProviderPartial_of_default_restrictionData
    (h : hasDefaultFormulaRestrictionCertificateDataPartial) :
    hasDefaultFormulaCertificateProviderPartial :=
  hasDefaultFormulaCertificateProviderPartial_of_restrictionData
    (defaultFormulaRestrictionCertificateDataPartial h)

/--
Default formula-certificate provider from support-based numeric assumptions.
-/
theorem hasDefaultFormulaCertificateProviderPartial_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    hasDefaultFormulaCertificateProviderPartial :=
  hasDefaultFormulaCertificateProviderPartial_of_restrictionData
    (formulaRestrictionCertificateData_of_supportBounds hBounds)

/--
Default formula-certificate provider from default support-based assumptions.
-/
theorem hasDefaultFormulaCertificateProviderPartial_of_default_supportBounds
    (h : hasDefaultFormulaSupportRestrictionBoundsPartial) :
    hasDefaultFormulaCertificateProviderPartial :=
  hasDefaultFormulaCertificateProviderPartial_of_default_restrictionData
    (hasDefaultFormulaRestrictionCertificateDataPartial_of_default_supportBounds h)

/--
Default structured-provider flag from the default formula-certificate
provider flag.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_default_formulaCertificate
    (h : hasDefaultFormulaCertificateProviderPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_formulaCertificate
    (defaultFormulaCertificateProviderPartial h)

/--
Default structured-provider flag from explicit restriction-level
certificate data.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_restrictionData
    (D : FormulaRestrictionCertificateDataPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_default_formulaCertificate
    (hasDefaultFormulaCertificateProviderPartial_of_restrictionData D)

/--
Default structured-provider flag from default restriction-level certificate data.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_default_restrictionData
    (h : hasDefaultFormulaRestrictionCertificateDataPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_default_formulaCertificate
    (hasDefaultFormulaCertificateProviderPartial_of_default_restrictionData h)

/--
Default structured-provider flag from support-based numeric assumptions.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_default_formulaCertificate
    (hasDefaultFormulaCertificateProviderPartial_of_supportBounds hBounds)

/--
Default structured-provider flag from default support-based assumptions.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_default_supportBounds
    (h : hasDefaultFormulaSupportRestrictionBoundsPartial) :
    hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_default_formulaCertificate
    (hasDefaultFormulaCertificateProviderPartial_of_default_supportBounds h)

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
