import Magnification.Facts_Magnification_Partial
import Magnification.LocalityLift_Partial
import Magnification.AC0LocalityBridge
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
Extracted local-core payload for one strict formula witness.

This object intentionally avoids committing to `support c` of the raw witness:
it stores directly the restriction object used by the locality route.
-/
structure ExtractedLocalCorePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  rFacts :
    Facts.LocalityLift.Restriction
      (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  supportBridge :
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
    rFacts = ThirdPartyFacts.castRestriction hlen.symm rPartial
  polylogAlive :
    rFacts.alive.card ≤
      Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  smallEnough :
    Facts.LocalityLift.LocalCircuitSmallEnough
      { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfFormula hFormula)).params.size * rFacts.alive.card.succ
        , ℓ := rFacts.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfFormula hFormula)).params.depth }
  quarterAlive :
    rFacts.alive.card ≤
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4

/--
Provider-style interface for extracted local cores: for each strict formula
witness, produce one local-core payload.
-/
def FormulaExtractedLocalCoreProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (ExtractedLocalCorePartial hFormula)

/--
Generic extracted local-core object (no canonical-support bridge).
-/
structure GenericExtractedLocalCorePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  rFacts :
    Facts.LocalityLift.Restriction
      (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  polylogAlive :
    rFacts.alive.card ≤
      Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  smallEnough :
    Facts.LocalityLift.LocalCircuitSmallEnough
      { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfFormula hFormula)).params.size * rFacts.alive.card.succ
        , ℓ := rFacts.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfFormula hFormula)).params.depth }
  quarterAlive :
    rFacts.alive.card ≤
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4
  stableFacts :
    ∀ x : Facts.LocalityLift.BitVec
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
      ThirdPartyFacts.solverDecideFacts (p := p) (generalSolverOfFormula hFormula)
        (rFacts.apply x) =
        ThirdPartyFacts.solverDecideFacts (p := p) (generalSolverOfFormula hFormula) x

/--
Provider interface for generic extracted local cores.
-/
def FormulaGenericExtractedLocalCoreProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (GenericExtractedLocalCorePartial hFormula)

/--
Weakened generic extracted local core: keeps only the numeric/locality data and
does not carry any semantic `stableFacts` field.
-/
structure WeakGenericExtractedLocalCorePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  rFacts :
    Facts.LocalityLift.Restriction
      (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  polylogAlive :
    rFacts.alive.card ≤
      Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  smallEnough :
    Facts.LocalityLift.LocalCircuitSmallEnough
      { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfFormula hFormula)).params.size * rFacts.alive.card.succ
        , ℓ := rFacts.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
            (generalSolverOfFormula hFormula)).params.depth }
  quarterAlive :
    rFacts.alive.card ≤
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4

/-- Provider interface for weakened generic extracted local cores. -/
def FormulaWeakGenericExtractedLocalCoreProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (WeakGenericExtractedLocalCorePartial hFormula)

namespace WeakGenericExtractedLocalCorePartial

/-- Forget the semantic `stableFacts` payload of the stronger generic core. -/
def ofGeneric
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (core : GenericExtractedLocalCorePartial hFormula) :
    WeakGenericExtractedLocalCorePartial hFormula where
  rFacts := core.rFacts
  polylogAlive := core.polylogAlive
  smallEnough := core.smallEnough
  quarterAlive := core.quarterAlive

end WeakGenericExtractedLocalCorePartial

/-- Any strong generic-core provider yields a weak generic-core provider. -/
theorem weakGenericExtractedLocalCoreProvider_of_generic
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial) :
    FormulaWeakGenericExtractedLocalCoreProviderPartial := by
  intro p hFormula
  rcases hCore (p := p) hFormula with ⟨core⟩
  exact ⟨WeakGenericExtractedLocalCorePartial.ofGeneric core⟩

/--
Source-layer frontier after the mid-layer cleanup:
from one semantic switching certificate, extract some restriction object
carrying the numeric locality bounds needed by the weak-core route.

This contract is intentionally phrased using existence of `rFacts`, without any
support-based canonicality requirement.
-/
def SemanticSwitchingRestrictionCoreExtractionPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (_cert : AC0LocalityBridge.SemanticSwitchingCertificatePartial hFormula),
    ∃ rFacts :
        Facts.LocalityLift.Restriction
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
      rFacts.alive.card ≤
        Facts.LocalityLift.polylogBudget
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
      Facts.LocalityLift.LocalCircuitSmallEnough
        { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
          , M := (ThirdPartyFacts.toFactsGeneralSolverPartial
              (generalSolverOfFormula hFormula)).params.size * rFacts.alive.card.succ
          , ℓ := rFacts.alive.card
          , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial
              (generalSolverOfFormula hFormula)).params.depth } ∧
      rFacts.alive.card ≤
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4

/--
Turn one semantic switching certificate plus a restriction-extraction contract
into one weak extracted local core.
-/
theorem weakGenericExtractedLocalCore_of_semantic_switching_certificate_and_extraction
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (cert : AC0LocalityBridge.SemanticSwitchingCertificatePartial hFormula)
    (hExtract : SemanticSwitchingRestrictionCoreExtractionPartial) :
    Nonempty (WeakGenericExtractedLocalCorePartial hFormula) := by
  rcases hExtract cert with ⟨rFacts, hPoly, hSmall, hQuarter⟩
  exact ⟨{
    rFacts := rFacts
    polylogAlive := hPoly
    smallEnough := hSmall
    quarterAlive := hQuarter
  }⟩

/--
Provider-level bridge from the new source-side certificate layer to the weak
generic extracted-core interface.
-/
theorem weakGenericExtractedLocalCoreProvider_of_semantic_switching_certificate_provider_and_extraction
    (hCert :
      AC0LocalityBridge.SemanticSwitchingCertificateProviderPartial)
    (hExtract : SemanticSwitchingRestrictionCoreExtractionPartial) :
    FormulaWeakGenericExtractedLocalCoreProviderPartial := by
  intro p hFormula
  rcases hCert (p := p) hFormula with ⟨cert⟩
  exact weakGenericExtractedLocalCore_of_semantic_switching_certificate_and_extraction
    cert hExtract

/--
Direct source-layer entry point:
semantic multi-switching provider + restriction extraction for its certificate
yield a weak extracted-core provider.
-/
theorem weakGenericExtractedLocalCoreProvider_of_semantic_provider_and_extraction
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
    (hExtract : SemanticSwitchingRestrictionCoreExtractionPartial) :
    FormulaWeakGenericExtractedLocalCoreProviderPartial := by
  exact
    weakGenericExtractedLocalCoreProvider_of_semantic_switching_certificate_provider_and_extraction
      (AC0LocalityBridge.semanticSwitchingCertificateProvider_of_provider hSem)
      hExtract

/--
Restricted local solver for the behavior of the extracted general solver after
applying a specific restriction `rFacts`.

This is intentionally weaker than `SmallLocalCircuitSolver_Partial`: it carries
local-circuit parameters, locality, and agreement with the *restricted*
behavior, but does not claim global correctness for the original promise
language.
-/
structure RestrictedLocalBehaviorSolver_Partial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))) where
  T : Finset (Core.BitVec (Models.partialInputLen p))
  params : LowerBounds.SmallLocalCircuitParamsPartial p
  sem : ComplexityInterfaces.SemanticDecider (Models.partialInputLen p)
  witness : sem.Carrier
  testSetPolylog :
    T.card ≤ Models.polylogBudget (Models.partialInputLen p)
  localityPolylog :
    params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p)
  restrictedCorrect :
    ∀ x : Facts.LocalityLift.BitVec
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
      sem.eval witness
          (ThirdPartyFacts.castBitVec (ThirdPartyFacts.inputLen_toFactsPartial p) x) =
        ThirdPartyFacts.solverDecideFacts (p := p) (generalSolverOfFormula hFormula)
          (rFacts.apply x)
  decideLocal :
    ∃ (alive : Finset (Fin (Models.partialInputLen p))),
      alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
      ∀ x y : Core.BitVec (Models.partialInputLen p),
        (∀ i ∈ alive, x i = y i) →
          sem.eval witness x = sem.eval witness y

/-- Evaluator induced by the semantic witness of a restricted local solver. -/
@[simp] def RestrictedLocalBehaviorSolver_Partial.decide
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    {rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))}
    (solver : RestrictedLocalBehaviorSolver_Partial hFormula rFacts) :
    Core.BitVec (Models.partialInputLen p) → Bool :=
  fun x => solver.sem.eval solver.witness x

/-- Convenience view of `decideLocal` through `solver.decide`. -/
lemma RestrictedLocalBehaviorSolver_Partial.decideLocal_decide
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    {rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))}
    (solver : RestrictedLocalBehaviorSolver_Partial hFormula rFacts) :
    ∃ (alive : Finset (Fin (Models.partialInputLen p))),
      alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
      ∀ x y : Core.BitVec (Models.partialInputLen p),
        (∀ i ∈ alive, x i = y i) →
          solver.decide x = solver.decide y := by
  rcases solver.decideLocal with ⟨alive, hcard, hloc⟩
  refine ⟨alive, hcard, ?_⟩
  intro x y hxy
  simpa [RestrictedLocalBehaviorSolver_Partial.decide] using hloc x y hxy

/--
Upgrade a restricted-behavior local solver to a global `SmallLocalCircuitSolver`
once correctness for the original promise language has been provided
separately.
-/
def RestrictedLocalBehaviorSolver_Partial.toSmallLocalCircuitSolver_Partial
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    {rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))}
    (solver : RestrictedLocalBehaviorSolver_Partial hFormula rFacts)
    (hCorrect : Complexity.SolvesPromise (Models.GapPartialMCSPPromise p) solver.decide) :
    LowerBounds.SmallLocalCircuitSolver_Partial p :=
  { params := solver.params
    sem := solver.sem
    witness := solver.witness
    correct := by
      simpa [RestrictedLocalBehaviorSolver_Partial.decide] using hCorrect
    decideLocal := solver.decideLocal }

/--
Generic restriction-aware behavior certificate: an extracted core plus a local
solver for the corresponding restricted behavior.
-/
structure GenericRestrictedBehaviorCertificatePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  core : GenericExtractedLocalCorePartial hFormula
  rloc : RestrictedLocalBehaviorSolver_Partial hFormula core.rFacts

/--
Provider interface for restricted-behavior certificates.
-/
def FormulaGenericRestrictedBehaviorProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (GenericRestrictedBehaviorCertificatePartial hFormula)

/--
Weak restriction-aware behavior certificate: same downstream payload, but based
on the weakened generic core without `stableFacts`.
-/
structure WeakGenericRestrictedBehaviorCertificatePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  core : WeakGenericExtractedLocalCorePartial hFormula
  rloc : RestrictedLocalBehaviorSolver_Partial hFormula core.rFacts

/-- Provider interface for weak restricted-behavior certificates. -/
def FormulaWeakGenericRestrictedBehaviorProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (WeakGenericRestrictedBehaviorCertificatePartial hFormula)

/--
Next theorem target for the switching route: from a generic extracted core,
produce a local solver for the *restricted* behavior only.
-/
def GenericRestrictedLocalBehaviorTransportPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (core : GenericExtractedLocalCorePartial hFormula),
    Nonempty (RestrictedLocalBehaviorSolver_Partial hFormula core.rFacts)

/--
Weak transport target: same restricted-behavior solver, but starting only from
the weak generic extracted core.
-/
def WeakGenericRestrictedLocalBehaviorTransportPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (core : WeakGenericExtractedLocalCorePartial hFormula),
    Nonempty (RestrictedLocalBehaviorSolver_Partial hFormula core.rFacts)

/--
Separate globalization step: once a restricted-behavior local solver is known,
this contract asks only for correctness with respect to the original promise
language.
-/
def GlobalizeRestrictedLocalBehaviorPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    {core : GenericExtractedLocalCorePartial hFormula},
    (rloc : RestrictedLocalBehaviorSolver_Partial hFormula core.rFacts) →
      Complexity.SolvesPromise (Models.GapPartialMCSPPromise p) rloc.decide

/--
Weak globalization contract: the same promise correctness target, but for the
weakened generic extracted core.

Compatibility layer only: the provenance-aware weak-core route below avoids
requiring a theorem that quantifies over all weak cores.
-/
def WeakGlobalizeRestrictedLocalBehaviorPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    {core : WeakGenericExtractedLocalCorePartial hFormula},
    (rloc : RestrictedLocalBehaviorSolver_Partial hFormula core.rFacts) →
      Complexity.SolvesPromise (Models.GapPartialMCSPPromise p) rloc.decide

/--
Weak semantic preservation contract needed for globalization.

It asks only that, on inputs lying in the promise partition, the extracted
restriction does not change the decision of the formula-derived general solver.
This is strictly weaker than the old global `stableFacts` condition.
-/
def RestrictedBehaviorDecisionPreservationOnPromisePartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (core : GenericExtractedLocalCorePartial hFormula)
    (x : Core.BitVec (Models.partialInputLen p)),
      x ∈ (Models.GapPartialMCSPPromise p).Yes ∨
        x ∈ (Models.GapPartialMCSPPromise p).No →
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfFormula hFormula)
          (core.rFacts.apply
            (ThirdPartyFacts.castBitVec
              (ThirdPartyFacts.inputLen_toFactsPartial p).symm x))
      =
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfFormula hFormula)
          (ThirdPartyFacts.castBitVec
            (ThirdPartyFacts.inputLen_toFactsPartial p).symm x)

/--
Weak semantic preservation contract on the promise partition for the weakened
generic extracted core.

Compatibility layer only: the real frontier should be phrased via a
provenance-aware weak-core provider rather than as a global theorem about all
weak cores.
-/
def WeakRestrictedBehaviorDecisionPreservationOnPromisePartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (core : WeakGenericExtractedLocalCorePartial hFormula)
    (x : Core.BitVec (Models.partialInputLen p)),
      x ∈ (Models.GapPartialMCSPPromise p).Yes ∨
        x ∈ (Models.GapPartialMCSPPromise p).No →
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfFormula hFormula)
          (core.rFacts.apply
            (ThirdPartyFacts.castBitVec
              (ThirdPartyFacts.inputLen_toFactsPartial p).symm x))
      =
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfFormula hFormula)
          (ThirdPartyFacts.castBitVec
            (ThirdPartyFacts.inputLen_toFactsPartial p).symm x)

/--
Provenance-aware weak core: the extracted weak restriction is bundled together
with the promise-preservation fact that is actually needed downstream.
-/
structure PromisePreservingWeakGenericExtractedLocalCorePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  core : WeakGenericExtractedLocalCorePartial hFormula
  preserveOnPromise :
    ∀ x : Core.BitVec (Models.partialInputLen p),
      x ∈ (Models.GapPartialMCSPPromise p).Yes ∨
        x ∈ (Models.GapPartialMCSPPromise p).No →
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfFormula hFormula)
          (core.rFacts.apply
            (ThirdPartyFacts.castBitVec
              (ThirdPartyFacts.inputLen_toFactsPartial p).symm x))
      =
      ThirdPartyFacts.solverDecideFacts
          (p := p) (generalSolverOfFormula hFormula)
          (ThirdPartyFacts.castBitVec
            (ThirdPartyFacts.inputLen_toFactsPartial p).symm x)

/--
Provider interface for provenance-aware weak cores.
-/
def FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (PromisePreservingWeakGenericExtractedLocalCorePartial hFormula)

namespace PromisePreservingWeakGenericExtractedLocalCorePartial

/--
Any strong generic core yields a provenance-aware weak core: `stableFacts`
implies preservation on the promise partition.
-/
def ofGeneric
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (core : GenericExtractedLocalCorePartial hFormula) :
    PromisePreservingWeakGenericExtractedLocalCorePartial hFormula where
  core := WeakGenericExtractedLocalCorePartial.ofGeneric core
  preserveOnPromise := by
    intro x _hxPromise
    exact core.stableFacts
      (ThirdPartyFacts.castBitVec (ThirdPartyFacts.inputLen_toFactsPartial p).symm x)

/--
Package an externally supplied weak-preservation theorem with a weak core.
-/
def ofWeakCoreAndPreservation
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (core : WeakGenericExtractedLocalCorePartial hFormula)
    (hPres :
      ∀ x : Core.BitVec (Models.partialInputLen p),
        x ∈ (Models.GapPartialMCSPPromise p).Yes ∨
          x ∈ (Models.GapPartialMCSPPromise p).No →
        ThirdPartyFacts.solverDecideFacts
            (p := p) (generalSolverOfFormula hFormula)
            (core.rFacts.apply
              (ThirdPartyFacts.castBitVec
                (ThirdPartyFacts.inputLen_toFactsPartial p).symm x))
        =
        ThirdPartyFacts.solverDecideFacts
            (p := p) (generalSolverOfFormula hFormula)
            (ThirdPartyFacts.castBitVec
              (ThirdPartyFacts.inputLen_toFactsPartial p).symm x)) :
    PromisePreservingWeakGenericExtractedLocalCorePartial hFormula where
  core := core
  preserveOnPromise := hPres

end PromisePreservingWeakGenericExtractedLocalCorePartial

/--
Any strong generic-core provider yields a provenance-aware weak-core provider.
-/
theorem promisePreservingWeakGenericExtractedLocalCoreProvider_of_generic
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial) :
    FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial := by
  intro p hFormula
  rcases hCore (p := p) hFormula with ⟨core⟩
  exact ⟨PromisePreservingWeakGenericExtractedLocalCorePartial.ofGeneric core⟩

/--
An externally supplied weak preservation theorem can be bundled with a weak-core
provider to obtain a provenance-aware weak-core provider.
-/
theorem promisePreservingWeakGenericExtractedLocalCoreProvider_of_weak_provider_and_preservation
    (hCore : FormulaWeakGenericExtractedLocalCoreProviderPartial)
    (hPres : WeakRestrictedBehaviorDecisionPreservationOnPromisePartial) :
    FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial := by
  intro p hFormula
  rcases hCore (p := p) hFormula with ⟨core⟩
  exact ⟨
    PromisePreservingWeakGenericExtractedLocalCorePartial.ofWeakCoreAndPreservation
      core (hPres (p := p) (hFormula := hFormula) core)⟩

/--
Assemble the new restricted-behavior provider from:
1) a generic extracted-core provider, and
2) the restricted-behavior transport theorem.
-/
noncomputable def
    genericRestrictedBehaviorProvider_of_generic_extracted_local_core_provider_and_transport
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial)
    (hTransport : GenericRestrictedLocalBehaviorTransportPartial) :
    FormulaGenericRestrictedBehaviorProviderPartial := by
  intro p hFormula
  rcases hCore (p := p) hFormula with ⟨core⟩
  rcases hTransport (p := p) hFormula core with ⟨rloc⟩
  exact ⟨{ core := core, rloc := rloc }⟩

/--
Assemble the weak restricted-behavior provider from:
1) a weak generic extracted-core provider, and
2) the restricted-behavior transport theorem for that weak core.
-/
noncomputable def
    weakGenericRestrictedBehaviorProvider_of_weak_generic_extracted_local_core_provider_and_transport
    (hCore : FormulaWeakGenericExtractedLocalCoreProviderPartial)
    (hTransport : WeakGenericRestrictedLocalBehaviorTransportPartial) :
    FormulaWeakGenericRestrictedBehaviorProviderPartial := by
  intro p hFormula
  rcases hCore (p := p) hFormula with ⟨core⟩
  rcases hTransport (p := p) hFormula core with ⟨rloc⟩
  exact ⟨{ core := core, rloc := rloc }⟩

/--
Canonical semantic model for the restricted behavior induced by `rFacts`.
-/
noncomputable def restrictedBehaviorSem
    {p : GapPartialMCSPParams}
    (_hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (_rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))) :
    ComplexityInterfaces.SemanticDecider (Models.partialInputLen p) :=
  ComplexityInterfaces.SemanticDecider.ofFunction (Models.partialInputLen p)

/--
Canonical witness for `restrictedBehaviorSem`: evaluate the extracted general
solver after first applying the restriction `rFacts`.
-/
noncomputable def restrictedBehaviorWitness
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (rFacts :
      Facts.LocalityLift.Restriction
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))) :
    (restrictedBehaviorSem hFormula rFacts).Carrier :=
  fun y =>
    ThirdPartyFacts.solverDecideFacts (p := p) (generalSolverOfFormula hFormula)
      (rFacts.apply
        (ThirdPartyFacts.castBitVec (ThirdPartyFacts.inputLen_toFactsPartial p).symm y))

/--
The restricted-behavior transport is already derivable from the extracted core:
no AC0/multi-switching input is needed at this stage.
-/
theorem genericRestrictedLocalBehaviorTransport_of_core :
    GenericRestrictedLocalBehaviorTransportPartial := by
  intro p hFormula core
  classical
  let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    ThirdPartyFacts.castRestriction hlen core.rFacts
  let params : LowerBounds.SmallLocalCircuitParamsPartial p :=
    { params :=
        { n := Models.partialInputLen p
          M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size *
            core.rFacts.alive.card.succ
          ℓ := core.rFacts.alive.card
          depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth }
      same_n := rfl
      small := by
        simpa [solver, ThirdPartyFacts.LocalCircuitSmallEnough] using core.smallEnough }
  refine ⟨
    { T := ∅
      params := params
      sem := restrictedBehaviorSem hFormula core.rFacts
      witness := restrictedBehaviorWitness hFormula core.rFacts
      testSetPolylog := by simp [Models.polylogBudget]
      localityPolylog := by
        simpa [params, solver, ThirdPartyFacts.polylogBudget_toFactsPartial] using
          core.polylogAlive
      restrictedCorrect := ?_
      decideLocal := ?_ }⟩
  · intro x
    simp [restrictedBehaviorSem,
      restrictedBehaviorWitness, ThirdPartyFacts.castBitVec_symm_castBitVec]
  · refine ⟨rPartial.alive, ?_, ?_⟩
    · have hquarter :
          rPartial.alive.card ≤ Models.partialInputLen p / 4 := by
        simpa [rPartial, hlen] using core.quarterAlive
      exact ThirdPartyFacts.quarterAlive_to_decideLocal_bound (p := p) hquarter
    · intro x y hxy
      have happly :
          rPartial.apply x = rPartial.apply y := by
        exact Facts.LocalityLift.Restriction.apply_eq_of_eq_on_alive rPartial hxy
      have happlyFacts :
          core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x) =
            core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm y) := by
        have hcast :
            ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply x) =
              ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply y) :=
          congrArg (ThirdPartyFacts.castBitVec hlen.symm) happly
        simpa [rPartial, ThirdPartyFacts.castRestriction_apply_castBitVec] using hcast
      have hdec :
          ThirdPartyFacts.solverDecideFacts (p := p) solver
            (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) =
          ThirdPartyFacts.solverDecideFacts (p := p) solver
            (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm y)) := by
        exact congrArg (ThirdPartyFacts.solverDecideFacts (p := p) solver) happlyFacts
      simpa [RestrictedLocalBehaviorSolver_Partial.decide, restrictedBehaviorSem,
        restrictedBehaviorWitness] using hdec

/--
The same restricted-behavior transport is derivable from the weakened generic
extracted core: no semantic field is used in the construction.
-/
theorem genericRestrictedLocalBehaviorTransport_of_weak_core :
    WeakGenericRestrictedLocalBehaviorTransportPartial := by
  intro p hFormula core
  classical
  let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
    ThirdPartyFacts.castRestriction hlen core.rFacts
  let params : LowerBounds.SmallLocalCircuitParamsPartial p :=
    { params :=
        { n := Models.partialInputLen p
          M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size *
            core.rFacts.alive.card.succ
          ℓ := core.rFacts.alive.card
          depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth }
      same_n := rfl
      small := by
        simpa [solver, ThirdPartyFacts.LocalCircuitSmallEnough] using core.smallEnough }
  refine ⟨
    { T := ∅
      params := params
      sem := restrictedBehaviorSem hFormula core.rFacts
      witness := restrictedBehaviorWitness hFormula core.rFacts
      testSetPolylog := by simp [Models.polylogBudget]
      localityPolylog := by
        simpa [params, solver, ThirdPartyFacts.polylogBudget_toFactsPartial] using
          core.polylogAlive
      restrictedCorrect := ?_
      decideLocal := ?_ }⟩
  · intro x
    simp [restrictedBehaviorSem,
      restrictedBehaviorWitness, ThirdPartyFacts.castBitVec_symm_castBitVec]
  · refine ⟨rPartial.alive, ?_, ?_⟩
    · have hquarter :
          rPartial.alive.card ≤ Models.partialInputLen p / 4 := by
        simpa [rPartial, hlen] using core.quarterAlive
      exact ThirdPartyFacts.quarterAlive_to_decideLocal_bound (p := p) hquarter
    · intro x y hxy
      have happly :
          rPartial.apply x = rPartial.apply y := by
        exact Facts.LocalityLift.Restriction.apply_eq_of_eq_on_alive rPartial hxy
      have happlyFacts :
          core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x) =
            core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm y) := by
        have hcast :
            ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply x) =
              ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply y) :=
          congrArg (ThirdPartyFacts.castBitVec hlen.symm) happly
        simpa [rPartial, ThirdPartyFacts.castRestriction_apply_castBitVec] using hcast
      have hdec :
          ThirdPartyFacts.solverDecideFacts (p := p) solver
            (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) =
          ThirdPartyFacts.solverDecideFacts (p := p) solver
            (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm y)) := by
        exact congrArg (ThirdPartyFacts.solverDecideFacts (p := p) solver) happlyFacts
      simpa [RestrictedLocalBehaviorSolver_Partial.decide, restrictedBehaviorSem,
        restrictedBehaviorWitness] using hdec

/--
Globalization follows from restricted-behavior agreement together with
decision preservation on the promise partition.
-/
theorem globalization_of_decision_preservation_on_promise
    (hPres : RestrictedBehaviorDecisionPreservationOnPromisePartial) :
    GlobalizeRestrictedLocalBehaviorPartial := by
  intro p hFormula core rloc
  refine (Models.solvesPromise_gapPartialMCSP_iff (p := p)).2 ?_
  intro x
  let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  have hRestricted :
      rloc.decide x =
        ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) := by
    simpa [RestrictedLocalBehaviorSolver_Partial.decide, restrictedBehaviorSem,
      restrictedBehaviorWitness, solver, hlen,
      ThirdPartyFacts.castBitVec_castBitVec_symm] using
      rloc.restrictedCorrect (x := ThirdPartyFacts.castBitVec hlen.symm x)
  have hPromise :
      x ∈ (Models.GapPartialMCSPPromise p).Yes ∨
        x ∈ (Models.GapPartialMCSPPromise p).No := by
    cases hlang : Models.gapPartialMCSP_Language p (Models.partialInputLen p) x
    · right
      simpa [Models.GapPartialMCSPPromise, hlang]
    · left
      simpa [Models.GapPartialMCSPPromise, hlang]
  have hPreserve :
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x))
      =
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (ThirdPartyFacts.castBitVec hlen.symm x) :=
    hPres (p := p) (hFormula := hFormula) core x hPromise
  have hCorrect :
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (ThirdPartyFacts.castBitVec hlen.symm x)
      =
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := by
    have hsolver :
        solver.decide x =
          Models.gapPartialMCSP_Language p (Models.partialInputLen p) x :=
      (Models.solvesPromise_gapPartialMCSP_iff (p := p)).1 solver.correct_decide x
    simpa [solver, ThirdPartyFacts.solverDecideFacts, hlen,
      ThirdPartyFacts.castBitVec_castBitVec_symm] using hsolver
  calc
    rloc.decide x =
      ThirdPartyFacts.solverDecideFacts
        (p := p) solver
        (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) := hRestricted
    _ =
      ThirdPartyFacts.solverDecideFacts
        (p := p) solver
        (ThirdPartyFacts.castBitVec hlen.symm x) := hPreserve
    _ = Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := hCorrect

/--
Probe wrapper: once decision preservation on the promise partition is supplied,
globalization is immediate.
-/
theorem globalization_probe_of_decision_preservation
    (hPres : RestrictedBehaviorDecisionPreservationOnPromisePartial) :
    GlobalizeRestrictedLocalBehaviorPartial :=
  globalization_of_decision_preservation_on_promise hPres

/--
The current generic extracted-core interface is still semantically stronger than
the new weak preservation contract: its `stableFacts` field already implies
decision preservation on the promise partition.
-/
theorem restrictedBehaviorDecisionPreservationOnPromise_of_generic_extracted_local_core :
    RestrictedBehaviorDecisionPreservationOnPromisePartial := by
  intro p hFormula core x _hxPromise
  exact core.stableFacts
    (ThirdPartyFacts.castBitVec (ThirdPartyFacts.inputLen_toFactsPartial p).symm x)

/--
As long as `GenericExtractedLocalCorePartial` carries `stableFacts`, the
globalization step is internally closed.
-/
theorem globalization_of_generic_extracted_local_core :
    GlobalizeRestrictedLocalBehaviorPartial :=
  globalization_of_decision_preservation_on_promise
    restrictedBehaviorDecisionPreservationOnPromise_of_generic_extracted_local_core

/--
Weak globalization follows from weak decision preservation on the promise
partition.
-/
theorem globalization_of_decision_preservation_on_promise_weak
    (hPres : WeakRestrictedBehaviorDecisionPreservationOnPromisePartial) :
    WeakGlobalizeRestrictedLocalBehaviorPartial := by
  intro p hFormula core rloc
  refine (Models.solvesPromise_gapPartialMCSP_iff (p := p)).2 ?_
  intro x
  let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  have hRestricted :
      rloc.decide x =
        ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) := by
    simpa [RestrictedLocalBehaviorSolver_Partial.decide, restrictedBehaviorSem,
      restrictedBehaviorWitness, solver, hlen,
      ThirdPartyFacts.castBitVec_castBitVec_symm] using
      rloc.restrictedCorrect (x := ThirdPartyFacts.castBitVec hlen.symm x)
  have hPromise :
      x ∈ (Models.GapPartialMCSPPromise p).Yes ∨
        x ∈ (Models.GapPartialMCSPPromise p).No := by
    cases hlang : Models.gapPartialMCSP_Language p (Models.partialInputLen p) x
    · right
      simpa [Models.GapPartialMCSPPromise, hlang]
    · left
      simpa [Models.GapPartialMCSPPromise, hlang]
  have hPreserve :
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x))
      =
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (ThirdPartyFacts.castBitVec hlen.symm x) :=
    hPres (p := p) (hFormula := hFormula) core x hPromise
  have hCorrect :
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (ThirdPartyFacts.castBitVec hlen.symm x)
      =
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := by
    have hsolver :
        solver.decide x =
          Models.gapPartialMCSP_Language p (Models.partialInputLen p) x :=
      (Models.solvesPromise_gapPartialMCSP_iff (p := p)).1 solver.correct_decide x
    simpa [solver, ThirdPartyFacts.solverDecideFacts, hlen,
      ThirdPartyFacts.castBitVec_castBitVec_symm] using hsolver
  calc
    rloc.decide x =
      ThirdPartyFacts.solverDecideFacts
        (p := p) solver
        (core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) := hRestricted
    _ =
      ThirdPartyFacts.solverDecideFacts
        (p := p) solver
        (ThirdPartyFacts.castBitVec hlen.symm x) := hPreserve
    _ = Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := hCorrect

/--
Weak probe wrapper: once decision preservation on the promise partition is
supplied for weak cores, globalization is immediate.
-/
theorem globalization_probe_of_weak_decision_preservation
    (hPres : WeakRestrictedBehaviorDecisionPreservationOnPromisePartial) :
    WeakGlobalizeRestrictedLocalBehaviorPartial :=
  globalization_of_decision_preservation_on_promise_weak hPres

/--
Per-core globalization for provenance-aware weak cores: this is the honest form
of globalization once preservation is treated as part of the extracted object
rather than as a global theorem about all weak cores.
-/
theorem solvesPromise_of_promisePreservingWeakGenericExtractedLocalCore
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pcore : PromisePreservingWeakGenericExtractedLocalCorePartial hFormula)
    (rloc : RestrictedLocalBehaviorSolver_Partial hFormula pcore.core.rFacts) :
    Complexity.SolvesPromise (Models.GapPartialMCSPPromise p) rloc.decide := by
  refine (Models.solvesPromise_gapPartialMCSP_iff (p := p)).2 ?_
  intro x
  let solver : SmallGeneralCircuitSolver_Partial p := generalSolverOfFormula hFormula
  let hlen :
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
        Models.partialInputLen p :=
    ThirdPartyFacts.inputLen_toFactsPartial p
  have hRestricted :
      rloc.decide x =
        ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (pcore.core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) := by
    simpa [RestrictedLocalBehaviorSolver_Partial.decide, restrictedBehaviorSem,
      restrictedBehaviorWitness, solver, hlen,
      ThirdPartyFacts.castBitVec_castBitVec_symm] using
      rloc.restrictedCorrect (x := ThirdPartyFacts.castBitVec hlen.symm x)
  have hPromise :
      x ∈ (Models.GapPartialMCSPPromise p).Yes ∨
        x ∈ (Models.GapPartialMCSPPromise p).No := by
    cases hlang : Models.gapPartialMCSP_Language p (Models.partialInputLen p) x
    · right
      simpa [Models.GapPartialMCSPPromise, hlang]
    · left
      simpa [Models.GapPartialMCSPPromise, hlang]
  have hPreserve :
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (pcore.core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x))
      =
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (ThirdPartyFacts.castBitVec hlen.symm x) :=
    pcore.preserveOnPromise x hPromise
  have hCorrect :
      ThirdPartyFacts.solverDecideFacts
          (p := p) solver
          (ThirdPartyFacts.castBitVec hlen.symm x)
      =
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := by
    have hsolver :
        solver.decide x =
          Models.gapPartialMCSP_Language p (Models.partialInputLen p) x :=
      (Models.solvesPromise_gapPartialMCSP_iff (p := p)).1 solver.correct_decide x
    simpa [solver, ThirdPartyFacts.solverDecideFacts, hlen,
      ThirdPartyFacts.castBitVec_castBitVec_symm] using hsolver
  calc
    rloc.decide x =
      ThirdPartyFacts.solverDecideFacts
        (p := p) solver
        (pcore.core.rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x)) := hRestricted
    _ =
      ThirdPartyFacts.solverDecideFacts
        (p := p) solver
        (ThirdPartyFacts.castBitVec hlen.symm x) := hPreserve
    _ = Models.gapPartialMCSP_Language p (Models.partialInputLen p) x := hCorrect

/--
Restriction-aware local certificate below the old `stableFacts` interface.

Unlike `FormulaRestrictionCertificateDataPartial`, this object does not claim
that the extracted restriction leaves the original solver globally invariant.
Instead it records a local solver for the *restricted* behavior together with
the test-set/locality bounds needed by `StructuredLocalityProviderPartial`.
-/
structure GenericRestrictedLocalCertificatePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  core : GenericExtractedLocalCorePartial hFormula
  T : Finset (Core.BitVec (Models.partialInputLen p))
  loc : LowerBounds.SmallLocalCircuitSolver_Partial p
  testSetPolylog :
    T.card ≤ Models.polylogBudget (Models.partialInputLen p)
  localityPolylog :
    loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p)
  restrictedCorrect :
    ∀ x : Facts.LocalityLift.BitVec
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
      loc.decide (ThirdPartyFacts.castBitVec (ThirdPartyFacts.inputLen_toFactsPartial p) x) =
        ThirdPartyFacts.solverDecideFacts (p := p) (generalSolverOfFormula hFormula)
          (core.rFacts.apply x)

/--
Provider interface for restriction-aware local certificates.
-/
def FormulaGenericRestrictedLocalCertificateProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (GenericRestrictedLocalCertificatePartial hFormula)

/--
Exact remaining transport obligation below the new generic extracted-core layer.

This is the first theorem target that is not just re-packaging the old
`stableFacts` route: given a restriction core, produce a local solver for the
restricted behavior of the extracted general solver.
-/
def GenericRestrictedLocalCertificateTransportPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (core : GenericExtractedLocalCorePartial hFormula),
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        ∀ x : Facts.LocalityLift.BitVec
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)),
          loc.decide (ThirdPartyFacts.castBitVec (ThirdPartyFacts.inputLen_toFactsPartial p) x) =
            ThirdPartyFacts.solverDecideFacts (p := p) (generalSolverOfFormula hFormula)
              (core.rFacts.apply x)

/--
Assemble the new restriction-aware certificate provider from:
1) a generic extracted-core provider, and
2) a transport theorem producing a local solver for restricted behavior.
-/
noncomputable def
    genericRestrictedLocalCertificateProvider_of_generic_extracted_local_core_provider_and_transport
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial)
    (hTransport : GenericRestrictedLocalCertificateTransportPartial) :
    FormulaGenericRestrictedLocalCertificateProviderPartial := by
  intro p hFormula
  rcases hCore (p := p) hFormula with ⟨core⟩
  rcases hTransport (p := p) hFormula core with
    ⟨T, loc, hT, hℓ, hrestricted⟩
  exact ⟨
    { core := core
      T := T
      loc := loc
      testSetPolylog := hT
      localityPolylog := hℓ
      restrictedCorrect := hrestricted }⟩

/--
Bridge: extracted local-core provider is sufficient to recover the existing
support-bounds interface consumed by the locality chain.
-/
theorem formula_support_bounds_of_extracted_local_core_provider
    (hCore : FormulaExtractedLocalCoreProviderPartial) :
    FormulaSupportRestrictionBoundsPartial := by
  classical
  intro p hFormula
  rcases hCore (p := p) hFormula with ⟨core⟩
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
  have hBridge : core.rFacts = rFacts := by
    simpa [wf, c, alive, rPartial, hlen, rFacts] using core.supportBridge
  change
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
  refine ⟨?_, ?_, ?_⟩
  · simpa [hBridge] using core.polylogAlive
  · simpa [solver, hBridge] using core.smallEnough
  · simpa [hBridge] using core.quarterAlive

/--
Semantic-link payload produced by the A9 semantic provider for one strict
formula witness.
-/
def FormulaSemanticLinkPartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) : Prop :=
  let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
    Classical.choose hFormula
  let c := wf.family (Models.partialInputLen p)
  ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
    (hsame : ac0.n = Models.partialInputLen p),
    ∃ f : Core.BitVec ac0.n → Bool,
      f ∈ F ∧
      ∀ x : Core.BitVec ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec hsame x)

/--
Extract the semantic link directly from `FormulaSemanticMultiSwitchingProvider`.
-/
theorem formulaSemanticLinkPartial_of_provider
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    FormulaSemanticLinkPartial hFormula := by
  classical
  simpa [FormulaSemanticLinkPartial] using
    AC0LocalityBridge.semantic_provider_semantic_link hSem (p := p) hFormula

/--
Core A9 obligations separated from wrapper-level plumbing.

These are the three red obligations that remain after projecting semantic
multi-switching payload to the strict formula witness:
1) polylog bound for the induced support restriction,
2) `LocalCircuitSmallEnough` for the induced restriction-local parameters,
3) quarter-alive bound for the induced restriction.
-/
structure FormulaSupportCoreSteps
    : Prop where
  formula_witness_yields_polylog_support :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      FormulaSemanticLinkPartial hFormula →
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
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p))
  small_local_core_shrinks_under_restrictions :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      FormulaSemanticLinkPartial hFormula →
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
      Facts.LocalityLift.LocalCircuitSmallEnough
        { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
          , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
              * rFacts.alive.card.succ
          , ℓ := rFacts.alive.card
          , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth }
  alive_card_quarter_bound :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      FormulaSemanticLinkPartial hFormula →
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
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4

/--
Core step (2): `LocalCircuitSmallEnough` is directly projectable from the
strengthened multi-switching contract.
-/
theorem small_local_core_shrinks_under_restrictions_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (_hLink : FormulaSemanticLinkPartial hFormula) :
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
    Facts.LocalityLift.LocalCircuitSmallEnough
      { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
        , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
            * rFacts.alive.card.succ
        , ℓ := rFacts.alive.card
        , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } := by
  classical
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
  obtain ⟨_, _, _, _, _, _, _, hsmall0, _⟩ := hMS.package (p := p) hFormula
  simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using hsmall0

/--
Core step (3): quarter-alive bound is directly projectable from the
strengthened multi-switching contract.
-/
theorem alive_card_quarter_bound_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (_hLink : FormulaSemanticLinkPartial hFormula) :
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
      Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 := by
  classical
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
  obtain ⟨_, _, _, _, _, _, _, _, hhalf⟩ := hMS.package (p := p) hFormula
  simpa [wf, c, alive, rPartial, hlen, rFacts] using hhalf

/--
Core step (1): polylog-support bound is directly projectable from the
strengthened multi-switching contract.
-/
theorem formula_witness_yields_polylog_support_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (_hLink : FormulaSemanticLinkPartial hFormula) :
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
        (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) := by
  classical
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
  obtain ⟨_, _, _, _, _, _, hpoly, _, _⟩ := hMS.package (p := p) hFormula
  simpa [wf, c, alive, rPartial, hlen, rFacts] using hpoly

/--
From the strengthened multi-switching contract all three core obligations are
projectable for the extracted strict witness.
-/
theorem formula_support_core_steps_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    FormulaSupportCoreSteps := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hFormula hLink
    exact formula_witness_yields_polylog_support_of_multiswitching_contract
      (hMS := hMS) (p := p) hFormula hLink
  · intro p hFormula hLink
    exact small_local_core_shrinks_under_restrictions_of_multiswitching_contract
      (hMS := hMS) (p := p) hFormula hLink
  · intro p hFormula hLink
    exact alive_card_quarter_bound_of_multiswitching_contract
      (hMS := hMS) (p := p) hFormula hLink

/--
Core assembly theorem for A9.

If the three core obligations are available from semantic multi-switching
payload, then the support-bounds interface used by the locality route follows.
-/
theorem formula_support_bounds_internal_of_core_steps
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
    (hCore : FormulaSupportCoreSteps) :
    FormulaSupportRestrictionBoundsPartial := by
  classical
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
  have hLink : FormulaSemanticLinkPartial hFormula :=
    formulaSemanticLinkPartial_of_provider hSem (p := p) hFormula
  have hPoly :
      rFacts.alive.card ≤
        Facts.LocalityLift.polylogBudget
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) := by
    simpa [wf, c, alive, rPartial, hlen, rFacts] using
      hCore.formula_witness_yields_polylog_support (p := p) hFormula hLink
  have hSmall :
      Facts.LocalityLift.LocalCircuitSmallEnough
        { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
          , M := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.size
              * rFacts.alive.card.succ
          , ℓ := rFacts.alive.card
          , depth := (ThirdPartyFacts.toFactsGeneralSolverPartial solver).params.depth } := by
    simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using
      hCore.small_local_core_shrinks_under_restrictions
        (p := p) hFormula hLink
  have hQuarter :
      rFacts.alive.card ≤
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4 := by
    simpa [wf, c, alive, rPartial, hlen, rFacts] using
      hCore.alive_card_quarter_bound (p := p) hFormula hLink
  exact ⟨hPoly, hSmall, hQuarter⟩

/--
Construct the strengthened I-2B contract from two independent ingredients:
1) semantic AC0/multi-switching provenance for extracted formulas;
2) numeric support-based locality bounds.

This isolates the remaining constructive target to semantic provisioning
(`FormulaSemanticMultiSwitchingProvider`), while keeping numeric bounds in the
existing support-bounds route.
-/
theorem multiswitching_contract_of_semantic_provider_and_support_bounds
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract := by
  classical
  refine ⟨?_⟩
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
  obtain ⟨ac0, F, hsame, hFam, hMSw, hLink⟩ :=
    hSem.package (p := p) hFormula
  exact ⟨ac0, F, hsame, hFam, hMSw, hLink, hB.1, hB.2.1, hB.2.2⟩

/--
Derived A9 contract builder through the core-step decomposition:
semantic provider + core obligations -> full strengthened contract.
-/
theorem multiswitching_contract_of_semantic_provider_and_core_steps
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
    (hCore : FormulaSupportCoreSteps) :
    AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract := by
  exact multiswitching_contract_of_semantic_provider_and_support_bounds
    hSem (formula_support_bounds_internal_of_core_steps hSem hCore)

/--
Named closure hook for I-4:
once multi-switching/counting establishes support-based bounds, this theorem is
the exact bridge expected by the magnification interface.

The strengthened I-2B contract also carries semantic linkage data (`F` contains
a function extensionally equal to the extracted strict formula).  This theorem
projects the numeric support-bounds fragment consumed by the locality route.
-/
theorem formula_support_bounds_from_multiswitching
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    FormulaSupportRestrictionBoundsPartial := by
  classical
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
  obtain ⟨_, _, _, _, _, _, hpoly, hsmall0, hhalf⟩ :=
    hMS.package (p := p) hFormula
  refine ⟨hpoly, ?_, hhalf⟩
  simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using hsmall0

/--
Direct extraction route from the strengthened A9 contract to the new
`ExtractedLocalCorePartial` interface.
-/
theorem extracted_local_core_provider_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    FormulaExtractedLocalCoreProviderPartial := by
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
  obtain ⟨_, _, _, _, _, _, hpoly, hsmall0, hhalf⟩ :=
    hMS.package (p := p) hFormula
  refine ⟨{
    rFacts := rFacts
    supportBridge := by
      simp [wf, c, alive, rPartial, rFacts]
    polylogAlive := hpoly
    smallEnough := by
      simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using hsmall0
    quarterAlive := hhalf
  }⟩

/--
Generic extracted-core provider obtained from the strengthened multi-switching
contract.  This route does not expose canonical-support equations at the
interface boundary.
-/
theorem generic_extracted_local_core_provider_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    FormulaGenericExtractedLocalCoreProviderPartial := by
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
  obtain ⟨_, _, _, _, _, _, hpoly, hsmall0, hhalf⟩ :=
    hMS.package (p := p) hFormula
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
  refine ⟨{
    rFacts := rFacts
    polylogAlive := hpoly
    smallEnough := by
      simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using hsmall0
    quarterAlive := hhalf
    stableFacts := hstableFacts
  }⟩

/--
The current support-based extraction is semantically stable for the formula
derived general solver: restricting outside `FormulaCircuit.support` does not
change the solver decision.
-/
theorem solverDecideFacts_stable_of_current_extracted_restriction
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))
    (x : Core.BitVec (Models.partialInputLen p)) :
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
    ThirdPartyFacts.solverDecideFacts (p := p) solver
      (rFacts.apply (ThirdPartyFacts.castBitVec hlen.symm x))
    =
    ThirdPartyFacts.solverDecideFacts (p := p) solver
      (ThirdPartyFacts.castBitVec hlen.symm x) := by
  classical
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
  have hstablePartial :
      ∀ y : Core.BitVec (Models.partialInputLen p),
        solver.decide (rPartial.apply y) = solver.decide y := by
    intro y
    change
      ComplexityInterfaces.FormulaCircuit.eval c (rPartial.apply y) =
        ComplexityInterfaces.FormulaCircuit.eval c y
    apply ComplexityInterfaces.FormulaCircuit.eval_eq_of_eq_on_support
    intro i hi
    exact Facts.LocalityLift.Restriction.apply_alive rPartial y hi
  have hstableCast :
      ∀ y : Core.BitVec (Models.partialInputLen p),
        ThirdPartyFacts.solverDecideFacts (p := p) solver
            (ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply y)) =
          ThirdPartyFacts.solverDecideFacts (p := p) solver
            (ThirdPartyFacts.castBitVec hlen.symm y) := by
    intro y
    change
      solver.decide
          (ThirdPartyFacts.castBitVec hlen
            (ThirdPartyFacts.castBitVec hlen.symm (rPartial.apply y))) =
        solver.decide
          (ThirdPartyFacts.castBitVec hlen
            (ThirdPartyFacts.castBitVec hlen.symm y))
    simpa [ThirdPartyFacts.castBitVec_castBitVec_symm] using hstablePartial y
  have hstableRaw :=
    ThirdPartyFacts.stable_of_stable_cast
      (h := hlen.symm)
      (decide := ThirdPartyFacts.solverDecideFacts (p := p) solver)
      (r := rPartial)
      hstableCast
  simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using
    hstableRaw (ThirdPartyFacts.castBitVec hlen.symm x)

/--
Current support-bounds assumptions already suffice to construct a
provenance-aware weak-core provider for the canonical support-based extraction.

This theorem makes explicit that the remaining weak-core route no longer
depends on the stronger multi-switching package: only the numeric
`FormulaSupportRestrictionBoundsPartial` fragment is used here, while
promise-preservation is supplied by
`solverDecideFacts_stable_of_current_extracted_restriction`.
-/
theorem promisePreservingWeakGenericExtractedLocalCoreProvider_of_supportBounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial := by
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
  refine ⟨{
    core := {
      rFacts := rFacts
      polylogAlive := hB.1
      smallEnough := hB.2.1
      quarterAlive := hB.2.2
    }
    preserveOnPromise := ?_
  }⟩
  intro x _hxPromise
  simpa [solver, wf, c, alive, rPartial, hlen, rFacts] using
    solverDecideFacts_stable_of_current_extracted_restriction
      (p := p) hFormula x

/--
Current extraction route promoted to a provenance-aware weak-core provider.

This theorem does not use the stronger generic-core interface: it attaches the
needed promise-preservation fact directly to the weak core produced by the
current support-based extraction.
-/
theorem promisePreservingWeakGenericExtractedLocalCoreProvider_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial :=
  promisePreservingWeakGenericExtractedLocalCoreProvider_of_supportBounds
    (formula_support_bounds_from_multiswitching hMS)

/--
Combined projection for the strengthened multi-switching contract:
it yields both the numeric support-bounds fragment used by locality lifting
and the semantic link tying the AC0-family payload to the extracted formula.
-/
theorem formula_support_bounds_and_semantic_link_from_multiswitching
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    FormulaSupportRestrictionBoundsPartial ∧
    (∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
        Classical.choose hFormula
      let c := wf.family (Models.partialInputLen p)
      ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
        (hsame : ac0.n = Models.partialInputLen p),
        ∃ f : Core.BitVec ac0.n → Bool,
          f ∈ F ∧
          ∀ x : Core.BitVec ac0.n,
            f x = ComplexityInterfaces.FormulaCircuit.eval c
              (ThirdPartyFacts.castBitVec hsame x)) := by
  refine ⟨formula_support_bounds_from_multiswitching hMS, ?_⟩
  intro p hFormula
  simpa using AC0LocalityBridge.package_semantic_link hMS (p := p) hFormula

/--
Convenient combined projection from split A9 inputs
(`semantic provider` + `support bounds`) to the active locality-facing API.
-/
theorem formula_support_bounds_and_semantic_link_of_semantic_provider_and_support_bounds
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider)
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    FormulaSupportRestrictionBoundsPartial ∧
    (∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
        Classical.choose hFormula
      let c := wf.family (Models.partialInputLen p)
      ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
        (hsame : ac0.n = Models.partialInputLen p),
        ∃ f : Core.BitVec ac0.n → Bool,
          f ∈ F ∧
          ∀ x : Core.BitVec ac0.n,
            f x = ComplexityInterfaces.FormulaCircuit.eval c
              (ThirdPartyFacts.castBitVec hsame x)) := by
  exact
    formula_support_bounds_and_semantic_link_from_multiswitching
      (multiswitching_contract_of_semantic_provider_and_support_bounds
        hSem hBounds)

/--
Internalized A9 constructor:
the strengthened multi-switching contract is derivable from support-bounds
assumptions alone via the internal semantic provider.
-/
theorem multiswitching_contract_internalized_of_support_bounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract := by
  exact multiswitching_contract_of_semantic_provider_and_support_bounds
    AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal
    hBounds

/--
Internalized combined A9 projection from support-bounds assumptions:
returns both numeric locality bounds and semantic linkage with no external
semantic-provider input.
-/
theorem formula_support_bounds_and_semantic_link_of_support_bounds
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    FormulaSupportRestrictionBoundsPartial ∧
    (∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
        Classical.choose hFormula
      let c := wf.family (Models.partialInputLen p)
      ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n)
        (hsame : ac0.n = Models.partialInputLen p),
        ∃ f : Core.BitVec ac0.n → Bool,
          f ∈ F ∧
          ∀ x : Core.BitVec ac0.n,
            f x = ComplexityInterfaces.FormulaCircuit.eval c
              (ThirdPartyFacts.castBitVec hsame x)) := by
  exact
    formula_support_bounds_and_semantic_link_from_multiswitching
      (multiswitching_contract_internalized_of_support_bounds hBounds)

/--
Default-flag wrapper for `formula_support_bounds_from_multiswitching`.
-/
theorem hasDefaultFormulaSupportRestrictionBoundsPartial_from_multiswitching
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    Nonempty FormulaSupportRestrictionBoundsPartial :=
  ⟨formula_support_bounds_from_multiswitching hMS⟩

/--
Constructive builder of `FormulaRestrictionCertificateDataPartial` from the new
generic extracted-core provider interface.
-/
noncomputable def formulaRestrictionCertificateData_of_generic_extracted_local_core_provider
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial) :
    FormulaRestrictionCertificateDataPartial where
  restrictionData := by
    intro p hFormula
    rcases hCore (p := p) hFormula with ⟨core⟩
    exact ⟨core.rFacts, core.polylogAlive, core.smallEnough, core.quarterAlive, core.stableFacts⟩

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
Direct structured-provider constructor from the generic extracted local-core
interface (no canonical `support c` requirement in the interface itself).
-/
theorem structuredLocalityProviderPartial_of_generic_extracted_local_core_provider
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_restrictionData
    (formulaRestrictionCertificateData_of_generic_extracted_local_core_provider hCore)

/--
Direct structured-provider constructor from restriction-aware local
certificates.

This route bypasses the old `FormulaRestrictionCertificateDataPartial` layer and
therefore does not use `stableFacts`.
-/
theorem structuredLocalityProviderPartial_of_generic_restricted_local_certificate_provider
    (hCert : FormulaGenericRestrictedLocalCertificateProviderPartial) :
    StructuredLocalityProviderPartial := by
  intro p δ hHyp hFormula
  rcases hCert (p := p) hFormula with ⟨cert⟩
  exact ⟨cert.T, cert.loc, cert.testSetPolylog, cert.localityPolylog⟩

/--
Direct structured-provider constructor from the weaker restricted-behavior
provider, assuming a separate globalization theorem.
-/
theorem structuredLocalityProviderPartial_of_generic_restricted_behavior_provider_and_globalize
    (hRestr : FormulaGenericRestrictedBehaviorProviderPartial)
    (hGlobalize : GlobalizeRestrictedLocalBehaviorPartial) :
    StructuredLocalityProviderPartial := by
  intro p δ hHyp hFormula
  rcases hRestr (p := p) hFormula with ⟨cert⟩
  let loc : LowerBounds.SmallLocalCircuitSolver_Partial p :=
    cert.rloc.toSmallLocalCircuitSolver_Partial
      (hGlobalize (p := p) (hFormula := hFormula) (core := cert.core) cert.rloc)
  exact ⟨cert.rloc.T, loc, cert.rloc.testSetPolylog, by
    simpa [loc] using cert.rloc.localityPolylog⟩

/--
Weak direct structured-provider constructor from the weaker restricted-behavior
provider, assuming only weak globalization.
-/
theorem structuredLocalityProviderPartial_of_weak_generic_restricted_behavior_provider_and_globalize
    (hRestr : FormulaWeakGenericRestrictedBehaviorProviderPartial)
    (hGlobalize : WeakGlobalizeRestrictedLocalBehaviorPartial) :
    StructuredLocalityProviderPartial := by
  intro p δ hHyp hFormula
  rcases hRestr (p := p) hFormula with ⟨cert⟩
  let loc : LowerBounds.SmallLocalCircuitSolver_Partial p :=
    cert.rloc.toSmallLocalCircuitSolver_Partial
      (hGlobalize (p := p) (hFormula := hFormula) (core := cert.core) cert.rloc)
  exact ⟨cert.rloc.T, loc, cert.rloc.testSetPolylog, by
    simpa [loc] using cert.rloc.localityPolylog⟩

/--
Provenance-aware weak route: once a weak extracted core is bundled with its own
promise-preservation fact, no global weak-preservation theorem is needed.
-/
theorem structuredLocalityProviderPartial_of_promisePreservingWeakGenericCoreProvider_and_behavior_transport
    (hCore : FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial)
    (hTransport : WeakGenericRestrictedLocalBehaviorTransportPartial) :
    StructuredLocalityProviderPartial := by
  intro p δ hHyp hFormula
  rcases hCore (p := p) hFormula with ⟨pcore⟩
  rcases hTransport (p := p) hFormula pcore.core with ⟨rloc⟩
  let loc : LowerBounds.SmallLocalCircuitSolver_Partial p :=
    rloc.toSmallLocalCircuitSolver_Partial
      (solvesPromise_of_promisePreservingWeakGenericExtractedLocalCore pcore rloc)
  exact ⟨rloc.T, loc, rloc.testSetPolylog, by
    simpa [loc] using rloc.localityPolylog⟩

/--
Convenience wrapper: the restricted-behavior transport for weak cores is already
internal, so a provenance-aware weak-core provider alone suffices.
-/
theorem structuredLocalityProviderPartial_of_promisePreservingWeakGenericCoreProvider
    (hCore : FormulaPromisePreservingWeakGenericExtractedLocalCoreProviderPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_promisePreservingWeakGenericCoreProvider_and_behavior_transport
    hCore
    genericRestrictedLocalBehaviorTransport_of_weak_core

/--
Support-bounds assumptions already imply the provenance-aware weak-core route.

This makes explicit that the weak-core plumbing no longer depends on the
stronger multi-switching contract once the numeric support-bounds fragment has
been isolated.
-/
theorem structuredLocalityProviderPartial_of_supportBounds_via_promisePreservingWeakCore
    (hBounds : FormulaSupportRestrictionBoundsPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_promisePreservingWeakGenericCoreProvider
    (promisePreservingWeakGenericExtractedLocalCoreProvider_of_supportBounds hBounds)

/--
Composed weak route: a generic extracted-core provider suffices for
`StructuredLocalityProviderPartial` once the remaining restricted-behavior
transport theorem is available.
-/
theorem structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_and_transport
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial)
    (hTransport : GenericRestrictedLocalCertificateTransportPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_generic_restricted_local_certificate_provider
    (genericRestrictedLocalCertificateProvider_of_generic_extracted_local_core_provider_and_transport
      hCore hTransport)

/--
New weakest route:
generic extracted cores + restricted-behavior transport + globalization are
sufficient for `StructuredLocalityProviderPartial`.
-/
theorem structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_and_behavior_transport_and_globalize
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial)
    (hTransport : GenericRestrictedLocalBehaviorTransportPartial)
    (hGlobalize : GlobalizeRestrictedLocalBehaviorPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_generic_restricted_behavior_provider_and_globalize
    (genericRestrictedBehaviorProvider_of_generic_extracted_local_core_provider_and_transport
      hCore hTransport)
    hGlobalize

/--
With the current generic extracted-core interface, restricted-behavior transport
already suffices: globalization follows from `core.stableFacts`.
-/
theorem structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_and_behavior_transport
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial)
    (hTransport : GenericRestrictedLocalBehaviorTransportPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_and_behavior_transport_and_globalize
    hCore hTransport globalization_of_generic_extracted_local_core

/--
Honest weakest route on the weakened generic core: the remaining semantic
question is now entirely isolated in weak globalization.
-/
theorem structuredLocalityProviderPartial_of_weak_generic_extracted_local_core_provider_and_behavior_transport_and_globalize
    (hCore : FormulaWeakGenericExtractedLocalCoreProviderPartial)
    (hTransport : WeakGenericRestrictedLocalBehaviorTransportPartial)
    (hGlobalize : WeakGlobalizeRestrictedLocalBehaviorPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_weak_generic_restricted_behavior_provider_and_globalize
    (weakGenericRestrictedBehaviorProvider_of_weak_generic_extracted_local_core_provider_and_transport
      hCore hTransport)
    hGlobalize

/--
Current strong generic cores already induce a provenance-aware weak-core
provider, so the provenance-aware weak route is internally available.
-/
theorem structuredLocalityProviderPartial_of_generic_extracted_local_core_provider_via_promisePreservingWeakCore
    (hCore : FormulaGenericExtractedLocalCoreProviderPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_promisePreservingWeakGenericCoreProvider_and_behavior_transport
    (promisePreservingWeakGenericExtractedLocalCoreProvider_of_generic hCore)
    genericRestrictedLocalBehaviorTransport_of_weak_core

/--
New core-facing bridge: extracted local-core provider implies structured
locality provider through the existing support-bounds pipeline.
-/
theorem structuredLocalityProviderPartial_of_extracted_local_core_provider
    (hCore : FormulaExtractedLocalCoreProviderPartial) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_supportBounds
    (formula_support_bounds_of_extracted_local_core_provider hCore)

/--
Direct constructive structured-provider constructor from an explicit
multi-switching support-bounds contract.
-/
theorem structuredLocalityProviderPartial_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_supportBounds
    (formula_support_bounds_from_multiswitching hMS)

/--
Same endpoint as `structuredLocalityProviderPartial_of_multiswitching_contract`,
but routed through the extracted local-core interface.
-/
theorem structuredLocalityProviderPartial_of_multiswitching_contract_via_extracted_local_core
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_extracted_local_core_provider
    (extracted_local_core_provider_of_multiswitching_contract hMS)

/--
Same endpoint as `structuredLocalityProviderPartial_of_multiswitching_contract`,
but routed through the generic extracted local-core interface.
-/
theorem structuredLocalityProviderPartial_of_multiswitching_contract_via_generic_extracted_local_core
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_generic_extracted_local_core_provider
    (generic_extracted_local_core_provider_of_multiswitching_contract hMS)

/--
Same endpoint as `structuredLocalityProviderPartial_of_multiswitching_contract`,
but routed through the provenance-aware weak-core provider extracted from the
current support-based restriction.
-/
theorem structuredLocalityProviderPartial_of_multiswitching_contract_via_promisePreservingWeakCore
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    StructuredLocalityProviderPartial :=
  structuredLocalityProviderPartial_of_supportBounds_via_promisePreservingWeakCore
    (formula_support_bounds_from_multiswitching hMS)

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
Direct I-2 contract from an explicit multi-switching support-bounds package.
-/
noncomputable def directStructuredLocalityProviderContract_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    DirectStructuredLocalityProviderContract :=
  directStructuredLocalityProviderContract_of_supportBounds
    (formula_support_bounds_from_multiswitching hMS)

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
End-to-end I-2 wiring: a multi-switching support-bounds contract provides
default structured locality-provider availability.
-/
theorem hasDefaultStructuredLocalityProviderPartial_of_multiswitching_contract
    (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_supportBounds
    (formula_support_bounds_from_multiswitching hMS)

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
