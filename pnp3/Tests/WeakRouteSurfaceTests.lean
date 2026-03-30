import Magnification.FinalResult

/-!
# Weak-route final surface smoke tests

This module is intentionally lightweight: it does not attempt to construct
nontrivial witnesses, but it **does** force Lean to elaborate the exact theorem
types that define the current weak-route final interface.

Rationale:
- when endpoint names or signatures drift during refactors, these declarations
  fail immediately;
- this gives a small, explicit regression surface for the current roadmap:
  accepted-family endpoint, promise-YES endpoint, PRG-image backup, and
  restriction fallback wrappers in `Magnification.FinalResult`.
-/

namespace Pnp3.Tests

open Pnp3
open Pnp3.LowerBounds
open Pnp3.Magnification

/-!
## Type-level interface checks

Each `def` below pins one exported theorem to its current type.
If any theorem is renamed or its argument order/type changes, this file stops
compiling and signals an interface regression.
-/

/-- Surface accepted-family wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_acceptedFamilyStatement :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      SmallDAGImpliesAcceptedFamilyStatement F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_acceptedFamilyStatement

/-- Surface promise-YES statement wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_promiseYesSubcubeStatement :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_promiseYesSubcubeStatement

/-- Surface PRG-image backup wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_prgImageAcceptanceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      prgImageAcceptanceAtProviderOnSlices F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_prgImageAcceptanceProviderOnSlices

/-- Surface restriction-fallback wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_restrictionFallbackOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound),
      smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_restrictionFallbackOnSlices

/--
Technical source-level reduction from pairwise promise/value packages to the
mainline promise-YES statement remains in the lower-bounds producer layer
(not in `Magnification.FinalResult`).
-/
def check_smallDAGPromiseYesSubcubeStatement_of_packageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound →
        SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound :=
  smallDAGPromiseYesSubcubeStatement_of_packageProvider

/--
Gate-G1 Route-B item (3) wrapper is available with the expected type:
a DAG-native certificate provider compiles directly to the canonical
stable-restriction goal family over `dagCanonicalPayload`.
-/
def check_gateG1_routeB_stableRestrictionGoal_of_certificateProvider :
    ∀ {p : Models.GapPartialMCSPParams}
      (_hCert : dagStableRestrictionCertificateProvider p),
      ∀ hDag : ComplexityInterfaces.PpolyDAG (Models.gapPartialMCSP_Language p),
        stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag) :=
  gateG1_routeB_stableRestrictionGoal_of_certificateProvider

/--
Q1/Q2 split-provider compilation to promise-YES certificate provider is
available with the expected type.
-/
def check_promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound),
      promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv →
        (∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
            PromiseYesSubcubeCertificateAt W) :=
  promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider

/-- Q1/Q2 split-provider no-small-DAG closure is available with the expected type. -/
def check_noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound),
      promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices

/--
Q1 semantic provider + required-budget provider compiles directly to no-small-DAG
with the expected type.
-/
def check_noSmallDAG_of_promiseYesRequiredBudgetProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound),
      promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound hInv →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_promiseYesRequiredBudgetProviderOnSlices

/--
Strict-semantics specialization of the required-budget closure is available with
the expected type.
-/
def check_noSmallDAG_of_strictSemanticsAndRequiredBudgetProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (_hBudget :
        promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound
          (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
            F SizeBound)),
      ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_strictSemanticsAndRequiredBudgetProviderOnSlices

/--
Canonical-surface strict-mainline blocker is available with the expected type:
at any concrete solver index, strict required-budget provider is impossible.
-/
def check_not_strictRequiredBudgetProvider_onCanonicalBound_of_smallDAGSolver :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)))
      (n : Nat) (β ε : Rat),
      SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε →
        ¬ promiseYesRequiredBudgetOnInvariantProviderOnSlices
            F
            (ppolyDAGSizeBoundOnSlices F hInDag)
            (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
              F (ppolyDAGSizeBoundOnSlices F hInDag)) :=
  not_strictRequiredBudgetProvider_onCanonicalBound_of_smallDAGSolver

/--
Pointwise contradiction wrapper for strict canonical required-budget route is
available with expected type.
-/
def check_false_of_smallDAGSolver_and_strictRequiredBudgetProvider_onCanonicalBound :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)))
      (n : Nat) (β ε : Rat),
      SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε →
      promiseYesRequiredBudgetOnInvariantProviderOnSlices
        F
        (ppolyDAGSizeBoundOnSlices F hInDag)
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
          F (ppolyDAGSizeBoundOnSlices F hInDag)) →
        False :=
  false_of_smallDAGSolver_and_strictRequiredBudgetProvider_onCanonicalBound

/--
Package-provider -> Q1 semantic-provider reduction is available with the
expected type.
-/
noncomputable def check_promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound →
        promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound :=
  promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider

/--
Strict-DAG-semantics witness-level Q1 constructor is available with the expected
type.
-/
def check_promiseYesAcceptanceInvariantAt_of_strictDAGSemantics :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      PromiseYesAcceptanceInvariantAt W :=
  promiseYesAcceptanceInvariantAt_of_strictDAGSemantics

/--
Strict-DAG-semantics family-level Q1 provider is available with the expected
type.
-/
def check_promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound :=
  promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics

/--
Route-B source constructor from a concrete strict DAG witness plus support-half
bound is available with expected type.
-/
noncomputable def check_dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf :
    ∀ {p : Models.GapPartialMCSPParams}
      (w : ComplexityInterfaces.InPpolyDAG (Models.gapPartialMCSP_Language p))
      (_hHalf :
        (ComplexityInterfaces.DagCircuit.support (w.family (Models.partialInputLen p))).card ≤
          Models.Partial.tableLen p.n / 2),
      DAGStableRestrictionInvariantPackage
        (show ComplexityInterfaces.PpolyDAG (Models.gapPartialMCSP_Language p) from ⟨w, trivial⟩) :=
  dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf

/--
Route-B Task-1 reduction theorem is available with expected type:
uniform strict-witness support-half bounds imply the invariant provider.
-/
noncomputable def check_dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf :
    ∀ {p : Models.GapPartialMCSPParams}
      (_hSupportHalf :
        ∀ w : ComplexityInterfaces.InPpolyDAG (Models.gapPartialMCSP_Language p),
          (ComplexityInterfaces.DagCircuit.support (w.family (Models.partialInputLen p))).card ≤
            Models.Partial.tableLen p.n / 2),
      dagStableRestrictionInvariantProvider p :=
  dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf

/--
Branch-A strengthened provider target (nontrivial `S`) is exposed with the
expected type.
-/
def check_promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices :
    (GapSliceFamily → (Nat → Rat → Rat → Nat → Prop) → Type) :=
  promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices

/--
Alternative positive-source route package with formula-track export hooks is
available with the expected type.
-/
def check_NontrivialSAlternativeProducerRoute :
    Type :=
  NontrivialSAlternativeProducerRoute

/--
Projection to `FormulaSupportRestrictionBoundsPartial` is available with the
expected type.
-/
def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSAlternativeProducerRoute :
    NontrivialSAlternativeProducerRoute →
      Magnification.FormulaSupportRestrictionBoundsPartial :=
  formulaSupportRestrictionBoundsPartial_of_nontrivialSAlternativeProducerRoute

/--
Projection to `FormulaRestrictionCertificateDataPartial` is available with the
expected type.
-/
noncomputable def check_formulaRestrictionCertificateDataPartial_of_nontrivialSAlternativeProducerRoute :
    NontrivialSAlternativeProducerRoute →
      Magnification.FormulaRestrictionCertificateDataPartial :=
  formulaRestrictionCertificateDataPartial_of_nontrivialSAlternativeProducerRoute

/--
First concrete inhabitant builder for the alternative route package is available
with the expected type.
-/
noncomputable def check_nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.FormulaSupportRestrictionBoundsPartial →
      NontrivialSAlternativeProducerRoute :=
  nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds

/--
Class-shaped export theorem to `FormulaSupportRestrictionBoundsPartial` is
available with the expected type.
-/
noncomputable def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.FormulaSupportRestrictionBoundsPartial →
      Magnification.FormulaSupportRestrictionBoundsPartial :=
  formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andSupportBounds

/--
I-2 ladder theorem from the same class-shaped source is available with the
expected type.
-/
noncomputable def check_hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.FormulaSupportRestrictionBoundsPartial →
      Magnification.hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andSupportBounds

/--
Support-bounds closure from non-full-`S` slice source plus multi-switching
contract is available with the expected type.
-/
noncomputable def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andMultiswitching :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract →
      Magnification.FormulaSupportRestrictionBoundsPartial :=
  formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andMultiswitching

/--
I-2 default structured-provider closure from the same assumptions is available
with the expected type.
-/
noncomputable def check_hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andMultiswitching :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract →
      Magnification.hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andMultiswitching

/--
Current strict-Q1 route explicitly pins `S = Finset.univ`.
-/
def check_strictDAGSemantics_S_eq_univ :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S = Finset.univ :=
  strictDAGSemantics_S_eq_univ

/--
Current strict-Q1 route cannot satisfy the Branch-A nontrivial-`S` target.
-/
def check_no_nontrivialS_acceptanceInvariant_of_strictDAGSemantics :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      ((promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S ≠ Finset.univ) → False :=
  strictDAGSemantics_nontrivialS_false

/--
N2 impossibility theorem for the current strict-semantics Q1 set choice is
available with the expected type.
-/
def check_no_sameSetSlack_of_strictDAGSemantics :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      ¬ Models.circuitCountBound p.n (p.sNO - 1) <
          2 ^ (Models.Partial.tableLen p.n - (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S.card) :=
  no_sameSetSlack_of_strictDAGSemantics

/--
Branch-C quantitative nontriviality from promise/value packages is available.
-/
def check_nontrivialS_of_promiseValueLocalityPackageAt :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      {W : SmallDAGWitnessOnSlice p SizeBound ε}
      (cert : PromiseValueLocalityPackageAt W),
      cert.S ≠ Finset.univ :=
  nontrivialS_of_promiseValueLocalityPackageAt

/--
Branch-C witness-level bridge to nontrivial-Q1 invariant is available.
-/
noncomputable def check_promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      {W : SmallDAGWitnessOnSlice p SizeBound ε}
      (_cert : PromiseValueLocalityPackageAt W),
      PromiseYesAcceptanceInvariantAtNontrivialS W :=
  promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt

/--
Branch-C provider-level bridge to nontrivial-Q1 invariants is available.
-/
noncomputable def
    check_promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices_of_promiseValueLocalityPackageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (_hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound),
      promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices F SizeBound :=
  promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices_of_promiseValueLocalityPackageProvider

/--
Package-provider -> Q2 slack-provider reduction is available with the expected
dependent-provider type.
-/
noncomputable def check_promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound),
      promiseYesSlackOnInvariantProviderOnSlices
        F SizeBound
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider
          F SizeBound hPkg) :=
  promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider

/--
Package-provider closure through split Q1/Q2 interface is available with the
expected type.
-/
noncomputable def check_noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices_viaSemanticAndSlack :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices_viaSemanticAndSlack

/-- Asymptotic eventual accepted-family surface wrapper is available. -/
def check_magnificationStyleNoSmallDAG_surface_of_eventuallyAcceptedFamily :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      (∀ β : Rat, 0 < β → β < β0 →
        ∃ nAcc : Nat, ∀ n ≥ nAcc, SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε) →
      MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound) :=
  magnificationStyleNoSmallDAG_surface_of_eventuallyAcceptedFamily

/-- Asymptotic eventual promise-YES surface wrapper is available. -/
def check_magnificationStyleNoSmallDAG_surface_of_eventuallyPromiseYesSubcube :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      (∀ β : Rat, 0 < β → β < β0 →
        ∃ nYes : Nat, ∀ n ≥ nYes, SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε) →
      MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound) :=
  magnificationStyleNoSmallDAG_surface_of_eventuallyPromiseYesSubcube

/--
Q3 bridge skeleton (witness-level): slice-indexed strict `InPpolyDAG` witnesses
compile into explicit `SmallDAGSolver` witnesses for all `(n,β,ε)`.
-/
def check_smallDAGSolver_of_inPpolyDAGFamilyOnSlices :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β))),
      ∀ n : Nat, ∀ β ε : Rat,
        SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
  smallDAGSolver_of_inPpolyDAGFamilyOnSlices

/--
Q3 bridge skeleton (membership-level): per-slice `PpolyDAG` assumptions are
lifted to strict witnesses and then to `SmallDAGSolver`.
-/
def check_smallDAGSolver_of_PpolyDAGOnSlices :
    ∀ (F : GapSliceFamily)
      (hDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.PpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β))),
      let hInDag := inPpolyDAGFamilyOnSlices_of_PpolyDAG F hDag
      ∀ n : Nat, ∀ β ε : Rat,
        SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
  smallDAGSolver_of_PpolyDAGOnSlices

/--
Eventual strict-witness family bridge exposes the canonical eventual
`SmallDAGSolver` surface.
-/
def check_eventuallySmallDAGSolverSurface_of_eventuallyInPpolyDAGWitnessFamily :
    ∀ (F : GapSliceFamily)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      EventuallyInPpolyDAGWitnessFamily F β0 →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_of_eventuallyInPpolyDAGWitnessFamily

/--
Eventual proposition-level witness family bridge also lands at the same
eventual `SmallDAGSolver` surface.
-/
def check_eventuallySmallDAGSolverSurface_of_eventuallyPpolyDAGWitnessFamily :
    ∀ (F : GapSliceFamily)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      EventuallyPpolyDAGWitnessFamily F β0 →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_of_eventuallyPpolyDAGWitnessFamily

/--
Global-language bridge package and transport theorem are available with expected
types (single-global witness -> slice-wise `PpolyDAG`).
-/
def check_ppolyDAGOnSlices_of_globalWitness :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F),
      ComplexityInterfaces.PpolyDAG bridge.L →
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.PpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)) :=
  ppolyDAGOnSlices_of_globalWitness

/--
Global `PpolyDAG` witness bridge to eventual `SmallDAGSolver` surface is
available with expected type.
-/
def check_eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      ComplexityInterfaces.PpolyDAG bridge.L →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness

/--
FinalResult exports the thin wrapper for the new global-witness bridge.
-/
def check_eventuallySmallDAGSolverSurface_surface_of_globalPpolyDAGWitness :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      ComplexityInterfaces.PpolyDAG bridge.L →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_surface_of_globalPpolyDAGWitness

/--
Global contradiction schema in lower-bounds bridge layer is available.
-/
def check_not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNoSmall :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ ε : Rat, 0 < ε ∧
            ∃ β0 : Rat, 0 < β0 ∧
              ∀ β : Rat, 0 < β → β < β0 →
                ∃ n0 : Nat, ∀ n ≥ n0,
                  ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies

/--
FinalResult exports the same contradiction schema as a thin boundary wrapper.
-/
def check_not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNoSmall :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ ε : Rat, 0 < ε ∧
            ∃ β0 : Rat, 0 < β0 ∧
              ∀ β : Rat, 0 < β → β < β0 →
                ∃ n0 : Nat, ∀ n ≥ n0,
                  ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies

/--
Concrete accepted-family weak-route contradiction theorem is available.
-/
def check_not_globalPpolyDAG_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_of_acceptedFamilyWeakRoute

/--
Concrete promise-YES weak-route contradiction theorem is available.
-/
def check_not_globalPpolyDAG_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_of_promiseYesWeakRoute

/--
Accepted-family weak route + NP witness closure to class-level separation is
available.
-/
def check_NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute

/--
Promise-YES weak route + NP witness closure to class-level separation is
available.
-/
def check_NP_not_subset_PpolyDAG_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_promiseYesWeakRoute

/--
G1 Route-A item (2) gate wrapper is available with the expected type:
provider-family assumptions specialized to canonical `ppolyDAG` size bounds
compile to the accepted-family source theorem schema.
-/
def check_gateG1_routeA2_acceptedFamily_of_providerFamily :
    ∀ (F : GapSliceFamily)
      (_hAccepted :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          acceptedFamilyCertificateAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA2_acceptedFamily_of_providerFamily

/--
G1 Route-A item (1) gate wrapper is available with the expected type:
provider-family assumptions specialized to canonical `ppolyDAG` size bounds
compile to the promise-YES source theorem schema.
-/
def check_gateG1_routeA1_promiseYes_of_providerFamily :
    ∀ (F : GapSliceFamily)
      (_hYes :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          promiseYesSubcubeCertificateAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesPromiseYesSubcubeStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA1_promiseYes_of_providerFamily

/--
Concrete Route-A.2 G1 compiler from restriction-certificate-data families is
available with the expected type.
-/
def check_gateG1_routeA2_acceptedFamily_of_restrictionDataFamily :
    ∀ (F : GapSliceFamily)
      (_hData :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGWitnessRestrictionCertificateDataProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA2_acceptedFamily_of_restrictionDataFamily

/--
Concrete Route-A.2 G1 compiler from extraction+numeric source families is
available with the expected type.
-/
def check_gateG1_routeA2_acceptedFamily_of_restrictionExtractionAndNumericFamily :
    ∀ (F : GapSliceFamily)
      (_hExtract :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGWitnessRestrictionExtractionProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag))
      (_hNumeric :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGWitnessRestrictionNumericDataProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)
            (_hExtract hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA2_acceptedFamily_of_restrictionExtractionAndNumericFamily

/--
Concrete Route-A.1 G1 compiler from promise/value package families is available
with the expected type.
-/
def check_gateG1_routeA1_promiseYes_of_packageFamily :
    ∀ (F : GapSliceFamily)
      (_hPkg :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          promiseValueLocalityPackageAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesPromiseYesSubcubeStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA1_promiseYes_of_packageFamily

/--
FinalResult exports the accepted-family weak-route contradiction wrapper.
-/
def check_not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute

/--
FinalResult exports the promise-YES weak-route contradiction wrapper.
-/
def check_not_globalPpolyDAG_surface_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_promiseYesWeakRoute

/--
FinalResult exports the PRG-image weak-route contradiction wrapper.
-/
def check_not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hPrgWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          prgImageAcceptanceAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute

/--
FinalResult exports the stronger restriction-extraction+numeric fallback
contradiction wrapper via the same bridge template.
-/
def check_not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hFallbackWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ hExtract :
            smallDAGWitnessRestrictionExtractionProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag),
            smallDAGWitnessRestrictionNumericDataProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag) hExtract),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute

/--
FinalResult exports accepted-family weak-route class-level separation wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute

/--
FinalResult exports promise-YES weak-route class-level separation wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_promiseYesWeakRoute

/--
FinalResult exports PRG-image weak-route class-level separation wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_prgImageAcceptanceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hPrgWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          prgImageAcceptanceAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_prgImageAcceptanceWeakRoute

/--
FinalResult exports stronger restriction-extraction+numeric fallback class-level
separation wrapper via the shared bridge template.
-/
def check_NP_not_subset_PpolyDAG_surface_of_restrictionExtractionNumericWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hFallbackWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ hExtract :
            smallDAGWitnessRestrictionExtractionProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag),
            smallDAGWitnessRestrictionNumericDataProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag) hExtract),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_restrictionExtractionNumericWeakRoute

end Pnp3.Tests
