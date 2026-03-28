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
FinalResult exports PRG-image weak-route contradiction wrapper.
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
FinalResult exports stronger-fallback weak-route contradiction wrapper.
-/
def check_not_globalPpolyDAG_surface_of_restrictionFallbackWeakRoute :
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
  not_globalPpolyDAG_surface_of_restrictionFallbackWeakRoute

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
FinalResult exports stronger-fallback weak-route class-level separation wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_restrictionFallbackWeakRoute :
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
  NP_not_subset_PpolyDAG_surface_of_restrictionFallbackWeakRoute

end Pnp3.Tests
