import Magnification.FinalResultMainline

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open Complexity
open ComplexityInterfaces

/-!
Thin DAG weak-route wrappers (active mainline surface):

- source theorem target:
  `SmallDAGImpliesPromiseYesSubcubeAt` / `SmallDAGImpliesPromiseYesSubcubeStatement`
- weak terminal consumer:
  `SmallDAGImpliesAcceptedFamilyAt` / `SmallDAGImpliesAcceptedFamilyStatement`
- asymptotic no-small-DAG endpoint:
  `MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound)`.

These wrappers intentionally keep the final file oriented to the weak accepted-family
route without forcing the stronger restriction-provider contracts as the only
frontier.
-/

/--
Final-surface wrapper: global no-small-DAG closure from the weak accepted-family
statement.

This is the theorem-level bridge used by the new weak mainline:
`AcceptedFamilyCertificateAt` is treated as terminal consumer, and the closure
to per-slice impossibility of small DAG solvers is entirely mechanical.
-/
theorem noSmallDAG_surface_of_acceptedFamilyStatement
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hAccepted : LowerBounds.SmallDAGImpliesAcceptedFamilyStatement F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.no_dag_solver_of_acceptedFamily F SizeBound hAccepted

/--
Final-surface wrapper: global no-small-DAG closure from the one-sided YES-centered
source statement.

This keeps the nearest-term source target explicit in `FinalResult`:
`SmallDAGImpliesPromiseYesSubcubeStatement` is reduced immediately to the same
no-solver endpoint.
-/
theorem noSmallDAG_surface_of_promiseYesSubcubeStatement
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hYes : LowerBounds.SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.no_dag_solver_of_promise_yes_subcube F SizeBound hYes

/--
Final-surface wrapper for the parallel structured-image backup route:

`PRGImageAcceptanceAt provider -> no small DAG solver`.

This keeps the backup producer compiled at the same endpoint level as the
promise-YES and accepted-family mainline wrappers.
-/
theorem noSmallDAG_surface_of_prgImageAcceptanceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hPrg : LowerBounds.prgImageAcceptanceAtProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_prgImageAcceptanceAtProviderOnSlices F SizeBound hPrg

/--
Final-surface wrapper for distributional easy-image PRG providers, with
internal counting closure and explicit epsilon-smallness side condition.
-/
theorem noSmallDAG_surface_of_easyImagePRGAtProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hEasy : LowerBounds.easyImagePRGAtProviderOnSlices F SizeBound)
  (hEpsSmall :
    ∀ n : Nat, ∀ β ε : Rat,
      ∀ W : LowerBounds.SmallDAGWitnessOnSlice
        (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
        (hEasy n β ε W).epsilon <
          1 - ((Models.circuitCountBound (F.paramsOf n β).n
                  ((F.paramsOf n β).sNO - 1) : Rat) /
                (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat))) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_easyImagePRGAtProviderOnSlices
    F SizeBound hEasy hEpsSmall

/--
Final-surface wrapper from source-level easy-image fooling providers.
-/
theorem noSmallDAG_surface_of_smallDAGEasyImageFoolingSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hSource : LowerBounds.smallDAGEasyImageFoolingSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGEasyImageFoolingSourceProviderOnSlices
    F SizeBound hSource

/-- Final-surface wrapper for the minimal canonical distributional source. -/
theorem noSmallDAG_surface_of_smallDAGEasyDistSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hSource : LowerBounds.smallDAGEasyDistSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGEasyDistSourceProviderOnSlices
    F SizeBound hSource

/--
Final-surface wrapper for one-sided easy-HSG source providers.

This is the preferred weak mainline endpoint because downstream contradiction
uses only one-sided lower transfer.
-/
theorem noSmallDAG_surface_of_smallDAGEasyHSGSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hSource : LowerBounds.smallDAGEasyHSGSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices
    F SizeBound hSource

/--
Final-surface wrapper from upstream average-case/hardness source providers.
-/
theorem noSmallDAG_surface_of_smallDAGAverageCaseHardnessSourceProviderOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hAvg : LowerBounds.smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact LowerBounds.noSmallDAG_of_smallDAGAverageCaseHardnessSourceProviderOnSlices
    F SizeBound hAvg

/--
Final-surface wrapper for the strong restriction/shrinkage fallback stack.

This theorem intentionally routes the stronger extraction+numerics contract into
the same weak accepted-family terminal closure, so the fallback remains
compatible with the weak mainline rather than reintroducing a separate endpoint.
-/
theorem noSmallDAG_surface_of_restrictionFallbackOnSlices
  (F : LowerBounds.GapSliceFamily)
  (SizeBound : Nat → Rat → Rat → Nat → Prop)
  (hExtract : LowerBounds.smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound)
  (hNumeric :
    LowerBounds.smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract) :
  ∀ n : Nat, ∀ β ε : Rat, ¬ LowerBounds.SmallDAGSolver F SizeBound n β ε := by
  exact
    LowerBounds.noSmallDAG_of_restrictionExtractionAndNumericProviderOnSlices_via_acceptedFamily
      F SizeBound hExtract hNumeric

/--
Asymptotic weak-route wrapper from eventual accepted-family production.
-/
theorem magnificationStyleNoSmallDAG_surface_of_eventuallyAcceptedFamily
    (F : LowerBounds.GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hEventuallyAccepted :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nAcc : Nat, ∀ n ≥ nAcc, LowerBounds.SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε) :
    LowerBounds.MagnificationStyleNoSmallDAG (LowerBounds.SmallDAGSolver F SizeBound) := by
  exact LowerBounds.magnificationStyleNoSmallDAG_of_eventually_acceptedFamily
    F SizeBound ε β0 hε hβ0 hEventuallyAccepted

/--
Asymptotic weak-route wrapper from eventual one-sided YES-subcube production.
-/
theorem magnificationStyleNoSmallDAG_surface_of_eventuallyPromiseYesSubcube
    (F : LowerBounds.GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hEventuallyYes :
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ nYes : Nat, ∀ n ≥ nYes, LowerBounds.SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε) :
    LowerBounds.MagnificationStyleNoSmallDAG (LowerBounds.SmallDAGSolver F SizeBound) := by
  exact LowerBounds.magnificationStyleNoSmallDAG_of_eventually_promiseYesSubcube
    F SizeBound ε β0 hε hβ0 hEventuallyYes

/--
Thin bridge wrapper (variant-1 style): a single global `PpolyDAG` witness on an
asymptotic language `bridge.L` implies the eventual small-solver surface for
the chosen slice family `F`.

This wrapper intentionally stops at `EventuallySmallDAGSolverSurface`; it does
not yet claim DAG separation by itself.  Its purpose is to expose the new
global-to-slice quantifier plumbing at the `FinalResult` boundary.
-/
theorem eventuallySmallDAGSolverSurface_surface_of_globalPpolyDAGWitness
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (ε β0 : Rat)
    (hε : 0 < ε)
    (hβ0 : 0 < β0)
    (hDagGlobal : ComplexityInterfaces.PpolyDAG bridge.L) :
    LowerBounds.EventuallySmallDAGSolverSurface F := by
  exact LowerBounds.eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness
    F bridge ε β0 hε hβ0 hDagGlobal

/--
Thin contradiction wrapper at the global-witness bridge boundary:
if magnification-style no-small-solver is available uniformly for every
canonical witness-derived size-bound family, then the bridged global language
cannot belong to `PpolyDAG`.

This theorem keeps the result bridge-local (`¬ PpolyDAG bridge.L`) and avoids
claiming full class separation prematurely.
-/
theorem not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNoSmall :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, ∀ n ≥ n0,
                ¬ LowerBounds.SmallDAGSolver
                    F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) n β ε) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    LowerBounds.not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      F bridge hNoSmall

/--
Thin bridge-local contradiction wrapper instantiated with the weak
accepted-family source theorem.
-/
theorem not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hAcceptedWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesAcceptedFamilyStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    LowerBounds.not_globalPpolyDAG_of_acceptedFamilyWeakRoute
      F bridge hAcceptedWeak

/--
Thin bridge-local contradiction wrapper instantiated with the nearer-term
promise-YES weak source theorem.
-/
theorem not_globalPpolyDAG_surface_of_promiseYesWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesPromiseYesSubcubeStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    LowerBounds.not_globalPpolyDAG_of_promiseYesWeakRoute
      F bridge hYesWeak

/--
Thin bridge-local contradiction wrapper instantiated with the PRG-image
accepted-image route.

This follows exactly the same bridge template as the accepted-family/promise-YES
wrappers: we first collapse the stronger source-side producer to the weak
accepted-family statement, then reuse the canonical bridge-local contradiction
schema without adding any new quantifier plumbing.
-/
theorem not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hPrgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.prgImageAcceptanceAtProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_acceptedFamilyWeakRoute
      F bridge ?_
  intro hInDag
  exact
    LowerBounds.smallDAGAcceptedFamilyStatement_of_prgImageAcceptanceProvider
      F
      (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
      (hPrgWeak hInDag)

/--
Thin bridge-local contradiction wrapper instantiated with the distributional
easy-image PRG route (plus epsilon-smallness side condition).
-/
theorem not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      F bridge ?_
  intro hInDag
  refine ⟨(1 / 4 : Rat), by positivity, (1 / 2 : Rat), by positivity, ?_⟩
  intro β hβPos hβLt
  refine ⟨0, ?_⟩
  intro n hn
  exact LowerBounds.noSmallDAG_of_smallDAGEasyDistSourceProviderOnSlices
    F
    (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
    (hEasyWeak hInDag)
    n β (1 / 4)

/--
Thin bridge-local contradiction wrapper instantiated with the one-sided easy-HSG
weak route.
-/
theorem not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyHSGWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies
      F bridge ?_
  intro hInDag
  refine ⟨(1 / 4 : Rat), by positivity, (1 / 2 : Rat), by positivity, ?_⟩
  intro β hβPos hβLt
  refine ⟨0, ?_⟩
  intro n hn
  exact LowerBounds.noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices
    F
    (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
    (hEasyHSGWeak hInDag)
    n β (1 / 4)

/--
Weak-route wrapper directly from upstream average-case/hardness sources.
-/
theorem not_globalPpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hAvgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGAverageCaseHardnessSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge
      (fun hInDag =>
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource
          F
          (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
          (hAvgWeak hInDag))

/--
Thin bridge-local contradiction wrapper instantiated with the stronger
restriction-extraction+numeric fallback route.

The route is intentionally wired through the same accepted-family bridge schema
to avoid introducing another endpoint-specific contradiction theorem.
-/
theorem not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hFallbackWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ hExtract :
          LowerBounds.smallDAGWitnessRestrictionExtractionProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag),
          LowerBounds.smallDAGWitnessRestrictionNumericDataProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) hExtract) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  refine
    LowerBounds.not_globalPpolyDAG_of_acceptedFamilyWeakRoute
      F bridge ?_
  intro hInDag
  rcases hFallbackWeak hInDag with ⟨hExtract, hNumeric⟩
  exact
    LowerBounds.smallDAGAcceptedFamilyStatement_of_restrictionExtractionAndNumericProvider
      F
      (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
      hExtract
      hNumeric

/--
Class-level wrapper: accepted-family weak route + explicit NP witness on
`bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hAcceptedWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesAcceptedFamilyStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    LowerBounds.NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute
      F bridge hNP hAcceptedWeak

/--
Fallback class-level wrapper from the canonical support-half family.

This packages the old Route-A2 accepted-family fallback into the asymptotic
bridge endpoint without restating the accepted-family weak-route plumbing.
-/
theorem not_globalPpolyDAG_surface_of_supportHalfBoundFamily
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : LowerBounds.SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute
      F bridge
      (LowerBounds.gateG1_routeA2_acceptedFamily_of_supportHalfBoundFamily
        F hSupportHalf)

/--
Fallback class-level wrapper from the canonical support-half family to
`NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hSupportHalf :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : LowerBounds.SmallDAGWitnessOnSlice
            (F.paramsOf n β)
            (fun ε' s => LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag n β ε' s) ε,
            (DagCircuit.support W.C).card ≤
              Models.Partial.tableLen (F.paramsOf n β).n / 2) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute
      F bridge hNP
      (LowerBounds.gateG1_routeA2_acceptedFamily_of_supportHalfBoundFamily
        F hSupportHalf)

/--
Class-level wrapper: promise-YES weak route + explicit NP witness on
`bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_promiseYesWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hYesWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.SmallDAGImpliesPromiseYesSubcubeStatement
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    LowerBounds.NP_not_subset_PpolyDAG_of_promiseYesWeakRoute
      F bridge hNP hYesWeak

/--
Class-level wrapper: PRG-image accepted-image weak route + explicit NP witness
on `bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_prgImageAcceptanceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hPrgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.prgImageAcceptanceAtProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute
      F bridge hPrgWeak

/--
Class-level wrapper: distributional easy-image PRG weak route + explicit NP
witness on `bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_easyImagePRGWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
      F bridge hEasyWeak

/--
Backward-compatible alias (old name) to the source-first weak-route wrapper.
-/
theorem not_globalPpolyDAG_surface_of_easyImagePRGWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
      F bridge hEasyWeak

/--
Renamed source-first class-level wrapper.
-/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_surface_of_easyImagePRGWeakRoute
      F bridge hNP hEasyWeak

/--
Class-level wrapper from one-sided easy-HSG weak route.
-/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyHSGWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge hEasyHSGWeak

/--
Class-level wrapper directly from upstream average-case/hardness weak route.
-/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hAvgWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGAverageCaseHardnessSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge hNP
      (fun hInDag =>
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource
          F
          (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
          (hAvgWeak hInDag))

/-- Backward-compatible alias under previous source-wrapper name. -/
theorem not_globalPpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute F bridge hEasyWeak

/-- Backward-compatible alias under previous source-wrapper name. -/
theorem NP_not_subset_PpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hEasyWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        LowerBounds.smallDAGEasyDistSourceProviderOnSlices
          F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute F bridge hNP hEasyWeak

/--
Bridge from the single canonical source-theorem debt to global non-inclusion.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyImageSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_easyImage_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute
      F bridge hCanonical

/--
Bridge from the canonical one-sided easy-HSG source debt to global
non-inclusion.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyHSGSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_easyHSG_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute
      F bridge
      (fun hInDag =>
        LowerBounds.smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyHSGSourceProviderOnSlices
          F
          (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag)
          (hCanonical hInDag))

/--
Bridge from canonical easy-density source debt to global non-inclusion.

This is the density-first mainline wrapper: density debt is compiled to the
canonical one-sided easy-HSG debt internally, then the existing HSG closure is
reused unchanged.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_easyDensity_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyHSGSourceDebt
      F bridge
      (LowerBounds.canonical_smallDAG_easyHSG_source_on_slices_of_canonical_smallDAG_easyDensity_source_on_slices
        F hCanonical)

/--
Bridge from witness-indexed canonical easy-density debt to global non-inclusion.

Compared with
`not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt`,
this route bypasses the all-circuits density object and uses the witness-level
transfer closure directly.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_witnessEasyDensity_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  have hNoSmall :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ ε : Rat, 0 < ε ∧
          ∃ β0 : Rat, 0 < β0 ∧
            ∀ β : Rat, 0 < β → β < β0 →
              ∃ n0 : Nat, ∀ n ≥ n0,
                ¬ LowerBounds.SmallDAGSolver
                    F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) n β ε := by
    intro hInDag
    refine ⟨(1 / 8 : Rat), by norm_num, (1 : Rat), by norm_num, ?_⟩
    intro β hβ hβlt
    refine ⟨0, ?_⟩
    intro n hn
    exact
      (LowerBounds.noSmallDAG_of_canonical_smallDAG_witnessEasyDensity_source_on_slices
        F hCanonical hInDag n β (1 / 8 : Rat))
  exact
    not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies
      F bridge hNoSmall

/--
Bridge from canonical average-case/hardness source debt to global contradiction.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGAvgHardnessSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hCanonical : LowerBounds.canonical_smallDAG_avgHardness_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute
      F bridge hCanonical

/--
Density-first class-level wrapper:
canonical easy-density source debt + NP witness on `bridge.L` imply
`NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hCanonical : LowerBounds.canonical_smallDAG_easyDensity_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt
      F bridge hCanonical

/--
Density-first class-level wrapper for the witness-indexed canonical debt:
if we can prove witness-indexed canonical easy-density sources on all slices,
then together with an NP witness on `bridge.L` we derive
`NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hCanonical : LowerBounds.canonical_smallDAG_witnessEasyDensity_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
      F bridge hCanonical

/--
Bridge from witness-uniform-lower canonical debt to global non-inclusion.

This theorem is a thin composition:
`witnessUniformLower` debt -> witness-easy-density debt -> global contradiction.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hUniform : LowerBounds.canonical_smallDAG_witnessUniformLower_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt
      F bridge
      (LowerBounds.canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower
        F hUniform)

/--
Class-level wrapper from witness-uniform-lower canonical debt.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hUniform : LowerBounds.canonical_smallDAG_witnessUniformLower_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
      F bridge hUniform

/--
Bridge from quarter-bounded witness-transfer debt to global non-inclusion.
-/
theorem not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hQuarterTr : LowerBounds.canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :
    ¬ ComplexityInterfaces.PpolyDAG bridge.L := by
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt
      F bridge
      (LowerBounds.canonical_smallDAG_witnessUniformLower_source_on_slices_of_witnessTransferQuarter
        F hQuarterTr)

/--
Class-level wrapper from quarter-bounded witness-transfer debt.
-/
theorem NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hQuarterTr : LowerBounds.canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt
      F bridge hQuarterTr

/--
Class-level wrapper: stronger restriction-extraction+numeric fallback route +
explicit NP witness on `bridge.L` gives `NP_not_subset_PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_surface_of_restrictionExtractionNumericWeakRoute
    (F : LowerBounds.GapSliceFamily)
    (bridge : LowerBounds.AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hFallbackWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        ∃ hExtract :
          LowerBounds.smallDAGWitnessRestrictionExtractionProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag),
          LowerBounds.smallDAGWitnessRestrictionNumericDataProviderOnSlices
            F (LowerBounds.ppolyDAGSizeBoundOnSlices F hInDag) hExtract) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  refine ⟨bridge.L, hNP, ?_⟩
  exact
    not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute
      F bridge hFallbackWeak


end Magnification
end Pnp3
