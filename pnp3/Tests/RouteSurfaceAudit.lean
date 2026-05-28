import Magnification.FinalResult

/-!
# Route Surface Audit

Compile-time checks for the public final-result surface.

The purpose of this file is narrow: prevent the historical refuted
support-bounds route from quietly becoming the apparent public final path
again.  The active frontier should be exactly a `ResearchGapWitness`, whose
only mathematical payload is `NP_not_subset_PpolyDAG`.

Legacy/magnification endpoints may still exist, but they must stay under
explicit audit/compatibility names.
-/

namespace Pnp3.Tests

open Pnp3

namespace RouteSurfaceAudit

/-! ## Active public frontier -/

/--
The public DAG endpoint has the honest gap boundary: a `ResearchGapWitness`,
not `MagnificationAssumptions` or a support-bounds contract.
-/
def check_public_NP_not_subset_PpolyDAG_final_surface :
    Magnification.ResearchGapWitness →
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  Magnification.NP_not_subset_PpolyDAG_final

/--
The public `P ≠ NP` endpoint has the same honest gap boundary.
-/
def check_public_P_ne_NP_final_surface :
    Magnification.ResearchGapWitness →
      ComplexityInterfaces.P_ne_NP :=
  Magnification.P_ne_NP_final

/--
Closing raw DAG separation is enough to inhabit the single remaining research
gap witness.
-/
def check_researchGapWitness_from_raw_dag_separation :
    ComplexityInterfaces.NP_not_subset_PpolyDAG →
      Magnification.ResearchGapWitness :=
  fun hDag => { dagSeparation := hDag }

/--
The final theorem can be closed from raw DAG separation and the internally
compiled `P ⊆ P/polyDAG` bridge.
-/
def check_public_P_ne_NP_final_from_raw_dag_separation :
    ComplexityInterfaces.NP_not_subset_PpolyDAG →
      ComplexityInterfaces.P_ne_NP :=
  fun hDag =>
    Magnification.P_ne_NP_final
      { dagSeparation := hDag }

/-! ## Clean anti-checker integration routes -/

/--
The canonical eventual route is available through `AntiCheckerAssumptions`
alone, without requiring the legacy `MagnificationAssumptions` package.
-/
def check_isoStrongRoute_antiChecker_surface :
    ∀ (anti : Magnification.AntiCheckerAssumptions),
      Magnification.AsymptoticIsoStrongRoute anti.asymptotic →
        ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker

/--
The promise-YES route is also available through the anti-checker package alone.
-/
def check_promiseYesCertificateRoute_antiChecker_surface :
    ∀ (anti : Magnification.AntiCheckerAssumptions),
      Magnification.AsymptoticPromiseYesCertificateRoute anti.asymptotic →
        ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker

/--
The shortest fixed-slice-collapse integration route has an anti-checker-only
surface.
-/
def check_fixedSliceCollapse_antiChecker_surface :
    ∀ (anti : Magnification.AntiCheckerAssumptions)
      (n : Nat)
      (hn : anti.asymptotic.N0 ≤ n),
      (ComplexityInterfaces.PpolyDAG
          (Models.gapPartialMCSP_Language (anti.asymptotic.pAt n hn)) → False) →
        ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse_withAntiChecker

/--
Fixed-slice source routes are exposed through the anti-checker package alone;
legacy `MagnificationAssumptions` wrappers live in audit routes.
-/
def check_fixedSlicePromiseYes_antiChecker_surface :
    ∀ (anti : Magnification.AntiCheckerAssumptions)
      (n : Nat)
      (hn : anti.asymptotic.N0 ≤ n),
      Magnification.FixedSlicePromiseYesCertificateRoute
        (anti.asymptotic.pAt n hn) →
        ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute_withAntiChecker

/--
Route-B blocker integration also has an anti-checker-only surface.
-/
def check_blocker_antiChecker_surface :
    ∀ (anti : Magnification.AntiCheckerAssumptions)
      (n : Nat)
      (hn : anti.asymptotic.N0 ≤ n),
      LowerBounds.dagRouteBSourceBlocker
        (anti.asymptotic.pAt n hn) →
        ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_blocker_withAntiChecker

/-! ## Legacy surfaces stay explicit -/

/--
The package-shaped magnification route is still present only under an explicit
compatibility/audit name.
-/
def check_legacy_magnification_surface_is_explicitly_named :
    Magnification.MagnificationAssumptions →
      ComplexityInterfaces.P_ne_NP :=
  Magnification.RefutedRoute_P_ne_NP_final_of_magnification

/--
The refuted support-bounds input is still present only under an explicit
compatibility/audit name.
-/
def check_legacy_supportBounds_surface_is_explicitly_named :
    Magnification.FormulaSupportRestrictionBoundsPartial →
      Magnification.AsymptoticFormulaTrackData →
        ComplexityInterfaces.P_ne_NP :=
  Magnification.RefutedRoute_P_ne_NP_final_of_supportBounds

/--
The old fixed-slice package-shaped route is retained only under its legacy
audit name; mainline callers should use the `_withAntiChecker` variant.
-/
def check_legacy_fixedSlice_package_surface_is_explicitly_named :
    ∀ (hMag : Magnification.MagnificationAssumptions)
      (n : Nat)
      (hn : hMag.antiChecker.asymptotic.N0 ≤ n),
      (ComplexityInterfaces.PpolyDAG
          (Models.gapPartialMCSP_Language
            (hMag.antiChecker.asymptotic.pAt n hn)) → False) →
        ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  Magnification.RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse

end RouteSurfaceAudit

end Pnp3.Tests
