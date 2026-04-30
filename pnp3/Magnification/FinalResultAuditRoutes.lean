import Magnification.FinalResultMainline

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ComplexityInterfaces

/-!
# Final-result audit and compatibility routes

This module contains legacy final-result wrappers that intentionally route
through refuted support-bounds/provider-backed surfaces.  They are retained so
historical call sites and audits keep compiling, while `FinalResultMainline`
can stay focused on the cleaner anti-checker and DAG integration surfaces.

The active public boundary for unconditional work remains
`Magnification.UnconditionalResearchGap`, where `P_ne_NP_final` takes a
`ResearchGapWitness`.
-/

/--
Fixed-slice DAG collapse from formula-track support bounds.

No DAG-to-formula bridge is assumed here.  On the fixed
`gapPartialMCSP_Language p` slice, a DAG witness is constructively unfolded into
the explicit truth-table formula supplied by
`Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`.

Legacy/audit status: `FormulaSupportRestrictionBoundsPartial` is itself a
refuted support-bounds surface, so this theorem is not a non-vacuous path to
unconditional DAG separation.
-/
theorem fixedSliceCollapse_of_supportBounds
  {p : GapPartialMCSPParams}
  (hBounds : FormulaSupportRestrictionBoundsPartial) :
  ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) → False := by
  exact
    LowerBounds.not_ppolyDAG_of_dag_stableRestriction
      (LowerBounds.dag_stableRestriction_producer_alias_of_supportBounds
        hBounds)

/--
Asymptotic DAG separation from the fixed-slice support-bounds route.

This route uses the already-internalized formula-track multiswitching payload
and the constructive fixed-slice DAG-to-formula conversion.

Legacy/audit status: the support-bounds payload is refuted.  This endpoint is
kept for compatibility with historical call sites, not as an active research
target.
-/
theorem RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptotic_supportBounds
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  apply NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
    (anti := hMag.antiChecker) (n := n) (hn := hn)
  exact
    fixedSliceCollapse_of_supportBounds
      (hBounds := formula_support_bounds_from_multiswitching
        hMag.switching.multiswitching)

/--
Legacy support-bounds DAG-separation compatibility theorem.

The proof chooses the threshold slice `n = N0` and feeds the historical
support-bounds package through the constructive fixed-slice DAG-to-formula
bridge plus the stable-restriction consumer.

Audit status: `hMag.switching.multiswitching` is a refuted support-bounds
surface.  The public active final boundary is
`UnconditionalResearchGap.P_ne_NP_final`, which requires `ResearchGapWitness`
instead of this legacy package.
-/
theorem RefutedRoute_NP_not_subset_PpolyDAG_final_with_magnification
  (hMag : MagnificationAssumptions) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  let n : Nat := hMag.antiChecker.asymptotic.N0
  have hn : hMag.antiChecker.asymptotic.N0 ≤ n := le_rfl
  exact
    RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptotic_supportBounds
      (hMag := hMag)
      (n := n)
      (hn := hn)

/-! ## Legacy package-shaped wrappers around anti-checker DAG routes

These names are retained for import stability.  Each proof immediately projects
`hMag.antiChecker` and delegates to the mainline anti-checker-only theorem.
Because the visible package `MagnificationAssumptions` still contains the
refuted switching field, these wrappers live in the audit module rather than in
`FinalResultMainline`.
-/

/-- Legacy package-shaped wrapper for the canonical eventual DAG route. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withMagnification
  (hMag : MagnificationAssumptions)
  (hIso : AsymptoticIsoStrongRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker
      (anti := hMag.antiChecker) hIso

/-- Legacy package-shaped companion `P ≠ NP` endpoint. -/
theorem P_ne_NP_final_of_asymptotic_isoStrongRoute
  (hMag : MagnificationAssumptions)
  (hIso : AsymptoticIsoStrongRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker
      (anti := hMag.antiChecker) hIso

/-- Legacy package-shaped wrapper for the promise-YES-certificate route. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withMagnification
  (hMag : MagnificationAssumptions)
  (hRoute : AsymptoticPromiseYesCertificateRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) hRoute

/-- Legacy package-shaped companion for the promise-YES-certificate route. -/
theorem P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute
  (hMag : MagnificationAssumptions)
  (hRoute : AsymptoticPromiseYesCertificateRoute hMag.antiChecker.asymptotic) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) hRoute

/-- Legacy package-shaped wrapper for one fixed-slice collapse. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (hMag.antiChecker.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hCollapseFixed

/-- Legacy package-shaped companion for one fixed-slice collapse. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceCollapse
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hCollapseFixed :
    ComplexityInterfaces.PpolyDAG
      (gapPartialMCSP_Language (hMag.antiChecker.asymptotic.pAt n hn)) → False) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceCollapse_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hCollapseFixed

/-- Legacy package-shaped wrapper for the fixed-slice promise-YES route. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSlicePromiseYesCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for the fixed-slice promise-YES route. -/
theorem P_ne_NP_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSlicePromiseYesCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSlicePromiseYesCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for the promise/value locality route. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseValueLocalityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hPkg :
    FixedSlicePromiseValueLocalityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSlicePromiseValueLocalityRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hPkg

/-- Legacy package-shaped companion for the promise/value locality route. -/
theorem P_ne_NP_final_of_asymptotic_fixedSlicePromiseValueLocalityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hPkg :
    FixedSlicePromiseValueLocalityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSlicePromiseValueLocalityRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hPkg

/-- Legacy package-shaped wrapper for support-half/value-supported fallback. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportHalfValueSupportedRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportHalfValueSupportedRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportHalfValueSupportedRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for support-half/value-supported fallback. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceSupportHalfValueSupportedRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportHalfValueSupportedRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceSupportHalfValueSupportedRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for strong-fallback slack. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceDAGStableRestrictionSlackRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for strong-fallback slack. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceDAGStableRestrictionSlackRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceDAGStableRestrictionSlackRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for shrinkage certificates. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceShrinkageCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceShrinkageCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceShrinkageCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for shrinkage certificates. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceShrinkageCertificateRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceShrinkageCertificateRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceShrinkageCertificateRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for restriction data. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceRestrictionDataRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceRestrictionDataRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceRestrictionDataRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for restriction data. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceRestrictionDataRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceRestrictionDataRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceRestrictionDataRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for support-numeric data. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for support-numeric data. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceSupportNumericRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceSupportNumericRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for support-component inequalities. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericComponentRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericComponentRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceSupportNumericComponentRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for support-component inequalities. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceSupportNumericComponentRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceSupportNumericComponentRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceSupportNumericComponentRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for quarter-bounded transfer. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceTransferQuarterRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceTransferQuarterRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceTransferQuarterRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped companion for quarter-bounded transfer. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceTransferQuarterRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hRoute :
    FixedSliceTransferQuarterRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceTransferQuarterRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hRoute

/-- Legacy package-shaped wrapper for witness-indexed easy density. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessEasyDensityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hDensity :
    FixedSliceWitnessEasyDensityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessEasyDensityRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hDensity

/-- Legacy package-shaped companion for witness-indexed easy density. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceWitnessEasyDensityRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hDensity :
    FixedSliceWitnessEasyDensityRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceWitnessEasyDensityRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hDensity

/-- Legacy package-shaped wrapper for witness-uniform lower bounds. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessUniformLowerRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hUniform :
    FixedSliceWitnessUniformLowerRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceWitnessUniformLowerRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hUniform

/-- Legacy package-shaped companion for witness-uniform lower bounds. -/
theorem P_ne_NP_final_of_asymptotic_fixedSliceWitnessUniformLowerRoute
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hUniform :
    FixedSliceWitnessUniformLowerRoute
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_fixedSliceWitnessUniformLowerRoute_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hUniform

/-- Legacy package-shaped wrapper for stable-restriction producers. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hStable :
    LowerBounds.dag_stableRestriction_producer
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hStable

/-- Legacy package-shaped companion for stable-restriction producers. -/
theorem P_ne_NP_final_of_asymptotic_dag_stableRestriction
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hStable :
    LowerBounds.dag_stableRestriction_producer
      (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_dag_stableRestriction_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hStable

/-- Legacy package-shaped wrapper for source-closure packages. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hSrc : LowerBounds.DAGRouteBSourceClosure (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hSrc

/-- Legacy package-shaped companion for source-closure packages. -/
theorem P_ne_NP_final_of_asymptotic_sourceClosure
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hSrc : LowerBounds.DAGRouteBSourceClosure (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_sourceClosure_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hSrc

/-- Legacy package-shaped wrapper for Route-B blockers. -/
theorem NP_not_subset_PpolyDAG_final_of_asymptotic_blocker
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hBlocker :
    LowerBounds.dagRouteBSourceBlocker (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_blocker_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hBlocker

/-- Legacy package-shaped companion for Route-B blockers. -/
theorem P_ne_NP_final_of_asymptotic_blocker
  (hMag : MagnificationAssumptions)
  (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
  (hBlocker :
    LowerBounds.dagRouteBSourceBlocker (hMag.antiChecker.asymptotic.pAt n hn)) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_asymptotic_blocker_withAntiChecker
      (anti := hMag.antiChecker) (n := n) (hn := hn) hBlocker

/--
Compatibility DAG-separation API with an explicit asymptotic NP pullback.

The multiswitching-data endpoint below uses `AsymptoticFormulaTrackData`,
so the NP pullback is constructed
internally from a concrete TM witness.  This theorem keeps the old lower-level
shape available for callers that still have a pre-packaged
`AsymptoticFormulaTrackHypothesis`.

Legacy/audit status: `hMS` is `FormulaSupportBoundsFromMultiSwitchingContract`,
a refuted support-bounds surface.
-/
theorem RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptoticPullback
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  -- Repackage the three explicit inputs into the historical compatibility
  -- bundle and reuse the already-audited internal closure proof.
  let hMag : MagnificationAssumptions :=
    { switching := { multiswitching := hMS }
      antiChecker :=
        { asymptotic := hAsym
          npBridge := hNPbridge } }
  exact RefutedRoute_NP_not_subset_PpolyDAG_final_with_magnification hMag

/--
Legacy multiswitching-data DAG-separation API.

The visible asymptotic-side input is now constructive source data.  The
asymptotic slice hypothesis and NP pullback are derived internally via
`asymptoticFormulaTrackHypothesis_of_data` and `asymptoticNPPullback_of_data`.

This endpoint is intentionally no longer named `NP_not_subset_PpolyDAG_final`,
because its `hMS` input is a refuted support-bounds surface.  The public final
name is reserved for the research-gap route in `UnconditionalResearchGap`.
-/
theorem RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (D : AsymptoticFormulaTrackData) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptoticPullback
      hMS
      (asymptoticFormulaTrackHypothesis_of_data D)
      (asymptoticNPPullback_of_data D)

/-! ### Step 6 (session 68) — fixed-params DAG final, all assumptions explicit

The compatibility endpoint
`RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptoticPullback` above takes
`FormulaSupportBoundsFromMultiSwitchingContract`, which was proven
formally inconsistent in audit Probe 4
(`Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:~315`).  The
session 66 pipeline replacement was also shown ex-falso in Probe 7.

Session 67 introduced the stronger
`FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb`, which
takes `ac0 : AC0Parameters` as a Prop parameter (not per-formula).
Probe 8 (session 68) documents that:

1. The Probe 7 singleton-provider attack does NOT syntactically port
   to `fixedParams` (ac0 is externally given, cannot be fitted to
   formula).
2. `fixedParams ac0 sb → FormulaSupportRestrictionBoundsPartial` is
   NOT derivable without an auxiliary `uniformProvenance` hypothesis
   (Probe 8a makes the reduction conditional on uniform-ac0 provenance
   per formula).

The fixed-params DAG final below makes BOTH hypotheses explicit:
- `hBoundsP`: the strengthened fixed-params support-bounds contract.
- `hUniformProv`: uniform AC0 provenance for every formula witness,
  matching the given `ac0`.

**Research status**: the conjunction `hBoundsP ∧ hUniformProv` reduces
(via Probe 8a + Probe 3) back to `False`.  So the conjunction cannot
be established for the same `ac0, sb` simultaneously — exactly ONE of
them must be false for realistic AC0 parameters.

This theorem is **named as the single-research-level bottleneck**:
closing it requires formalizing a version of AC0 multi-switching that
commits to uniform parameters AND produces the polylog support bounds
AND is consistent with known `MCSP ∉ AC⁰` intuition.  That formal
content is the research-open gap.  **This theorem exposes the gap, it
does not bridge it.** -/
theorem RefutedRoute_NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance
  (ac0 : ThirdPartyFacts.AC0Parameters)
  (sb : Nat → Nat)
  (hBoundsP : FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb)
  (hUniformProv :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      ∃ (F : Core.Family ac0.n) (hsame : ac0.n = Models.partialInputLen p),
        ThirdPartyFacts.AC0FamilyWitnessProp ac0 F ∧
        Nonempty (ThirdPartyFacts.AC0MultiSwitchingWitness ac0 F) ∧
        (∃ f : Core.BitVec ac0.n → Bool, f ∈ F ∧
          ∀ x : Core.BitVec ac0.n,
            f x = ComplexityInterfaces.FormulaCircuit.eval
              ((Classical.choose hFormula).family (Models.partialInputLen p))
              (ThirdPartyFacts.castBitVec hsame x)))
  (D : AsymptoticFormulaTrackData) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  -- Bridge: fixedParams + uniformProvenance → old FormulaSupportRestrictionBoundsPartial.
  -- This is the path that audit Probe 8a formalizes.  The old
  -- predicate is then consumed by the legacy multi-switching-contract
  -- route, which Probe 4/5 show is ex-falso.  So the PROOF below
  -- still routes through an inconsistent intermediate.  The THEOREM is
  -- valuable only as a gap-exposing signature: with the current broad
  -- `hUniformProv` shape, the pair of assumptions reconstructs the old false
  -- predicate, so a future legitimate source must be narrower than this API.
  have hBoundsOld : FormulaSupportRestrictionBoundsPartial := by
    intro p' hFormula'
    obtain ⟨F, hsame, hAC0, hMSWit, hSem⟩ := hUniformProv (p := p') hFormula'
    exact hBoundsP (p := p') F hsame hAC0 hMSWit hFormula' hSem
  -- Construct the old multi-switching contract from the old predicate
  -- (structural: the multi-switching contract IS the ∀ form with
  -- fitted semantics, which we can synthesize via the internal
  -- singleton provider for SOME ac0).
  --
  -- IMPORTANT: this route is exactly what Probes 3-5 showed to be
  -- inconsistent.  The placeholder-free chain below reuses the legacy
  -- closure so that the theorem's signature makes the research gap visible:
  -- the current `hBoundsP + hUniformProv` pair is intentionally too strong and
  -- collapses back to ex-falso.
  let hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract :=
    multiswitching_contract_of_semantic_provider_and_support_bounds
      AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal
      hBoundsOld
  exact RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D

/--
Compatibility wrapper preserving the historical package-shaped DAG endpoint.

Legacy/audit status: this consumes `MagnificationAssumptions`, whose switching
field carries the refuted multiswitching support-bounds contract.
-/
theorem RefutedRoute_NP_not_subset_PpolyDAG_final_of_magnification
  (hMag : MagnificationAssumptions) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  RefutedRoute_NP_not_subset_PpolyDAG_final_with_magnification hMag

/--
Compatibility `P ≠ NP` endpoint with an explicit asymptotic NP pullback.

The multiswitching-data `P != NP` endpoint below uses
`AsymptoticFormulaTrackData`; this theorem preserves the old explicit-pullback
shape for historical wrappers.

Legacy/audit status: `hMS` is a refuted support-bounds surface.
-/
theorem RefutedRoute_P_ne_NP_final_of_asymptoticPullback
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (RefutedRoute_NP_not_subset_PpolyDAG_final_of_asymptoticPullback hMS hAsym hNPbridge)

/--
Legacy multiswitching-data `P ≠ NP` endpoint.

Compared with the previous surface, the default theorem no longer exposes
`hNPbridge : AsymptoticNPPullback hAsym`; it derives the NP pullback from
`D.asymptoticNP_TM`.

This theorem is kept as an audit route.  Its `hMS` input is not an acceptable
unconditional source, so the public name `P_ne_NP_final` is reserved for the
research-gap endpoint in `UnconditionalResearchGap`.
-/
theorem RefutedRoute_P_ne_NP_final_of_multiswitchingData
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (D : AsymptoticFormulaTrackData) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData hMS D)

/--
Support-bounds endpoint that removes `hMS` from the public input surface.

The multi-switching contract is reconstructed internally from
`FormulaSupportRestrictionBoundsPartial` via
`multiswitching_contract_internalized_of_support_bounds`.

Legacy/audit status: `FormulaSupportRestrictionBoundsPartial` is refuted, so
this is an interface compatibility wrapper, not an active route.
-/
theorem RefutedRoute_NP_not_subset_PpolyDAG_final_of_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (D : AsymptoticFormulaTrackData) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact
    RefutedRoute_NP_not_subset_PpolyDAG_final_of_multiswitchingData
      (hMS := multiswitching_contract_internalized_of_support_bounds hBounds)
      (D := D)

/--
`P ≠ NP` endpoint with support-bounds input instead of explicit `hMS`.

Legacy/audit status: the support-bounds input is refuted; this theorem only
preserves the historical interface layer.
-/
theorem RefutedRoute_P_ne_NP_final_of_supportBounds
  (hBounds : FormulaSupportRestrictionBoundsPartial)
  (D : AsymptoticFormulaTrackData) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (RefutedRoute_NP_not_subset_PpolyDAG_final_of_supportBounds hBounds D)

/--
Compatibility wrapper preserving the historical package-shaped `P ≠ NP`
endpoint for callers that still pass `MagnificationAssumptions`.

Legacy/audit status: this consumes the refuted multiswitching support-bounds
contract inside `hMag.switching`.
-/
theorem RefutedRoute_P_ne_NP_final_of_magnification
  (hMag : MagnificationAssumptions) :
  ComplexityInterfaces.P_ne_NP :=
  RefutedRoute_P_ne_NP_final_of_asymptoticPullback
    hMag.switching.multiswitching
    hMag.antiChecker.asymptotic
    hMag.antiChecker.npBridge

/--
Legacy provider-style payload for the zero-argument compatibility endpoint.

Important honesty note:
this does **not** make the result unconditional by itself.  It only moves the
remaining payload from explicit theorem arguments into one auditable provider
interface.  The `hMS` field is the refuted multiswitching support-bounds
contract, so this provider surface is retained for audit/compatibility only.

Quarantine status (Research Governance v0.1, PR 2):
this provider channel is hereby renamed `VacuousFinalPayloadProvider` to
make its audit-only status visible at the type level.  Use of
`[VacuousFinalPayloadProvider]` is forbidden outside the audit/test/docs
tree by `scripts/check_typeclass_payload_quarantine.sh`.  See
`RESEARCH_CONSTITUTION.md` Rule 16 and `Phase0_Audit_Surface.md` §1.3.
-/
class VacuousFinalPayloadProvider : Type where
  hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract
  data : AsymptoticFormulaTrackData

/--
Asymptotic-side provider extracted out of `VacuousFinalPayloadProvider`
(historically `FinalPayloadProvider` before the PR 2 quarantine).

This isolates the non-formula residual payload as constructive source data, so
the formula-side part (`hMS`) can be reconstructed internally from
support-bounds default flags.
-/
class AsymptoticPayloadProvider : Type where
  data : AsymptoticFormulaTrackData

/--
Default-availability flag for constructive asymptotic formula-track data.

This is the asymptotic analogue of the formula-side default flags used in
`LocalityProvider_Partial`: it carries the slice source and its TM NP witness
together, so no separate `AsymptoticNPPullback` fact is needed.
-/
def hasDefaultAsymptoticFormulaTrackData : Prop :=
  Nonempty AsymptoticFormulaTrackData

/--
Extract constructive asymptotic formula-track data from its default flag.
-/
noncomputable def defaultAsymptoticFormulaTrackData
    (h : hasDefaultAsymptoticFormulaTrackData) :
    AsymptoticFormulaTrackData :=
  Classical.choice h

/--
Build the asymptotic payload provider from default constructive source data.

This removes the need for a separate theorem-level NP-pullback fact: the pullback
is derived from the TM witness inside `AsymptoticFormulaTrackData` at the final
endpoint.
-/
noncomputable instance asymptoticPayloadProvider_of_default_asymptoticData
    [hData : Fact hasDefaultAsymptoticFormulaTrackData] :
    AsymptoticPayloadProvider where
  data := defaultAsymptoticFormulaTrackData hData.out

/--
Build the full final payload from:
1) default formula-side support-bounds source, and
2) asymptotic-side provider payload.

Legacy/audit status: this reconstructs the refuted formula-side support-bounds
source at the final endpoint boundary.  Callers no longer pass `hMS`
explicitly, but the same refuted payload is still present through typeclass
resolution.

Quarantine status (Research Governance v0.1, PR 2): renamed from
`finalPayloadProvider_of_default_supportBounds` so that its
audit-only status is visible at the call site.
-/
instance vacuousFinalPayloadProvider_of_default_supportBounds
    [hAsymProv : AsymptoticPayloadProvider]
    [hBounds : Fact hasDefaultFormulaSupportRestrictionBoundsPartial] :
    VacuousFinalPayloadProvider where
  hMS :=
    multiswitching_contract_internalized_of_support_bounds
      (defaultFormulaSupportRestrictionBoundsPartial hBounds.out)
  data := hAsymProv.data

/--
Legacy zero-argument provider-backed endpoint.

This theorem removes explicit non-zero payload from the visible signature, but
the hidden `VacuousFinalPayloadProvider` still contains the refuted
support-bounds surface.  The active public frontier is
`UnconditionalResearchGap.P_ne_NP_final`, not this compatibility theorem.

Quarantine status (Research Governance v0.1, PR 2): the previous public
name `P_ne_NP` is replaced with `Vacuous_P_ne_NP_via_FinalPayloadProvider`
so that the typeclass-payload channel can no longer be mistaken for a
canonical final endpoint.  No backwards-compatibility alias is provided.
-/
theorem Vacuous_P_ne_NP_via_FinalPayloadProvider
    [payload : VacuousFinalPayloadProvider] :
  ComplexityInterfaces.P_ne_NP :=
  RefutedRoute_P_ne_NP_final_of_multiswitchingData payload.hMS payload.data

/--
Zero-argument endpoint under the default formula-side source policy.

Compared to `Vacuous_P_ne_NP_via_FinalPayloadProvider`, this variant no longer
requires explicit/opaque `hMS`: it is reconstructed internally from
`hasDefaultFormulaSupportRestrictionBoundsPartial`.

Legacy/audit status: the default formula-side source is the refuted
`FormulaSupportRestrictionBoundsPartial` surface.

Quarantine status (Research Governance v0.1, PR 2): renamed from
`P_ne_NP_of_default_formulaSource`.
-/
theorem Vacuous_P_ne_NP_via_DefaultFormulaSource
    [AsymptoticPayloadProvider]
    [Fact hasDefaultFormulaSupportRestrictionBoundsPartial] :
    ComplexityInterfaces.P_ne_NP :=
  Vacuous_P_ne_NP_via_FinalPayloadProvider

/--
Zero-argument endpoint under both default source policies:

1) formula-side source from support-bounds defaults, and
2) constructive asymptotic source data from theorem-level default flags.

Compared to `Vacuous_P_ne_NP_via_DefaultFormulaSource`, this variant no
longer requires an explicit `AsymptoticPayloadProvider` contract.

Legacy/audit status: it still depends on the refuted default formula-side
support-bounds source.

Quarantine status (Research Governance v0.1, PR 2): renamed from
`P_ne_NP_of_default_sources`.
-/
theorem Vacuous_P_ne_NP_via_DefaultSources
    [Fact hasDefaultFormulaSupportRestrictionBoundsPartial]
    [Fact hasDefaultAsymptoticFormulaTrackData] :
    ComplexityInterfaces.P_ne_NP :=
  Vacuous_P_ne_NP_via_DefaultFormulaSource

/--
Legacy provider-free compatibility endpoint from explicit constructive
asymptotic source data.

This theorem is the direct "next step" route requested for closure work:
`hAsym` and `hNPbridge` are not taken from provider classes.  They are built
internally from `AsymptoticFormulaTrackData`, while formula-side `hMS` is still
reconstructed from default support-bounds assumptions.

Legacy/audit status: the formula-side default support-bounds assumptions are
refuted, so this endpoint is not an active unconditional route.

Quarantine status (Research Governance v0.1, PR 2): renamed from
`P_ne_NP_of_constructive_asymptoticData`.
-/
theorem Vacuous_P_ne_NP_via_ConstructiveAsymptotic
    [hBounds : Fact hasDefaultFormulaSupportRestrictionBoundsPartial]
    (D : AsymptoticFormulaTrackData) :
    ComplexityInterfaces.P_ne_NP := by
  let hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract :=
    multiswitching_contract_internalized_of_support_bounds
      (defaultFormulaSupportRestrictionBoundsPartial hBounds.out)
  exact RefutedRoute_P_ne_NP_final_of_multiswitchingData hMS D

end Magnification
end Pnp3
