import Magnification.FinalResultMainline

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open Complexity
open ComplexityInterfaces

/-!
Current DAG endpoint ledger for this file:

- `P_ne_NP_final` remains conditional on explicit DAG separation
  `hNPDag : NP_not_subset_PpolyDAG`.
- The stable-restriction, certificate-provider, invariant-provider, and
  support-bounds wrappers below are compiled stronger sufficient routes and
  compatibility/audit surfaces.
- The generic accepted-family weak endpoint is now already formalized at the
  slice level (`AcceptedFamilyCertificateAt`) and at the asymptotic barrier
  schema level (`SmallDAGImpliesAcceptedFamilyAt` /
  `SmallDAGImpliesAcceptedFamilyStatement`); the nearer-term chosen mainline
  theorem target is the one-sided promise-aware schema
  `SmallDAGImpliesPromiseYesSubcubeAt` /
  `SmallDAGImpliesPromiseYesSubcubeStatement`, and
  `YesSubcubeCertificateAt` is wired as a stronger structured producer into
  that route.
- This file now exposes thin asymptotic weak-route wrappers (`magnificationStyle*`)
  consuming eventual accepted-family / promise-YES-subcube statements directly.
  The remaining open step is the actual DAG-side source theorem producing those
  eventual statements from strict small-DAG semantics.
-/

/--
Final DAG-separation wrapper specialized to the stronger stable-restriction
route.

This wrapper is kept as a compiled sufficient condition and audit surface: if
one can prove that
every DAG solver for the fixed `gapPartialMCSP` slice yields a small stable
restriction for the canonical DAG payload, then the lower-bound layer already
produces `NP ⊄ PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload
        (LowerBounds.dagCanonicalPayload hDag)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_dag_stableRestriction_TM W hStable

/--
Final DAG-separation wrapper specialized to the new DAG-native Route-B
certificate provider.

Compared with `NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM`, this
form packages the source-side obligation as explicit per-DAG certificates
(`DAGStableRestrictionCertificate`) instead of raw probe witnesses. It remains
a stronger optional route rather than the intended theorem-minimal blocker.
-/
theorem NP_not_subset_PpolyDAG_final_of_certificateProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hCert : LowerBounds.dagStableRestrictionCertificateProvider p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_certificateProvider_TM W hCert

/--
End-to-end `P ≠ NP` wrapper specialized to the same DAG stable-restriction
producer obligation.

This remains a stronger compatibility wrapper. The roadmap does not treat the
producer-side proof of `hStable` as the only honest remaining theorem-level
blocker.
-/
theorem P_ne_NP_final_of_dag_stableRestriction_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.stableRestrictionGoal_of_abstractGapTargetedPayload
        (LowerBounds.dagCanonicalPayload hDag)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM W hStable)

/--
End-to-end `P ≠ NP` wrapper specialized to the DAG-native Route-B certificate
provider.
-/
theorem P_ne_NP_final_of_certificateProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hCert : LowerBounds.dagStableRestrictionCertificateProvider p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_certificateProvider_TM W hCert)

/--
Final DAG-separation wrapper specialized to a DAG-side locality-invariant
provider (the stronger Route-B source contract).
-/
theorem NP_not_subset_PpolyDAG_final_of_invariantProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hInv : LowerBounds.dagStableRestrictionInvariantProvider p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_invariantProvider_TM W hInv

/--
End-to-end `P ≠ NP` wrapper for the same DAG-side locality-invariant provider.
-/
theorem P_ne_NP_final_of_invariantProvider_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hInv : LowerBounds.dagStableRestrictionInvariantProvider p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_invariantProvider_TM W hInv)

/--
Final DAG-separation wrapper specialized to the localized Route-B source
closure package (`LowerBounds.DAGRouteBSourceClosure`).

This keeps the endpoint surface simple: all source-side DAG work is packaged in
one structure and consumed here without introducing additional endpoint APIs.
-/
theorem NP_not_subset_PpolyDAG_final_of_sourceClosure_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hSrc : LowerBounds.DAGRouteBSourceClosure p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_sourceClosure_TM W hSrc

/--
Companion `P ≠ NP` endpoint for the same localized Route-B source closure
package.
-/
theorem P_ne_NP_final_of_sourceClosure_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hSrc : LowerBounds.DAGRouteBSourceClosure p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_sourceClosure_TM W hSrc)

/--
Direct final DAG-separation wrapper from the named Route-B blocker gate.

This avoids exposing intermediate source packaging at call sites when one wants
to state end-to-end implications in blocker-first form.
-/
theorem NP_not_subset_PpolyDAG_final_of_blocker_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBlocker : LowerBounds.dagRouteBSourceBlocker p) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_blocker_TM W hBlocker

/--
Companion `P ≠ NP` final wrapper from the same named Route-B blocker gate.
-/
theorem P_ne_NP_final_of_blocker_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBlocker : LowerBounds.dagRouteBSourceBlocker p) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_blocker_TM W hBlocker)

/--
Final DAG-separation wrapper specialized to the support-bounds + DAG→formula
bridge route.

This is intentionally a thin endpoint around the new lower-bound closure lemma:
it does not add new assumptions beyond the support-bounds package and the
functional DAG→formula bridge.
-/
theorem NP_not_subset_PpolyDAG_final_of_supportBounds_and_dagToFormula_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial)
  (hDagToFormula :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact LowerBounds.NP_not_subset_PpolyDAG_of_supportBounds_and_dagToFormula_TM
    W hBounds hDagToFormula

/--
Companion `P ≠ NP` endpoint for the same support-bounds + DAG→formula route.
-/
theorem P_ne_NP_final_of_supportBounds_and_dagToFormula_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial)
  (hDagToFormula :
    ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_dag_only
    (NP_not_subset_PpolyDAG_final_of_supportBounds_and_dagToFormula_TM
      W hBounds hDagToFormula)


/--
Final DAG-separation wrapper specialized to the packaged stable-restriction
route.

Just like the lower-bound theorem below it, this is only a thin corollary of
the probe-form final route: packaged payloads are converted back to the single
probe obligation and the existing final theorem is reused unchanged.
-/
theorem NP_not_subset_PpolyDAG_final_of_dag_stableRestrictionPayload_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ _ : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.AbstractGapStableRestrictionPayload p)
  (hBase :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      (hStable hDag).base = LowerBounds.dagCanonicalPayload hDag) :
  ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM W
    (LowerBounds.dag_stableRestrictionGoal_of_stableRestrictionPayload
      hStable hBase)


/--
End-to-end `P ≠ NP` wrapper specialized to the packaged DAG stable-restriction
producer obligation.

Again this is just a thin corollary of the probe-form final route.
-/
theorem P_ne_NP_final_of_dag_stableRestrictionPayload_TM
  {p : GapPartialMCSPParams}
  (W : Models.GapPartialMCSP_TMWitness p)
  (hStable :
    ∀ _ : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      LowerBounds.AbstractGapStableRestrictionPayload p)
  (hBase :
    ∀ hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p),
      (hStable hDag).base = LowerBounds.dagCanonicalPayload hDag) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final_of_dag_stableRestriction_TM W
    (LowerBounds.dag_stableRestrictionGoal_of_stableRestrictionPayload
      hStable hBase)


end Magnification
end Pnp3
