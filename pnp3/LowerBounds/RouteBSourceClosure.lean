import LowerBounds.DAGStableRestrictionProducer
import LowerBounds.SingletonDensityContradiction

namespace Pnp3
namespace LowerBounds

open ComplexityInterfaces
open Models

/-!
`RouteBSourceClosure` contains the **active Route-B source interfaces** used by
final wrappers:

* named blocker proposition,
* compact closure package,
* canonical maps from blocker to closure and to DAG-separation endpoints.

This file intentionally avoids audit-side impossibility facts; those are kept in
`FailedRoute_FixedSliceSupportHalfImpossible` to reduce conceptual mixing.
-/

/--
Route-B source blocker, isolated as one named proposition.

If this obligation is discharged, the DAG-side invariant provider is obtained by
existing machinery (`dagStableRestrictionInvariantProvider_of_supportHalfObligation`).
Keeping this name localizes the remaining source-side debt in one place.
-/
abbrev dagRouteBSourceBlocker (p : GapPartialMCSPParams) : Prop :=
  gapPartialMCSP_supportHalfObligation p

/--
A compact package for the Route-B source-side closure object.

This structure is intentionally small and local: we store only the theorem that
feeds the existing DAG stable-restriction pipeline, and we keep all endpoint
wrappers outside of the source module.
-/
structure DAGRouteBSourceClosure (p : GapPartialMCSPParams) : Type where
  /-- Uniform DAG-side locality invariant provider for `gapPartialMCSP`. -/
  invariantProvider : dagStableRestrictionInvariantProvider p

/--
Canonical constructor from the named Route-B blocker.

This is the intended "single gate" interface for source-side work: proving
`dagRouteBSourceBlocker p` immediately yields the invariant provider package.
-/
noncomputable def dagRouteBSourceClosure_of_blocker
    {p : GapPartialMCSPParams}
    (hBlocker : dagRouteBSourceBlocker p) :
    DAGRouteBSourceClosure p := by
  refine ⟨?_⟩
  exact dagStableRestrictionInvariantProvider_of_supportHalfObligation
    (p := p) hBlocker

/--
One-way packaging lemma: discharging the named Route-B blocker immediately
produces a nonempty localized source-closure package.

The converse is intentionally not claimed: `DAGRouteBSourceClosure` is a
potentially weaker source contract than the specific support-half blocker.
-/
theorem nonempty_sourceClosure_of_dagRouteBSourceBlocker
    {p : GapPartialMCSPParams}
    (hBlocker : dagRouteBSourceBlocker p) :
    Nonempty (DAGRouteBSourceClosure p) := by
  exact ⟨dagRouteBSourceClosure_of_blocker (p := p) hBlocker⟩

/--
Expose the canonical stable-restriction producer from the localized Route-B
closure package.
-/
theorem dag_stableRestriction_producer_of_sourceClosure
    {p : GapPartialMCSPParams}
    (hSrc : DAGRouteBSourceClosure p) :
    dag_stableRestriction_producer p := by
  exact dag_stableRestriction_producer_of_invariantProvider hSrc.invariantProvider

/--
DAG separation endpoint from the localized Route-B source closure.
-/
theorem NP_not_subset_PpolyDAG_of_sourceClosure_TM
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hSrc : DAGRouteBSourceClosure p) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_of_invariantProvider_TM W hSrc.invariantProvider

/--
Direct Route-B theorem endpoint from the named blocker gate, without explicitly
passing the intermediate closure package.
-/
theorem NP_not_subset_PpolyDAG_of_blocker_TM
    {p : GapPartialMCSPParams}
    (W : Models.GapPartialMCSP_TMWitness p)
    (hBlocker : dagRouteBSourceBlocker p) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  exact NP_not_subset_PpolyDAG_of_sourceClosure_TM W
    (dagRouteBSourceClosure_of_blocker (p := p) hBlocker)

end LowerBounds
end Pnp3
