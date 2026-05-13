import Magnification.AuditRoutes.SupportCardinalityBarrier.InSupportFunctionalDiversityApplication

/-!
# Smoke test for the support-cardinality barrier audit route

This module intentionally contains only surface checks.  It verifies that the
T1--T6 support-cardinality barrier artifacts are available through the build and
that the final T6 application theorem remains elaborable.
-/

namespace Pnp3
namespace Tests

open Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier

#check canonicalHardwiringFamily
#check canonicalHardwiringFamily_support_card
#check canonicalHardwiringWitness
#check IsSupportCardinalityOnly
#check support_cardinality_barrier
#check inSupportFunctionalDiversity_is_support_cardinality_only
#check any_honest_sublinear_support_witness_has_hardwiring_twin

/-- Smoke theorem: the support-cardinality barrier audit route is wired in. -/
theorem support_cardinality_barrier_smoke_loaded : True := trivial

end Tests
end Pnp3
