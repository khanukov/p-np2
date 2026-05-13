import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NaturalProofsSelfTest.RepresentationSensitivity
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.AdversarialRobustness.RewriteAttack

/-!
# Smoke test for the V2-A landing artifacts (fp3b3.1 + fp3b3.2)

This module verifies that the kernel-checked V2-A landing artifacts —
representation-sensitivity self-test (fp3b3.1) and adversarial rewrite
attack (fp3b3.2) — remain elaborable through the build.  Companion to
`pnp3/Tests/AuditRoutes_SupportCardinalityBarrier_Smoke.lean`.
-/

namespace Pnp3
namespace Tests

open Pnp3.Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55

#check NaturalProofsSelfTest.doubleNotPad
#check NaturalProofsSelfTest.paddedSeededPrefixAndFamily
#check NaturalProofsSelfTest.paddedSeededPrefixAndWitness
#check NaturalProofsSelfTest.paddedSeededPrefixAndWitness_rejected
#check NaturalProofsSelfTest.v2A_same_language_different_representation
#check NaturalProofsSelfTest.v2A_not_extensional_on_witness_representations

#check AdversarialRobustness.rewritePrefixAndFamily
#check AdversarialRobustness.rewritePrefixAndFamily_eval_eq
#check AdversarialRobustness.rewritePrefixAndWitness
#check AdversarialRobustness.rewritePrefixAndWitness_admitted
#check AdversarialRobustness.v2A_rewrite_attack_prefixAnd

/-- Smoke theorem: the V2-A landing artifacts are wired in. -/
theorem v2a_landing_artifacts_smoke_loaded : True := trivial

end Tests
end Pnp3
