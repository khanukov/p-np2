import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesOverbroad
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesPrefixAnd
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesArbitraryPayload
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NotSupportCardinalityOnly

/-!
# V2-A Phase 2 survivor surface

Progress classification: side-track audit formalization.  This integration file
collects the Phase-2 exclusion, non-support-cardinality-only, and non-vacuity
surfaces for review.  It intentionally does **not** promote V2-A to an accepted
provenance guard and introduces no source theorem, `gap_from` bridge, candidate,
or final endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces

/-- Single review surface collecting the V2-A Phase-2 theorem names. -/
theorem v2_A_gpt55_phase2_survivor_surface :
    (¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
          @ProvenanceFilter_v2_V2_A_gpt55_Filter) ∧
    (∀ {L : Language} (w : InPpolyFormula L) (B : Nat),
      (∀ n : Nat, (FormulaCircuit.support (w.family n)).card ≤ B) →
        ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter w) ∧
    (¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
        Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2) ∧
    (∀ (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
        (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F),
        ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
          (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload F hF)) ∧
    ProvenanceFilter_v2_V2_A_gpt55_Filter seededPrefixAndWitness := by
  exact ⟨ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only,
    excludes_bounded_support,
    excludes_adversaryWitness_v_natlog2,
    excludes_adversaryWitness_v_arbpayload,
    seededPrefixAndWitness_admitted⟩

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
