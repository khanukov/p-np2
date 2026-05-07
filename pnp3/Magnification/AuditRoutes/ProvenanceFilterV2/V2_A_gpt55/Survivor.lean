import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesOverbroad
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesPrefixAnd
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesArbitraryPayload
import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NonVacuity

/-!
# V2-A Phase 2 survivor surface

Progress classification: side-track audit formalization.  This integration file
collects the Phase-2 exclusion and non-vacuity surfaces for review; it does not
promote the filter to an accepted provenance guard.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

/-- Single review surface collecting the V2-A Phase-2 theorem names. -/
theorem v2_A_gpt55_phase2_survivor_surface :
    (¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
        Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2) ∧
    (∀ (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
        (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F),
        ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
          (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload F hF)) ∧
    ProvenanceFilter_v2_V2_A_gpt55_Filter honestConstFalseWitness := by
  exact ⟨excludes_adversaryWitness_v_natlog2,
    excludes_adversaryWitness_v_arbpayload,
    honestConstFalseWitness_admitted⟩

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
