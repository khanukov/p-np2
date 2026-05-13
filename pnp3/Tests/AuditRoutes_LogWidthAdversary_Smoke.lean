import Magnification.AuditRoutes.LogWidthAdversary.Composition
-- Composition pulls in Width_NatLog2 / Family_NatLog2 / Diversity_*
-- transitively; the parallel realisations and S3 retry need explicit
-- imports below for the smoke #checks to see them.
import Magnification.AuditRoutes.LogWidthAdversary.Width_PowOfTwoSlice
import Magnification.AuditRoutes.LogWidthAdversary.TTFormulaSizeBound
import Magnification.AuditRoutes.LogWidthAdversary.Family_PowOfTwoSlice

/-!
# Log-width adversary smoke regression

S10/S11-merged smoke for `seed_packs/fp3b1_log_width_hardwiring_lift/`.

Pinpoints the canonical names exposed by the parallel-engineer
decomposition + the integration composition so any future refactor
that accidentally renames or removes one fails `lake build PnP3`
immediately.

This is NOT a proof of any new statement.  It is a name-existence +
type-existence regression for the audit-route surface.
-/

namespace Pnp3
namespace Tests
namespace AuditRoutesLogWidthAdversarySmoke

-- Width helpers (S1, S2).
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.logWidth_le
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.logWidth_unbounded
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.logWidth_lt_self
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.k_pow2_le
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.k_pow2_unbounded
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.k_pow2_lt_self

-- ttFormula size bound (S3 retry; not on the canonical Path A but still
-- a durable artifact).
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.ttFormula_size_le

-- Diversity reducers (S8 retry, S9).
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.adversary_support_unbounded
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.adversary_support_below_n_io

-- Adversary family (S6 = canonical Path A).
#check @Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2
#check @Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2

-- Adversary family (S7 = parallel realisation, Path B).  Wired but not
-- used by the canonical composition.
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.adversaryFamily_v_pow2
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.adversaryWitness_v_pow2

-- Composition outputs (S11).
#check @Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd_support_card
#check @Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2_support_card
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.adversaryWitness_v_natlog2_support_unbounded
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.adversaryWitness_v_natlog2_support_below_n_io

-- The headline theorem: log-width adversary satisfies the
-- InSupportFunctionalDiversity filter, refuting the FP-3 candidate.
#check @Pnp3.Magnification.AuditRoutes.LogWidthAdversary.logWidthAdversary_satisfies_diversity

theorem logwidth_adversary_smoke_loaded : True := trivial

end AuditRoutesLogWidthAdversarySmoke
end Tests
end Pnp3
