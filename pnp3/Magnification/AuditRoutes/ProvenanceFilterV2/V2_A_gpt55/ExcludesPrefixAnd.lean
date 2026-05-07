import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter
import Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2

/-!
# V2-A Phase 2: prefix-AND exclusion

Progress classification: side-track audit formalization.  The theorem targets
the concrete Nat.log2 prefix-AND witness from the log-width audit route.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces
open FormulaShape

/-- Exact AND-gate count for the concrete `prefixAnd` syntax. -/
theorem andGateCount_prefixAnd (n k : Nat) (h : k ≤ n) :
    andGateCount (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd n k h) = k := by
  induction k with
  | zero => simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, andGateCount]
  | succ k ih =>
      simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, andGateCount, ih]

/-- At length `3`, the Nat.log2 prefix-AND adversary has an AND gate. -/
theorem one_le_andGateCount_adversaryFamily_v_natlog2_at_three :
    1 ≤ andGateCount (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2 3) := by
  simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.logWidthNat,
    andGateCount_prefixAnd]
  rw [Nat.le_log2 (by decide : 4 ≠ 0)]
  norm_num

/-- The concrete `adversaryWitness_v_natlog2` is rejected by V2-A Phase 2. -/
theorem excludes_adversaryWitness_v_natlog2 :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2 := by
  intro hFilter
  obtain ⟨_hUnbounded, _hGate, _hDepth, hAndFree⟩ := hFilter
  have hZero := hAndFree 3
  have hZero' : andGateCount
      (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2 3) = 0 := by
    simpa [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2] using hZero
  have hPos := one_le_andGateCount_adversaryFamily_v_natlog2_at_three
  rw [hZero'] at hPos
  exact Nat.not_succ_le_zero 0 hPos

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
