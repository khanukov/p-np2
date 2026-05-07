import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter
import Magnification.AuditRoutes.LogWidthAdversary.Composition

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

/-- The concrete `prefixAnd` syntax contains no OR gates. -/
theorem orGateCount_prefixAnd (n k : Nat) (h : k ≤ n) :
    orGateCount (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd n k h) = 0 := by
  induction k with
  | zero => simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, orGateCount]
  | succ k ih =>
      simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, orGateCount, ih]


/-- The concrete `prefixAnd` syntax contains no NOT gates. -/
theorem notGateCount_prefixAnd (n k : Nat) (h : k ≤ n) :
    notGateCount (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd n k h) = 0 := by
  induction k with
  | zero => simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, notGateCount]
  | succ k ih =>
      simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, notGateCount, ih]

/-- The concrete `adversaryWitness_v_natlog2` is rejected by V2-A Phase 2. -/
theorem excludes_adversaryWitness_v_natlog2 :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2 := by
  intro hFilter
  obtain ⟨_hUnbounded, _hGate, _hDepth, hMix⟩ := hFilter
  have hSupport : 2 ≤ (FormulaCircuit.support
      (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2.family 3)).card := by
    rw [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2]
    rw [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2_support_card]
    rw [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.logWidthNat]
    rw [Nat.le_log2 (by decide : 4 ≠ 0)]
  have hOrPos := (hMix 3 hSupport).1
  have hOrZero : orGateCount
      (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2.family 3) = 0 := by
    simp [Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2,
      Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.adversaryFamily_v_natlog2,
      orGateCount_prefixAnd]
  rw [hOrZero] at hOrPos
  exact Nat.lt_irrefl 0 hOrPos

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
