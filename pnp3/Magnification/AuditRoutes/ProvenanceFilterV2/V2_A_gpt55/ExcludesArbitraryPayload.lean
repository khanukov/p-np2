import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Witness

/-!
# V2-A Phase 2: arbitrary truth-table payload exclusion

Progress classification: side-track audit formalization.  The theorem targets
the concrete `rename (ttFormula payload)` syntax from NOGO-000006.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces
open FormulaShape
open Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe

/-- The Phase-2 payload width at ambient length `1` is exactly one bit. -/
theorem widthFn_one : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.widthFn 1 = 1 := by
  rw [Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.widthFn, Nat.log2_eq_log_two, Nat.log_eq_one_iff]
  norm_num

/-- At length `1`, every arbitrary-payload witness contains an AND gate. -/
theorem one_le_andGateCount_adversaryFamily_v_arbpayload_at_one
    (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily) :
    1 ≤ andGateCount (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryFamily_v_arbpayload F 1) := by
  unfold Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryFamily_v_arbpayload
  rw [andGateCount_rename]
  have hposGen : ∀ {w : Nat}, w = 1 → (f : Bitstring w → Bool) →
      1 ≤ andGateCount (ttFormula f) := by
    intro w hw f
    cases hw
    exact one_le_andGateCount_ttFormula_succ (k := 0) f
  exact hposGen widthFn_one (F 1)

/-- The concrete arbitrary all-essential truth-table payload witness is rejected. -/
theorem excludes_adversaryWitness_v_arbpayload
    (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily) (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload F hF) := by
  intro hFilter
  obtain ⟨_hUnbounded, _hGate, _hDepth, hAndFree⟩ := hFilter
  have hZero := hAndFree 1
  have hZero' : andGateCount (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryFamily_v_arbpayload F 1) = 0 := by
    simpa [Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload] using hZero
  have hPos := one_le_andGateCount_adversaryFamily_v_arbpayload_at_one F
  rw [hZero'] at hPos
  exact Nat.not_succ_le_zero 0 hPos

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
