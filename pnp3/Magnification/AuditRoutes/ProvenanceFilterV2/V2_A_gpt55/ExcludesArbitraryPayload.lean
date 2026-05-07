import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Witness

/-!
# V2-A Phase 2: arbitrary truth-table payload exclusion

Progress classification: side-track audit formalization.  The theorem targets
the concrete `rename (ttFormula payload)` syntax from NOGO-000006.  Unlike the
prefix-AND exclusion, this uses the restored Phase-1 linear gate-count cap: at a
fixed length where the logarithmic payload width is `6`, the truth-table syntax
already has too many Boolean gates for support size `6`.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces
open FormulaShape

/-- At ambient length `64`, the arbitrary-payload width is exactly `6`. -/
theorem widthFn_sixtyFour :
    Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.widthFn 64 = 6 := by
  rw [Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.widthFn, Nat.log2_eq_log_two]
  rw [Nat.log_eq_iff (Or.inl (by decide : 6 ≠ 0))]
  norm_num

/-- Exact Boolean-gate count for the arbitrary payload family at length `64`. -/
theorem booleanGateCount_adversaryFamily_v_arbpayload_at_sixtyFour
    (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily) :
    booleanGateCount
        (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryFamily_v_arbpayload F 64) =
      252 := by
  unfold Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryFamily_v_arbpayload
  rw [booleanGateCount_rename]
  rw [booleanGateCount_ttFormula]
  rw [widthFn_sixtyFour]
  norm_num

/-- The concrete arbitrary all-essential truth-table payload witness is rejected. -/
theorem excludes_adversaryWitness_v_arbpayload
    (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
    (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
      (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload F hF) := by
  intro hFilter
  obtain ⟨_hUnbounded, hGate, _hDepth, _hMix⟩ := hFilter
  have hGate64 := hGate 64
  have hSupport : (FormulaCircuit.support
      ((Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload F hF).family 64)).card = 6 := by
    rw [Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload]
    rw [Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryFamily_v_arbpayload_support_card F hF 64]
    exact widthFn_sixtyFour
  have hCount : booleanGateCount
      ((Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload F hF).family 64) = 252 := by
    rw [Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.adversaryWitness_v_arbpayload]
    exact booleanGateCount_adversaryFamily_v_arbpayload_at_sixtyFour F
  rw [hSupport, hCount] at hGate64
  norm_num at hGate64

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
