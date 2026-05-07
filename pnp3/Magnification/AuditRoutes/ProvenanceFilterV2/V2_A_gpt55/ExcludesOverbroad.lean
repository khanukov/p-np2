import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter
import Magnification.AuditRoutes.FixedParamsProbe

/-!
# V2-A Phase 2: bounded-support / overbroad-hardwiring exclusion

Progress classification: side-track audit formalization.  This file proves a
local exclusion theorem for the bounded-support hardwiring shape behind
NOGO-000001; it does not claim to refute every possible overbroad provenance
assumption.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces
open FormulaShape

/--
Any record whose displayed formulas have uniformly bounded support is rejected
by the Phase-2 V2-A filter.  This is the precise Lean-level overbroad
hardwiring hook: the fixed-slice truth-table witness from NOGO-000001 has this
bounded-support shape.
-/
theorem excludes_bounded_support
    {L : Language} (w : InPpolyFormula L) (B : Nat)
    (hBound : ∀ n : Nat, (FormulaCircuit.support (w.family n)).card ≤ B)
    (hNotConst : ¬ ∀ n : Nat, w.family n = FormulaCircuit.const false) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter w := by
  intro hFilter
  obtain ⟨hSupport, _hGate, _hDepth, _hAndFree⟩ := hFilter
  rcases hSupport with hUnbounded | hConst
  · obtain ⟨n, hn⟩ := hUnbounded B
    exact Nat.not_lt_of_ge (hBound n) hn
  · exact hNotConst hConst

/--
A convenient corollary for witnesses with a uniformly bounded polynomial-size
cap.  This matches the concrete NOGO-000001 fixed-slice hardwiring witness
shape: support is bounded by formula size, formula size is bounded by the
record's `polyBound`, and `polyBound` is bounded by a constant.
-/
theorem excludes_uniform_polyBound
    {L : Language} (w : InPpolyFormula L) (B : Nat)
    (hBound : ∀ n : Nat, w.polyBound n ≤ B)
    (hNotConst : ¬ ∀ n : Nat, w.family n = FormulaCircuit.const false) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter w := by
  apply excludes_bounded_support w B ?_ hNotConst
  intro n
  exact Nat.le_trans (FormulaCircuit.support_card_le_size (w.family n))
    (Nat.le_trans (w.family_size_le n) (hBound n))

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
