import Complexity.Interfaces

/-!
# Log-width adversary, slot S8: unbounded-support diversity reducer

This file contains the S8 component for the log-width hardwiring lift.  It is
intentionally parametric in the concrete adversary family: the S6/S7 packaging
slots choose the family, while this slot proves the tiny monotonicity argument
needed for the first diversity conjunct.

The result below says that if a proposed `InPpolyFormula` witness has support
cardinality at least some auxiliary width at every input length, and that width
is unbounded, then the witness support is itself unbounded.  Integration can
instantiate `width` with either the Nat-log window or the power-of-two-slice
window once the corresponding family-specific support lower bound is available.

This is audit-only side-track infrastructure for formalizing the FP-3b.2
log-width hardwiring obstruction.  It does not introduce a lower-bound bridge,
a source theorem, or any final complexity-separation endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces

/--
S8 reducer for the first diversity conjunct.

For a strict `InPpolyFormula` witness `w`, suppose an explicit width function is
pointwise bounded above by the syntactic support cardinality of `w.family n`.
If that width is unbounded, then the actual support cardinality is unbounded.

The log-width adversary integration slot should supply `hWidthBySupport` from
the concrete family support calculation and `hWidthUnbounded` from the chosen
width helper (`Nat.log2` or power-of-two-slice).  This theorem performs only the
kernel-checked monotonicity step, keeping S8 independent of the S6/S7 choice.
-/
theorem adversary_support_unbounded
    {L : Language} (w : InPpolyFormula L) (width : Nat → Nat)
    (hWidthBySupport :
      ∀ n : Nat, width n ≤ (FormulaCircuit.support (w.family n)).card)
    (hWidthUnbounded : ∀ B : Nat, ∃ n : Nat, B < width n) :
    ∀ B : Nat, ∃ n : Nat,
      B < (FormulaCircuit.support (w.family n)).card := by
  intro B
  rcases hWidthUnbounded B with ⟨n, hBWidth⟩
  exact ⟨n, Nat.lt_of_lt_of_le hBWidth (hWidthBySupport n)⟩

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
