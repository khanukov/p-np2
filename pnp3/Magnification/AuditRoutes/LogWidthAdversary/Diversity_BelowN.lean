import Complexity.Interfaces

/-!
# Log-width adversary, slot S9: below-`n` diversity reducer

This file contains the S9 component for the log-width hardwiring lift.
It deliberately does not choose between the Nat-log and power-of-two-slice
families from the packaging slots.  Instead it records the small kernel-checked
step that S9 is responsible for: once a proposed adversary family has a support
cardinality bounded by an auxiliary width function, and that width is strictly
below the ambient input length infinitely often, the family itself satisfies the
"below `n` infinitely often" conjunct used by
`FP3Attempt.InSupportFunctionalDiversity`.

The theorem is intentionally parametric so the S11 integration worker can apply
it to either the S6 or S7 realization without duplicating this argument.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces

/--
S9 reducer for the second diversity conjunct.

For a strict `InPpolyFormula` witness `w`, suppose every support cardinality is
bounded by some explicit `width n`.  If that width is strictly smaller than the
ambient length for arbitrarily large `n`, then the actual support cardinality is
also strictly smaller than `n` for arbitrarily large `n`.

The log-width and power-of-two-slice adversary families are expected to provide
`hSupportByWidth` from their concrete support analysis and `hWidthBelowN` from
their width helper lemmas; this theorem performs the final monotonicity step.
-/
theorem adversary_support_below_n_io
    {L : Language} (w : InPpolyFormula L) (width : Nat → Nat)
    (hSupportByWidth :
      ∀ n : Nat, (FormulaCircuit.support (w.family n)).card ≤ width n)
    (hWidthBelowN : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ width n < n) :
    ∀ N : Nat, ∃ n : Nat,
      N ≤ n ∧ (FormulaCircuit.support (w.family n)).card < n := by
  intro N
  rcases hWidthBelowN N with ⟨n, hNn, hWidthLt⟩
  exact ⟨n, hNn, Nat.lt_of_le_of_lt (hSupportByWidth n) hWidthLt⟩

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
