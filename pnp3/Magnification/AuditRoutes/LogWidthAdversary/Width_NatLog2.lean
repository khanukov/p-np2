import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Log-width helper lemmas for the FP-3b.1 hardwiring lift

This module is the S1/T1.A contribution for
`seed_packs/fp3b1_log_width_hardwiring_lift`.  It isolates the small
arithmetic facts needed by the later log-width adversary construction:

* `logWidth_le`: `Nat.log2 (n + 1)` always fits inside an `n`-bit slice.
* `logWidth_unbounded`: the width function is unbounded.
* `logWidth_lt_self`: arbitrarily far out, the width is strictly below
  the ambient input length.

The file is deliberately arithmetic-only.  It does not define a family,
construct a lower-bound bridge, or touch any trust-root endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

/-- The logarithmic window `Nat.log2 (n + 1)` fits into the `n` available
coordinates.  The proof uses the strict floor-log bound
`Nat.log 2 (n + 1) < n + 1` and converts `< n + 1` to `≤ n`. -/
theorem logWidth_le (n : Nat) : Nat.log2 (n + 1) ≤ n := by
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_self 2 (Nat.succ_ne_zero n))

/-- The logarithmic width is unbounded: at length `2^(B+1)-1`, the
successor length is exactly `2^(B+1)`, so the base-two logarithm is
`B+1`. -/
theorem logWidth_unbounded (B : Nat) : ∃ n, B < Nat.log2 (n + 1) := by
  let n := 2 ^ (B + 1) - 1
  refine ⟨n, ?_⟩
  have hpos : 0 < 2 ^ (B + 1) := (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ (B + 1))
  have hsucc : n + 1 = 2 ^ (B + 1) := by
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  rw [hsucc, Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]
  exact Nat.lt_succ_self B

/-- A tiny exponential slack lemma used to pick lengths where the
logarithmic window is strictly below the ambient length.

The later theorem instantiates this at exponent `N + 6`; the extra
constant keeps the proof elementary and avoids any asymptotic library
machinery. -/
private theorem linear_slack_le_two_pow (N : Nat) : N + 8 ≤ 2 ^ (N + 6) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      calc
        N.succ + 8 = (N + 8) + 1 := by omega
        _ ≤ 2 * (N + 8) := by omega
        _ ≤ 2 * 2 ^ (N + 6) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (N + 7) := by
          rw [show N + 7 = N + 6 + 1 by omega, pow_succ]
          ring
        _ = 2 ^ (N.succ + 6) := by
          congr 1

/-- Arbitrarily far out, there is a length `n ≥ N` whose logarithmic
window is genuinely smaller than `n`.

We choose `n = 2^(N+6)-1`.  Its successor is a power of two, so the
logarithmic width is exactly `N+6`; the preceding slack lemma proves
`N+6 < 2^(N+6)-1`. -/
theorem logWidth_lt_self (N : Nat) :
    ∃ n, N ≤ n ∧ Nat.log2 (n + 1) < n := by
  let e := N + 6
  let n := 2 ^ e - 1
  refine ⟨n, ?_, ?_⟩
  · have hslack : N + 8 ≤ 2 ^ e := by
      simpa [e] using linear_slack_le_two_pow N
    omega
  · have hpos : 0 < 2 ^ e := (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ e)
    have hsucc : n + 1 = 2 ^ e := by
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    have hslack : N + 8 ≤ 2 ^ e := by
      simpa [e] using linear_slack_le_two_pow N
    rw [hsucc, Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]
    omega

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
