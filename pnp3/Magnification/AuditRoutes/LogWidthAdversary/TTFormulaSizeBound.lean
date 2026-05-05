import Tests.FormulaSupportBoundsFalsifiabilityProbe
import Mathlib.Tactic

/-!
# Size bound for the truth-table formula used by the log-width adversary

Slot S3 for `seed_packs/fp3b1_log_width_hardwiring_lift/`.

The seed-pack sketch proposed a `6 * 2^k` bound.  With the current
`FormulaCircuit.size` accounting and the already-committed `ttFormula`
constructor, the exact recurrence is

* `T(0) = 1`, and
* `T(k+1) = T(k) + T(k) + 6`.

Hence the exact size is `7 * 2^k - 6`, and the integration-friendly
polynomial bound is `7 * 2^k`.  This file deliberately proves the exact
closed form first, so future changes to either `size` or `ttFormula` trip a
small, local kernel-checked theorem instead of silently changing constants.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces
open Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe

/-- Renaming formula input coordinates preserves the syntactic size. -/
theorem rename_size {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    FormulaCircuit.size (FormulaCircuit.rename σ c) = FormulaCircuit.size c := by
  induction c with
  | const b => rfl
  | input i => rfl
  | not c ih => simp [FormulaCircuit.rename, FormulaCircuit.size, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.size, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.size, ih₁, ih₂]

/-- Exact closed form for the currently committed truth-table formula. -/
theorem ttFormula_size_eq (k : Nat) (f : Bitstring k → Bool) :
    FormulaCircuit.size (ttFormula f) = 7 * 2 ^ k - 6 := by
  induction k with
  | zero =>
      simp [ttFormula, FormulaCircuit.size]
  | succ k ih =>
      have hpow_pos : 0 < 2 ^ k := Nat.pow_pos (by norm_num : 0 < 2)
      have hsix_le : 6 ≤ 7 * 2 ^ k := by nlinarith
      have hsucc : 2 ^ (k + 1) = 2 * 2 ^ k := by
        rw [Nat.pow_succ]
        ring
      rw [hsucc]
      simp [ttFormula, FormulaCircuit.size, rename_size, ih]
      omega


/--
Integration-facing truth-table formula size bound.

The constant is `7` rather than the seed-pack sketch's `6`: under the current
syntax, every split introduces six nodes around the two recursive subformulas,
so the exact closed form is `7 * 2^k - 6`.
-/
theorem ttFormula_size_le (k : Nat) (f : Bitstring k → Bool) :
    FormulaCircuit.size (ttFormula f) ≤ 7 * 2 ^ k := by
  rw [ttFormula_size_eq k f]
  exact Nat.sub_le _ _

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
