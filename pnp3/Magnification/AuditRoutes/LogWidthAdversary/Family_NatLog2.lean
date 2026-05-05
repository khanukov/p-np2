import Mathlib.Data.Nat.Log
import Magnification.AuditRoutes.FixedParamsProbe

/-!
# Log-width hardwiring adversary, S6 Nat.log2 family packaging

This worker slot supplies the Nat.log2 variant of the FP-3b.2 adversary
family and packages it as an `InPpolyFormula` witness.  The construction is
kept intentionally small and self-contained: at input length `n` it reads the
first `Nat.log2 (n + 1)` coordinates (embedded into `Fin n` using
`Nat.log_le_self`) and conjoins them.  Thus it is not the constant placeholder
from `FP3b1`, its syntactic size is linear in the logarithmic window, and the
language is defined by evaluating the family so the `correct` field is `rfl`.

This file is audit-only side-track infrastructure for formalizing the
log-width hardwiring obstruction; it only packages the local formula family
needed by the later integration slots.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace FixedParamsProbe
namespace FP3Attempt
namespace FP3b1
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces

/-- Nat.log2 window used by the S6 adversary family. -/
def logWidthNat (n : Nat) : Nat := Nat.log2 (n + 1)

/-- The log window always embeds into the ambient input length. -/
theorem logWidthNat_le (n : Nat) : logWidthNat n ≤ n := by
  have hlt : Nat.log 2 (n + 1) < n + 1 := Nat.log_lt_self 2 (Nat.succ_ne_zero n)
  simpa [logWidthNat, Nat.log2_eq_log_two] using Nat.lt_succ_iff.mp hlt

/--
`prefixAnd n k h` is the conjunction of the first `k` input variables of an
`n`-bit input, where `h : k ≤ n` certifies that those variables exist.  The
empty conjunction is `true`.
-/
def prefixAnd (n : Nat) : (k : Nat) → k ≤ n → FormulaCircuit n
  | 0, _ => FormulaCircuit.const true
  | k + 1, h =>
      FormulaCircuit.and
        (FormulaCircuit.input ⟨k, Nat.lt_of_succ_le h⟩)
        (prefixAnd n k (Nat.le_of_succ_le h))

/-- Exact size of `prefixAnd`: every selected input contributes one input node
and, except in the empty case, one `and` node. -/
theorem prefixAnd_size (n k : Nat) (h : k ≤ n) :
    FormulaCircuit.size (prefixAnd n k h) = 2 * k + 1 := by
  induction k with
  | zero =>
      simp [prefixAnd, FormulaCircuit.size]
  | succ k ih =>
      simp [prefixAnd, FormulaCircuit.size, ih]
      omega

/-- A small arithmetic lemma used to keep the polynomial package explicit. -/
theorem two_mul_succ_le_pow_two_plus_two (n : Nat) :
    2 * n + 1 ≤ n ^ 2 + 2 := by
  nlinarith [sq_nonneg ((n : Int) - 1)]

/-- The concrete polynomial bound used by the S6 witness. -/
def adversaryPolyBound_v_natlog2 (n : Nat) : Nat := 2 * n + 1

/-- The polynomial-boundedness certificate for `adversaryPolyBound_v_natlog2`. -/
theorem adversaryPolyBound_v_natlog2_poly :
    ∃ c : Nat, ∀ n, adversaryPolyBound_v_natlog2 n ≤ n ^ c + c := by
  refine ⟨2, ?_⟩
  intro n
  exact two_mul_succ_le_pow_two_plus_two n

/--
S6 output: the Nat.log2 log-window adversary family.  At length `n`, the
formula conjoins the first `Nat.log2 (n + 1)` inputs of the ambient `n`-bit
string.  This is deliberately non-constant while remaining polynomial-size.
-/
def adversaryFamily_v_natlog2 : ∀ n : Nat, FormulaCircuit n :=
  fun n => prefixAnd n (logWidthNat n) (logWidthNat_le n)

/-- The language decided by `adversaryFamily_v_natlog2`. -/
def adversaryLanguage_v_natlog2 : Pnp3.ComplexityInterfaces.Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily_v_natlog2 n) x

/-- Size bound for the Nat.log2 adversary family under the explicit linear cap. -/
theorem adversaryFamily_v_natlog2_size_le (n : Nat) :
    FormulaCircuit.size (adversaryFamily_v_natlog2 n) ≤ adversaryPolyBound_v_natlog2 n := by
  have hlog : logWidthNat n ≤ n := logWidthNat_le n
  calc
    FormulaCircuit.size (adversaryFamily_v_natlog2 n)
        = 2 * logWidthNat n + 1 := by
          simp [adversaryFamily_v_natlog2, prefixAnd_size]
    _ ≤ 2 * n + 1 := by omega
    _ = adversaryPolyBound_v_natlog2 n := rfl

/--
S6 output: `InPpolyFormula` packaging for the Nat.log2 adversary language.
The language is defined as evaluation of the family, so semantic correctness is
judgmental (`rfl`).
-/
def adversaryWitness_v_natlog2 : InPpolyFormula adversaryLanguage_v_natlog2 where
  polyBound := adversaryPolyBound_v_natlog2
  polyBound_poly := adversaryPolyBound_v_natlog2_poly
  family := adversaryFamily_v_natlog2
  family_size_le := adversaryFamily_v_natlog2_size_le
  correct := fun _ _ => rfl

end LogWidthAdversary
end FP3b1
end FP3Attempt
end FixedParamsProbe
end AuditRoutes
end Magnification
end Pnp3
