import Mathlib.Data.Nat.Log
import Magnification.AuditRoutes.FixedParamsProbe

/-!
# Log-width hardwiring adversary, S7 power-of-two-slice family packaging

This audit-only module closes slot S7 of the parallel log-width hardwiring
lift.  It packages a sparse power-of-two-slice formula family as an
`InPpolyFormula` witness.  At length `n`, the formula reads the first
`pow2SliceWidth n` coordinates and conjoins them; outside exact powers of two,
`pow2SliceWidth n` is zero, so the family is sparse but still non-constant along the
power-of-two slices.

The language is definitionally the evaluation of this family, so the semantic
correctness field of the witness is the expected `rfl` proof.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces

/-- Sparse log-width selector for the S7 family.

At exact power-of-two lengths it returns the binary exponent; at other lengths
it returns zero.  This keeps the packaged family sparse while preserving the
power-of-two slices needed by later support-cardinality arguments. -/
def pow2SliceWidth (n : Nat) : Nat :=
  if n = 2 ^ Nat.log 2 n then Nat.log 2 n else 0

/-- The sparse selector never exceeds the ambient input length. -/
theorem pow2SliceWidth_le (n : Nat) : pow2SliceWidth n ≤ n := by
  unfold pow2SliceWidth
  by_cases h : n = 2 ^ Nat.log 2 n
  · rw [if_pos h]
    have hlt : Nat.log 2 n < 2 ^ Nat.log 2 n :=
      (show Nat.log 2 n < 2 ^ Nat.log 2 n from Nat.lt_two_pow_self)
    exact Nat.le_of_lt (by simpa [← h] using hlt)
  · rw [if_neg h]
    exact Nat.zero_le n

/--
`pow2PrefixAnd n k h` is the conjunction of the first `k` input variables of an
`n`-bit input, where `h : k ≤ n` certifies that the selected prefix embeds into
the ambient input length.  The empty conjunction is `true`.
-/
def pow2PrefixAnd (n : Nat) : (k : Nat) → k ≤ n → FormulaCircuit n
  | 0, _ => FormulaCircuit.const true
  | k + 1, h =>
      FormulaCircuit.and
        (FormulaCircuit.input ⟨k, Nat.lt_of_succ_le h⟩)
        (pow2PrefixAnd n k (Nat.le_of_succ_le h))

/-- Exact syntactic size of the prefix conjunction used by the S7 family. -/
theorem pow2PrefixAnd_size (n k : Nat) (h : k ≤ n) :
    FormulaCircuit.size (pow2PrefixAnd n k h) = 2 * k + 1 := by
  induction k with
  | zero =>
      simp [pow2PrefixAnd, FormulaCircuit.size]
  | succ k ih =>
      simp [pow2PrefixAnd, FormulaCircuit.size, ih]
      omega

/-- A quadratic polynomial cap for the linear size bound. -/
theorem two_mul_add_one_le_square_add_two (n : Nat) :
    2 * n + 1 ≤ n ^ 2 + 2 := by
  nlinarith [sq_nonneg ((n : Int) - 1)]

/-- The explicit polynomial bound used by the power-of-two-slice witness. -/
def adversaryPolyBound_v_pow2 (n : Nat) : Nat := 2 * n + 1

/-- Polynomial-boundedness certificate for `adversaryPolyBound_v_pow2`. -/
theorem adversaryPolyBound_v_pow2_poly :
    ∃ c : Nat, ∀ n, adversaryPolyBound_v_pow2 n ≤ n ^ c + c := by
  refine ⟨2, ?_⟩
  intro n
  exact two_mul_add_one_le_square_add_two n

/--
S7 output: the sparse power-of-two-slice adversary family.

The selected width is `pow2SliceWidth n`, which is always at most `n`, so the first
`pow2SliceWidth n` variables can be read as inputs of an `n`-variable formula.
-/
def adversaryFamily_v_pow2 : ∀ n : Nat, FormulaCircuit n :=
  fun n => pow2PrefixAnd n (pow2SliceWidth n) (pow2SliceWidth_le n)

/-- The language decided by `adversaryFamily_v_pow2`. -/
def adversaryLanguage_v_pow2 : Pnp3.ComplexityInterfaces.Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily_v_pow2 n) x

/-- Size bound for the S7 family under the explicit linear cap. -/
theorem adversaryFamily_v_pow2_size_le (n : Nat) :
    FormulaCircuit.size (adversaryFamily_v_pow2 n) ≤ adversaryPolyBound_v_pow2 n := by
  calc
    FormulaCircuit.size (adversaryFamily_v_pow2 n)
        = 2 * pow2SliceWidth n + 1 := by
          simp [adversaryFamily_v_pow2, pow2PrefixAnd_size]
    _ ≤ 2 * n + 1 := by
          have hk : pow2SliceWidth n ≤ n := pow2SliceWidth_le n
          omega
    _ = adversaryPolyBound_v_pow2 n := rfl

/--
S7 output: `InPpolyFormula` packaging for the power-of-two-slice adversary
language.  Because the language is defined by evaluating the same family, the
semantic correctness field is judgmental.
-/
def adversaryWitness_v_pow2 : InPpolyFormula adversaryLanguage_v_pow2 where
  polyBound := adversaryPolyBound_v_pow2
  polyBound_poly := adversaryPolyBound_v_pow2_poly
  family := adversaryFamily_v_pow2
  family_size_le := adversaryFamily_v_pow2_size_le
  correct := fun _ _ => rfl

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
