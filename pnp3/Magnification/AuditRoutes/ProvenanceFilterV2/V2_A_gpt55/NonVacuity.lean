import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesPrefixAnd

/-!
# V2-A Phase 2: non-vacuity witness

Progress classification: side-track audit formalization.  This file supplies a
non-vacuity witness that is not the degenerate constant-false family.  The
family is a *seeded prefix conjunction*: it starts with the canonical
`prefixAnd n n` formula and adds the tautological seed `(x₀ ∨ ¬x₀)`.  The seed
forces the displayed syntax to contain both OR and NOT gates while preserving the
full-support profile and only adding constant overhead.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces
open FormulaShape

/-- The local tautological seed `(x₀ ∨ ¬x₀)` used when at least one input exists. -/
def seedGate (n : Nat) (h : 1 ≤ n) : FormulaCircuit n :=
  FormulaCircuit.or
    (FormulaCircuit.input ⟨0, h⟩)
    (FormulaCircuit.not (FormulaCircuit.input ⟨0, h⟩))

/--
Seeded full-prefix conjunction.

For `n = 0` we use `const false`; for every positive length we conjoin the full
prefix conjunction with the seed `(x₀ ∨ ¬x₀)`.  Semantically the seed is a
tautology, but syntactically it witnesses the V2-A OR/NOT gate-mix requirement.
-/
def seededPrefixAndFamily (n : Nat) : FormulaCircuit n :=
  if h : 1 ≤ n then
    FormulaCircuit.and (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd n n (Nat.le_refl n)) (seedGate n h)
  else
    FormulaCircuit.const false

/-- The seeded family has full support at every length. -/
theorem seededPrefixAndFamily_support_card (n : Nat) :
    (FormulaCircuit.support (seededPrefixAndFamily n)).card = n := by
  by_cases h : 1 ≤ n
  · have hPrefix := Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd_support_card n n (Nat.le_refl n)
    have hLower : n ≤ (FormulaCircuit.support (seededPrefixAndFamily n)).card := by
      calc
        n = (FormulaCircuit.support (Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd n n (Nat.le_refl n))).card := hPrefix.symm
        _ ≤ (FormulaCircuit.support (seededPrefixAndFamily n)).card := by
          apply Finset.card_le_card
          intro i hi
          simp [seededPrefixAndFamily, h, FormulaCircuit.support, hi]
    have hUpper : (FormulaCircuit.support (seededPrefixAndFamily n)).card ≤ n := by
      simpa using Finset.card_le_univ (FormulaCircuit.support (seededPrefixAndFamily n))
    exact Nat.le_antisymm hUpper hLower
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [seededPrefixAndFamily, FormulaCircuit.support]

/-- Exact Boolean-gate count for the seeded full-prefix conjunction. -/
theorem seededPrefixAndFamily_booleanGateCount (n : Nat) :
    booleanGateCount (seededPrefixAndFamily n) = if 1 ≤ n then n + 3 else 0 := by
  by_cases h : 1 ≤ n
  · simp [seededPrefixAndFamily, h, seedGate, booleanGateCount,
      notGateCount, andGateCount, orGateCount, andGateCount_prefixAnd,
      orGateCount_prefixAnd, notGateCount_prefixAnd]
    omega
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [seededPrefixAndFamily, booleanGateCount, notGateCount, andGateCount,
      orGateCount]

/-- A linear size bound for the seeded full-prefix conjunction. -/
theorem seededPrefixAndFamily_size_le (n : Nat) :
    FormulaCircuit.size (seededPrefixAndFamily n) ≤ 2 * n + 6 := by
  by_cases h : 1 ≤ n
  · have hSize := Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd_size n n (Nat.le_refl n)
    simp [seededPrefixAndFamily, h, seedGate, FormulaCircuit.size, hSize]
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [seededPrefixAndFamily, FormulaCircuit.size]

/-- Formula depth is bounded by formula size. -/
theorem FormulaCircuit.depth_le_size {n : Nat} (c : FormulaCircuit n) :
    FormulaCircuit.depth c ≤ FormulaCircuit.size c := by
  induction c with
  | const b => simp [FormulaCircuit.depth, FormulaCircuit.size]
  | input i => simp [FormulaCircuit.depth, FormulaCircuit.size]
  | not c ih => simp [FormulaCircuit.depth, FormulaCircuit.size, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.depth, FormulaCircuit.size]
      omega
  | or c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.depth, FormulaCircuit.size]
      omega

/-- A linear depth bound for the seeded full-prefix conjunction. -/
theorem seededPrefixAndFamily_depth_le (n : Nat) :
    FormulaCircuit.depth (seededPrefixAndFamily n) ≤ 2 * n + 6 := by
  exact le_trans (FormulaCircuit.depth_le_size (seededPrefixAndFamily n))
    (seededPrefixAndFamily_size_le n)

/-- The language decided by the seeded prefix-AND family. -/
def seededPrefixAndLanguage : Language :=
  fun n x => FormulaCircuit.eval (seededPrefixAndFamily n) x

/-- Linear polynomial bound used by `seededPrefixAndWitness`. -/
def seededPrefixAndPolyBound (n : Nat) : Nat := 2 * n + 6

/-- The seeded-prefix size bound is polynomial. -/
theorem seededPrefixAndPolyBound_poly :
    ∃ c : Nat, ∀ n, seededPrefixAndPolyBound n ≤ n ^ c + c := by
  refine ⟨7, ?_⟩
  intro n
  have hquad : seededPrefixAndPolyBound n ≤ n ^ 2 + 7 := by
    unfold seededPrefixAndPolyBound
    nlinarith [sq_nonneg ((n : Int) - 1)]
  have hpow : n ^ 2 ≤ n ^ 7 := by
    cases n with
    | zero => norm_num
    | succ n =>
        exact Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num : 2 ≤ 7)
  exact le_trans hquad (Nat.add_le_add_right hpow 7)

/-- Strict `InPpolyFormula` package for the seeded full-prefix conjunction. -/
def seededPrefixAndWitness : InPpolyFormula seededPrefixAndLanguage where
  polyBound := seededPrefixAndPolyBound
  polyBound_poly := seededPrefixAndPolyBound_poly
  family := seededPrefixAndFamily
  family_size_le := seededPrefixAndFamily_size_le
  correct := fun _ _ => rfl

/-- The seeded full-prefix conjunction is admitted by the restored V2-A filter. -/
theorem seededPrefixAndWitness_admitted :
    ProvenanceFilter_v2_V2_A_gpt55_Filter seededPrefixAndWitness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B
    refine ⟨B + 1, ?_⟩
    simp [seededPrefixAndWitness, seededPrefixAndFamily_support_card]
  · intro n
    rw [seededPrefixAndWitness, seededPrefixAndFamily_booleanGateCount,
      seededPrefixAndFamily_support_card]
    split <;> omega
  · intro n
    have hDepth := seededPrefixAndFamily_depth_le n
    change FormulaCircuit.depth (seededPrefixAndFamily n) ≤
      8 * (FormulaCircuit.support (seededPrefixAndFamily n)).card + 8
    rw [seededPrefixAndFamily_support_card]
    omega
  · intro n hSupport
    by_cases h : 1 ≤ n
    · simp [seededPrefixAndWitness, seededPrefixAndFamily, h, seedGate,
        orGateCount, notGateCount]
    · have hn0 : n = 0 := by omega
      subst hn0
      simp [seededPrefixAndWitness, seededPrefixAndFamily_support_card] at hSupport

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
