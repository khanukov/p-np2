import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NonVacuity
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Composition

/-!
# V2-A adversarial robustness: semantic rewrite attack

Progress classification: side-track audit self-attack.

This file intentionally plays the adversary against the V2-A/gpt55 syntactic
filter.  The attack is not a lower-bound route and does not introduce a source
obligation, bridge, candidate package, or final endpoint.  It shows that the
canonical Nat.log2 prefix-AND hardwiring witness can be rewritten by conjoining
a tautological local seed `(x₀ ∨ ¬x₀)`.  The rewritten family computes exactly
`adversaryLanguage_v_natlog2`, but syntactically contains the OR/NOT gates that
V2-A asks for while retaining only constant gate overhead.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55
namespace AdversarialRobustness

open Pnp3.ComplexityInterfaces
open FormulaShape
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary

/--
The semantic-rewrite family for the prefix-AND adversary.

For positive input lengths, this is the original Nat.log2 prefix conjunction
conjoined with the tautology `(x₀ ∨ ¬x₀)`.  At length zero there is no `x₀`, and
`logWidthNat 0 = 0`, so the family is left unchanged.  The seed is deliberately
syntactic: it is logically redundant but forces one OR gate and one NOT gate.
-/
def rewritePrefixAndFamily (n : Nat) : FormulaCircuit n :=
  if h : 1 ≤ n then
    FormulaCircuit.and (adversaryFamily_v_natlog2 n) (seedGate n h)
  else
    adversaryFamily_v_natlog2 n

/-- The tautological seed always evaluates to `true`. -/
theorem seedGate_eval_eq_true {n : Nat} (h : 1 ≤ n) (x : Bitstring n) :
    FormulaCircuit.eval (seedGate n h) x = true := by
  simp [seedGate, FormulaCircuit.eval]

/-- The rewritten family is pointwise semantically identical to the excluded one. -/
theorem rewritePrefixAndFamily_eval_eq (n : Nat) (x : Bitstring n) :
    FormulaCircuit.eval (rewritePrefixAndFamily n) x =
      FormulaCircuit.eval (adversaryFamily_v_natlog2 n) x := by
  by_cases h : 1 ≤ n
  · simp [rewritePrefixAndFamily, h, FormulaCircuit.eval, seedGate_eval_eq_true h x]
  · simp [rewritePrefixAndFamily, h]

/-- The rewritten prefix-AND language is definitionally the old adversary language. -/
def rewritePrefixAndLanguage : Language := adversaryLanguage_v_natlog2

/-- Linear polynomial bound for the rewritten log-width prefix conjunction. -/
def rewritePrefixAndPolyBound (n : Nat) : Nat := 2 * n + 6

/-- The rewritten-prefix linear cap is polynomial. -/
theorem rewritePrefixAndPolyBound_poly :
    ∃ c : Nat, ∀ n, rewritePrefixAndPolyBound n ≤ n ^ c + c := by
  simpa [rewritePrefixAndPolyBound, seededPrefixAndPolyBound] using
    seededPrefixAndPolyBound_poly

/-- Size of the rewritten family is still linearly bounded. -/
theorem rewritePrefixAndFamily_size_le (n : Nat) :
    FormulaCircuit.size (rewritePrefixAndFamily n) ≤ rewritePrefixAndPolyBound n := by
  by_cases h : 1 ≤ n
  · have hPrefixSize := prefixAnd_size n (logWidthNat n) (logWidthNat_le n)
    calc
      FormulaCircuit.size (rewritePrefixAndFamily n)
          = 2 * logWidthNat n + 6 := by
            simp [rewritePrefixAndFamily, h, adversaryFamily_v_natlog2,
              seedGate, FormulaCircuit.size, hPrefixSize]
      _ ≤ 2 * n + 6 := by
            have hLog := logWidthNat_le n
            omega
      _ = rewritePrefixAndPolyBound n := rfl
  · have hn0 : n = 0 := by omega
    subst hn0
    have hPrefixSize := prefixAnd_size 0 (logWidthNat 0) (logWidthNat_le 0)
    have hLog0 : logWidthNat 0 = 0 := by
      have hle := logWidthNat_le 0
      omega
    calc
      FormulaCircuit.size (rewritePrefixAndFamily 0)
          = 2 * logWidthNat 0 + 1 := by
            simpa [rewritePrefixAndFamily, adversaryFamily_v_natlog2] using hPrefixSize
      _ = 1 := by rw [hLog0]
      _ ≤ rewritePrefixAndPolyBound 0 := by norm_num [rewritePrefixAndPolyBound]

/-- Strict `InPpolyFormula` package computing the same language as prefix-AND. -/
def rewritePrefixAndWitness : InPpolyFormula rewritePrefixAndLanguage where
  polyBound := rewritePrefixAndPolyBound
  polyBound_poly := rewritePrefixAndPolyBound_poly
  family := rewritePrefixAndFamily
  family_size_le := rewritePrefixAndFamily_size_le
  correct := by
    intro n x
    exact rewritePrefixAndFamily_eval_eq n x

/-- The original prefix support is contained in the rewritten syntax. -/
theorem adversaryFamily_support_subset_rewrite (n : Nat) :
    FormulaCircuit.support (adversaryFamily_v_natlog2 n) ⊆
      FormulaCircuit.support (rewritePrefixAndFamily n) := by
  intro i hi
  by_cases h : 1 ≤ n
  · simp [rewritePrefixAndFamily, h, FormulaCircuit.support, hi]
  · simpa [rewritePrefixAndFamily, h] using hi

/-- The rewritten support cardinality is at least the original log-width support. -/
theorem logWidthNat_le_rewrite_support_card (n : Nat) :
    logWidthNat n ≤ (FormulaCircuit.support (rewritePrefixAndFamily n)).card := by
  calc
    logWidthNat n = (FormulaCircuit.support (adversaryFamily_v_natlog2 n)).card :=
      (adversaryFamily_v_natlog2_support_card n).symm
    _ ≤ (FormulaCircuit.support (rewritePrefixAndFamily n)).card := by
      exact Finset.card_le_card (adversaryFamily_support_subset_rewrite n)

/-- Exact Boolean-gate count: prefix-AND gates plus one AND, one OR, and one NOT. -/
theorem rewritePrefixAndFamily_booleanGateCount (n : Nat) :
    booleanGateCount (rewritePrefixAndFamily n) =
      if 1 ≤ n then logWidthNat n + 3 else 0 := by
  by_cases h : 1 ≤ n
  · simp [rewritePrefixAndFamily, h, adversaryFamily_v_natlog2, seedGate,
      booleanGateCount, notGateCount, andGateCount, orGateCount,
      andGateCount_prefixAnd, orGateCount_prefixAnd, notGateCount_prefixAnd]
    omega
  · have hn0 : n = 0 := by omega
    subst hn0
    have hLog0 : logWidthNat 0 = 0 := by
      have hle := logWidthNat_le 0
      omega
    simp [rewritePrefixAndFamily, adversaryFamily_v_natlog2, hLog0,
      booleanGateCount, notGateCount_prefixAnd, andGateCount_prefixAnd,
      orGateCount_prefixAnd]

/-- The rewritten family has a linear depth bound in its log-width. -/
theorem rewritePrefixAndFamily_depth_le (n : Nat) :
    FormulaCircuit.depth (rewritePrefixAndFamily n) ≤ 2 * logWidthNat n + 6 := by
  calc
    FormulaCircuit.depth (rewritePrefixAndFamily n)
        ≤ FormulaCircuit.size (rewritePrefixAndFamily n) :=
          FormulaCircuit.depth_le_size _
    _ ≤ 2 * logWidthNat n + 6 := by
      by_cases h : 1 ≤ n
      · have hPrefixSize := prefixAnd_size n (logWidthNat n) (logWidthNat_le n)
        simp [rewritePrefixAndFamily, h, adversaryFamily_v_natlog2, seedGate,
          FormulaCircuit.size, hPrefixSize]
      · have hn0 : n = 0 := by omega
        subst hn0
        have hPrefixSize := prefixAnd_size 0 (logWidthNat 0) (logWidthNat_le 0)
        have hLog0 : logWidthNat 0 = 0 := by
          have hle := logWidthNat_le 0
          omega
        calc
          FormulaCircuit.size (rewritePrefixAndFamily 0)
              = 2 * logWidthNat 0 + 1 := by
                simpa [rewritePrefixAndFamily, adversaryFamily_v_natlog2] using hPrefixSize
          _ ≤ 2 * logWidthNat 0 + 6 := by omega

/-- The semantic rewrite of the excluded prefix-AND witness passes V2-A. -/
theorem rewritePrefixAndWitness_admitted :
    ProvenanceFilter_v2_V2_A_gpt55_Filter rewritePrefixAndWitness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B
    rcases Pnp3.Magnification.AuditRoutes.LogWidthAdversary.logWidth_unbounded B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact lt_of_lt_of_le hn (logWidthNat_le_rewrite_support_card n)
  · intro n
    change booleanGateCount (rewritePrefixAndFamily n) ≤
      16 * (FormulaCircuit.support (rewritePrefixAndFamily n)).card + 16
    rw [rewritePrefixAndFamily_booleanGateCount]
    have hSupportLower := logWidthNat_le_rewrite_support_card n
    split <;> omega
  · intro n
    change FormulaCircuit.depth (rewritePrefixAndFamily n) ≤
      8 * (FormulaCircuit.support (rewritePrefixAndFamily n)).card + 8
    have hDepth := rewritePrefixAndFamily_depth_le n
    have hSupportLower := logWidthNat_le_rewrite_support_card n
    omega
  · intro n hSupport
    by_cases h : 1 ≤ n
    · simp [rewritePrefixAndWitness, rewritePrefixAndFamily, h, seedGate,
        orGateCount, notGateCount]
    · have hn0 : n = 0 := by omega
      subst hn0
      have hCard0 : (FormulaCircuit.support (rewritePrefixAndFamily 0)).card = 0 := by
        have hOrig := adversaryFamily_v_natlog2_support_card 0
        have hLog0 : logWidthNat 0 = 0 := by
          have hle := logWidthNat_le 0
          omega
        rw [hLog0] at hOrig
        simpa [rewritePrefixAndFamily] using hOrig
      change 2 ≤ (FormulaCircuit.support (rewritePrefixAndFamily 0)).card at hSupport
      rw [hCard0] at hSupport
      omega

/--
Primary adversarial witness requested by the seed pack: the rewritten witness
computes the same language as the excluded Nat.log2 prefix-AND adversary and
nevertheless satisfies the V2-A syntactic filter.
-/
theorem v2A_rewrite_attack_prefixAnd :
    ∃ (L : Language) (w_rewritten : InPpolyFormula L),
      L = adversaryLanguage_v_natlog2 ∧
      ProvenanceFilter_v2_V2_A_gpt55_Filter w_rewritten := by
  refine ⟨rewritePrefixAndLanguage, rewritePrefixAndWitness, rfl, ?_⟩
  exact rewritePrefixAndWitness_admitted

end AdversarialRobustness
end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
