import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NonVacuity

/-!
# V2-A natural-proofs self-test: representation sensitivity

Progress classification: side-track audit formalization.  This file does not
claim progress toward `P != NP`; it checks a natural-proofs escape property of
the proposal-level V2-A syntactic filter.

The point of the test is extensionality failure at the level of strict
`InPpolyFormula` witnesses.  We keep the accepted `seededPrefixAndWitness` as
`w_good`, and build a second witness for the *same* language by wrapping every
family member in twenty double-negation pads.  Double negation preserves the
truth table, so both witnesses decide `seededPrefixAndLanguage`; however, V2-A
counts the displayed NOT gates.  At length `1` the support cardinality is still
`1`, so the V2-A Boolean-gate cap is `16 * 1 + 16 = 32`, while the padded syntax
has the original `4` gates plus `40` added NOT gates.  Thus V2-A accepts the
good witness and rejects the bad witness solely because of representation.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55
namespace NaturalProofsSelfTest

open Pnp3.ComplexityInterfaces
open FormulaShape

/-- Add `k` layers of syntactically redundant double negation around a formula. -/
def doubleNotPad {n : Nat} : Nat → FormulaCircuit n → FormulaCircuit n
  | 0, c => c
  | k + 1, c => FormulaCircuit.not (FormulaCircuit.not (doubleNotPad k c))

/-- Double-negation padding preserves the Boolean function computed. -/
theorem doubleNotPad_eval {n : Nat} (k : Nat) (c : FormulaCircuit n)
    (x : Bitstring n) :
    FormulaCircuit.eval (doubleNotPad k c) x = FormulaCircuit.eval c x := by
  induction k with
  | zero => simp [doubleNotPad]
  | succ k ih => simp [doubleNotPad, FormulaCircuit.eval, ih]

/-- Double-negation padding adds exactly two NOT gates per padding layer. -/
theorem notGateCount_doubleNotPad {n : Nat} (k : Nat) (c : FormulaCircuit n) :
    notGateCount (doubleNotPad k c) = notGateCount c + 2 * k := by
  induction k with
  | zero => simp [doubleNotPad]
  | succ k ih =>
      simp [doubleNotPad, notGateCount, ih]
      omega


/-- Double-negation padding preserves syntactic support exactly. -/
theorem support_doubleNotPad {n : Nat} (k : Nat) (c : FormulaCircuit n) :
    FormulaCircuit.support (doubleNotPad k c) = FormulaCircuit.support c := by
  induction k with
  | zero => simp [doubleNotPad]
  | succ k ih => simp [doubleNotPad, FormulaCircuit.support, ih]

/-- Double-negation padding leaves the AND-gate count unchanged. -/
theorem andGateCount_doubleNotPad {n : Nat} (k : Nat) (c : FormulaCircuit n) :
    andGateCount (doubleNotPad k c) = andGateCount c := by
  induction k with
  | zero => simp [doubleNotPad]
  | succ k ih => simp [doubleNotPad, andGateCount, ih]

/-- Double-negation padding leaves the OR-gate count unchanged. -/
theorem orGateCount_doubleNotPad {n : Nat} (k : Nat) (c : FormulaCircuit n) :
    orGateCount (doubleNotPad k c) = orGateCount c := by
  induction k with
  | zero => simp [doubleNotPad]
  | succ k ih => simp [doubleNotPad, orGateCount, ih]

/-- Double-negation padding adds exactly two Boolean gates per padding layer. -/
theorem booleanGateCount_doubleNotPad {n : Nat} (k : Nat) (c : FormulaCircuit n) :
    booleanGateCount (doubleNotPad k c) = booleanGateCount c + 2 * k := by
  simp [booleanGateCount, notGateCount_doubleNotPad, andGateCount_doubleNotPad,
    orGateCount_doubleNotPad]
  omega

/-- Double-negation padding adds exactly two size units per padding layer. -/
theorem size_doubleNotPad {n : Nat} (k : Nat) (c : FormulaCircuit n) :
    FormulaCircuit.size (doubleNotPad k c) = FormulaCircuit.size c + 2 * k := by
  induction k with
  | zero => simp [doubleNotPad]
  | succ k ih =>
      simp [doubleNotPad, FormulaCircuit.size, ih]
      omega

/-- The fixed padding amount used by the bad representation. -/
def representationSensitivityPad : Nat := 20

/-- A semantically equivalent but syntactically over-padded representation. -/
def paddedSeededPrefixAndFamily (n : Nat) : FormulaCircuit n :=
  doubleNotPad representationSensitivityPad (seededPrefixAndFamily n)

/-- The padded family computes exactly the same language as the accepted family. -/
theorem paddedSeededPrefixAndFamily_eval (n : Nat) (x : Bitstring n) :
    FormulaCircuit.eval (paddedSeededPrefixAndFamily n) x =
      FormulaCircuit.eval (seededPrefixAndFamily n) x := by
  simp [paddedSeededPrefixAndFamily, doubleNotPad_eval]

/-- Polynomial size bound for the over-padded witness. -/
def paddedSeededPrefixAndPolyBound (n : Nat) : Nat := 2 * n + 46

/-- The padded linear bound is polynomial. -/
theorem paddedSeededPrefixAndPolyBound_poly :
    ∃ c : Nat, ∀ n, paddedSeededPrefixAndPolyBound n ≤ n ^ c + c := by
  refine ⟨47, ?_⟩
  intro n
  have hquad : paddedSeededPrefixAndPolyBound n ≤ n ^ 2 + 47 := by
    unfold paddedSeededPrefixAndPolyBound
    nlinarith [sq_nonneg ((n : Int) - 1)]
  have hpow : n ^ 2 ≤ n ^ 47 := by
    cases n with
    | zero => norm_num
    | succ n =>
        exact Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num : 2 ≤ 47)
  exact le_trans hquad (Nat.add_le_add_right hpow 47)

/-- The padded seeded-prefix family obeys its advertised polynomial bound. -/
theorem paddedSeededPrefixAndFamily_size_le (n : Nat) :
    FormulaCircuit.size (paddedSeededPrefixAndFamily n) ≤
      paddedSeededPrefixAndPolyBound n := by
  rw [paddedSeededPrefixAndFamily, size_doubleNotPad]
  unfold representationSensitivityPad paddedSeededPrefixAndPolyBound
  have hSize := seededPrefixAndFamily_size_le n
  omega

/--
The bad witness: same `seededPrefixAndLanguage`, different representation.

Its `correct` field follows from `paddedSeededPrefixAndFamily_eval` and the
same language definition used by `seededPrefixAndWitness`; hence any separation
below is not a semantic separation of Boolean functions.
-/
def paddedSeededPrefixAndWitness : InPpolyFormula seededPrefixAndLanguage where
  polyBound := paddedSeededPrefixAndPolyBound
  polyBound_poly := paddedSeededPrefixAndPolyBound_poly
  family := paddedSeededPrefixAndFamily
  family_size_le := paddedSeededPrefixAndFamily_size_le
  correct := by
    intro n x
    simp [seededPrefixAndLanguage, paddedSeededPrefixAndFamily_eval]

/-- The padded representation is rejected by V2-A because it violates the gate cap at length `1`. -/
theorem paddedSeededPrefixAndWitness_rejected :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter paddedSeededPrefixAndWitness := by
  intro hFilter
  obtain ⟨_hUnbounded, hGate, _hDepth, _hMix⟩ := hFilter
  have hGateAtOne := hGate 1
  have hTooMany :
      16 * (FormulaCircuit.support (paddedSeededPrefixAndWitness.family 1)).card + 16 <
        booleanGateCount (paddedSeededPrefixAndWitness.family 1) := by
    simp [paddedSeededPrefixAndWitness, paddedSeededPrefixAndFamily,
      booleanGateCount_doubleNotPad, support_doubleNotPad,
      seededPrefixAndFamily_booleanGateCount, seededPrefixAndFamily_support_card,
      representationSensitivityPad]
  exact Nat.not_lt_of_ge hGateAtOne hTooMany

/--
V2-A is representation-sensitive: it separates two strict formula witnesses for
one and the same language even though their displayed families compute identical
truth tables at every input length.
-/
theorem v2A_same_language_different_representation :
    ∃ (L : Language)
      (w_good w_bad : InPpolyFormula L),
        (∀ n x,
          FormulaCircuit.eval (w_good.family n) x =
          FormulaCircuit.eval (w_bad.family n) x) ∧
        ProvenanceFilter_v2_V2_A_gpt55_Filter w_good ∧
        ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter w_bad := by
  refine ⟨seededPrefixAndLanguage,
    seededPrefixAndWitness,
    paddedSeededPrefixAndWitness,
    ?_,
    seededPrefixAndWitness_admitted,
    paddedSeededPrefixAndWitness_rejected⟩
  intro n x
  exact (paddedSeededPrefixAndFamily_eval n x).symm

/--
Weaker named surface for consumers that only need non-extensionality over
witness representations.  Both witnesses are strict `InPpolyFormula` packages
for `seededPrefixAndLanguage`; the stronger theorem above additionally records
pointwise semantic equality of their family members.
-/
theorem v2A_not_extensional_on_witness_representations :
    ∃ (L : Language)
      (w_good w_bad : InPpolyFormula L),
        ProvenanceFilter_v2_V2_A_gpt55_Filter w_good ∧
        ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter w_bad := by
  obtain ⟨L, w_good, w_bad, _hSame, hGood, hBad⟩ :=
    v2A_same_language_different_representation
  exact ⟨L, w_good, w_bad, hGood, hBad⟩

end NaturalProofsSelfTest
end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
