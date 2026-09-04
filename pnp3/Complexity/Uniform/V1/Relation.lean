import Complexity.Uniform.V1.PairEncoding
import Complexity.Uniform.V1.PolynomialTime

/-!
# Advice-free, length-indexed witness relations

This module gives a total raw-word semantics to an indexed witness relation.
Every finite word is decoded before the relation is consulted. A malformed
word denotes `false`; because verifier correctness is stated with
`DecidesWithin`, `false` requires the machine to reach its literal reject
state. Timeout is therefore not silently identified with rejection.

There is deliberately no verifier structure carrying a running-time,
input-length, advice, or correctness function. `VerifiesRelation` is a
proposition about one closed `UniformTM` and one fixed verifier exponent.
`UniformNP` separately fixes its witness-length exponent.
-/

namespace Pnp3.Complexity.Uniform.V1

open PairEncoding

/-- A Boolean relation on an input and a witness, with both lengths explicit. -/
abbrev WitnessRelation :=
  ∀ n m, Bitstring n → Bitstring m → Bool

/--
The total language of raw encoded words induced by `R`.

The `none` branch is semantically load-bearing: malformed words have answer
`false`,
so a correct verifier must literally reject them within its clock.
-/
def encodedRelationLanguage (R : WitnessRelation) : Language := fun _ y =>
  match decodePair y with
  | none => false
  | some p => R p.1.1 p.2.1 p.1.2 p.2.2

/-- On a canonical pair encoding, total raw-word semantics reduces to `R`. -/
theorem encodedRelationLanguage_encodePair (R : WitnessRelation)
    {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    encodedRelationLanguage R (pairLength n m) (encodePair x w) =
      R n m x w := by
  simp only [encodedRelationLanguage, decodePair_roundtrip]

/-- A malformed raw word has the literal Boolean answer `false`. -/
theorem encodedRelationLanguage_malformed (R : WitnessRelation)
    {N : Nat} (y : Bitstring N) (hdecode : decodePair y = none) :
    encodedRelationLanguage R N y = false := by
  simp [encodedRelationLanguage, hdecode]

/--
`M` verifies `R` with exponent `verifierExponent` on *every raw word*.

The clock is a polynomial in `N`, the actual length of the encoded word
received by the machine. Both the machine and exponent occur outside the raw
input quantifiers.
-/
def VerifiesRelation (M : UniformTM) (verifierExponent : Nat)
    (R : WitnessRelation) : Prop :=
  ∀ N (y : Bitstring N),
    DecidesWithin M (polyClock verifierExponent N) y
      (encodedRelationLanguage R N y)

/-- Raw-word correctness specializes to indexed correctness on `encodePair`. -/
theorem verifiesRelation_encodePair {M : UniformTM} {verifierExponent : Nat}
    {R : WitnessRelation} (h : VerifiesRelation M verifierExponent R)
    {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    DecidesWithin M (polyClock verifierExponent (pairLength n m))
      (encodePair x w) (R n m x w) := by
  simpa only [encodedRelationLanguage_encodePair] using
    h (pairLength n m) (encodePair x w)

/-- Total correctness forces literal rejection of every malformed word. -/
theorem verifiesRelation_rejects_malformed {M : UniformTM}
    {verifierExponent : Nat} {R : WitnessRelation}
    (h : VerifiesRelation M verifierExponent R)
    {N : Nat} (y : Bitstring N) (hdecode : decodePair y = none) :
    RejectsWithin M (polyClock verifierExponent N) y := by
  have hdecides := h N y
  rw [encodedRelationLanguage_malformed R y hdecode] at hdecides
  simpa [DecidesWithin] using hdecides

/-- A false relation value on a canonical pair means literal rejection. -/
theorem verifiesRelation_rejects_encodePair {M : UniformTM}
    {verifierExponent : Nat} {R : WitnessRelation}
    (h : VerifiesRelation M verifierExponent R)
    {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (hR : R n m x w = false) :
    RejectsWithin M (polyClock verifierExponent (pairLength n m))
      (encodePair x w) := by
  have hdecides := verifiesRelation_encodePair h x w
  rw [hR] at hdecides
  simpa [DecidesWithin] using hdecides

/-- A true relation value on a canonical pair means literal acceptance. -/
theorem verifiesRelation_accepts_encodePair {M : UniformTM}
    {verifierExponent : Nat} {R : WitnessRelation}
    (h : VerifiesRelation M verifierExponent R)
    {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (hR : R n m x w = true) :
    AcceptsWithin M (polyClock verifierExponent (pairLength n m))
      (encodePair x w) := by
  have hdecides := verifiesRelation_encodePair h x w
  rw [hR] at hdecides
  simpa [DecidesWithin] using hdecides

/--
For a fixed finite machine and verifier exponent, total verification determines
at most one indexed relation. Canonical encodings expose every dependent
relation query, while the same machine, input, and budget cannot decide both
Boolean verdicts.
-/
theorem verifiesRelation_unique {M : UniformTM} {verifierExponent : Nat}
    {R S : WitnessRelation}
    (hR : VerifiesRelation M verifierExponent R)
    (hS : VerifiesRelation M verifierExponent S) :
    R = S := by
  funext n
  funext m
  funext x
  funext w
  have hRdecides := verifiesRelation_encodePair hR x w
  have hSdecides := verifiesRelation_encodePair hS x w
  cases hRvalue : R n m x w <;> cases hSvalue : S n m x w
  · rfl
  · exfalso
    exact (not_decidesWithin_true_and_false M (encodePair x w))
      ⟨by simpa only [hSvalue] using hSdecides,
        by simpa only [hRvalue] using hRdecides⟩
  · exfalso
    exact (not_decidesWithin_true_and_false M (encodePair x w))
      ⟨by simpa only [hRvalue] using hRdecides,
        by simpa only [hSvalue] using hSdecides⟩
  · rfl

end Pnp3.Complexity.Uniform.V1
