import Complexity.Uniform.V1.UniformNP
import Complexity.Uniform.V1.Examples

/-!
# Executable controls for advice-free relation semantics

The all-accept and all-reject literals pin the two Boolean verdicts on
canonical pair encodings. The all-reject literal is also a total verifier
for the constantly-false relation under total raw-word semantics. In contrast,
the all-accept literal is intentionally proved *not* to verify the
constantly-true relation on raw words: it accepts the malformed empty word.

The nonterminal literal is the negative control showing that a false
acceptance flag at the deadline is not literal rejection.
-/

namespace Pnp3.Complexity.Uniform.V1

open PairEncoding

/-- The constantly-true indexed witness relation. -/
def trueRelation : WitnessRelation := fun _ _ _ _ => true

/-- The constantly-false indexed witness relation. -/
def falseRelation : WitnessRelation := fun _ _ _ _ => false

/-- Literal-accept control. This is not a total raw-word verifier. -/
def trueRelationMachine : UniformTM := allAcceptMachine

/-- Literal-reject control and a total verifier for `falseRelation`. -/
def falseRelationMachine : UniformTM := allRejectMachine

/-- Nonterminal timeout control. -/
def timeoutRelationMachine : UniformTM := nonterminalMachine

/-- The true control literally accepts every canonical pair. -/
theorem trueRelationMachine_decides_encodePair {n m : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    DecidesWithin trueRelationMachine
      (polyClock 0 (pairLength n m)) (encodePair x w)
      (trueRelation n m x w) := by
  simpa [trueRelationMachine, trueRelation, DecidesWithin] using
    (allAccept_acceptsWithin
      (budget := polyClock 0 (pairLength n m)) (encodePair x w))

/-- The false control literally rejects every canonical pair. -/
theorem falseRelationMachine_decides_encodePair {n m : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    DecidesWithin falseRelationMachine
      (polyClock 0 (pairLength n m)) (encodePair x w)
      (falseRelation n m x w) := by
  simpa [falseRelationMachine, falseRelation, DecidesWithin] using
    (allReject_rejectsWithin
      (budget := polyClock 0 (pairLength n m)) (encodePair x w))

/-- The total raw-word language of `falseRelation` is constantly false. -/
theorem encodedRelationLanguage_falseRelation {N : Nat} (y : Bitstring N) :
    encodedRelationLanguage falseRelation N y = false := by
  cases hdecode : decodePair y <;>
    simp [encodedRelationLanguage, falseRelation, hdecode]

/-- The same fixed rejecting machine verifies `falseRelation` at every fixed
choice of exponent. -/
theorem falseRelationMachine_verifies (verifierExponent : Nat) :
    VerifiesRelation falseRelationMachine verifierExponent falseRelation := by
  intro N y
  rw [encodedRelationLanguage_falseRelation]
  simpa [falseRelationMachine, DecidesWithin] using
    (allReject_rejectsWithin (budget := polyClock verifierExponent N) y)

/-- The empty raw word is malformed; the canonical empty/empty pair has one
separator bit and is therefore not this word. -/
def emptyRawWord : Bitstring 0 := fun i => Fin.elim0 i

theorem emptyRawWord_malformed : decodePair emptyRawWord = none := by
  simp [decodePair, decodePairList]

/--
The literal-accept control cannot be mislabeled as a total verifier for the
true relation, because total semantics requires rejection of the malformed
empty raw word.
-/
theorem trueRelationMachine_not_verifies (verifierExponent : Nat) :
    ¬ VerifiesRelation trueRelationMachine verifierExponent trueRelation := by
  intro hverify
  have hrejects :
      RejectsWithin trueRelationMachine
        (polyClock verifierExponent 0) emptyRawWord :=
    verifiesRelation_rejects_malformed hverify emptyRawWord
      emptyRawWord_malformed
  have haccepts :
      AcceptsWithin trueRelationMachine
        (polyClock verifierExponent 0) emptyRawWord := by
    simpa [trueRelationMachine] using
      (allAccept_acceptsWithin
        (budget := polyClock verifierExponent 0) emptyRawWord)
  exact (not_acceptsWithin_and_rejectsWithin
    trueRelationMachine emptyRawWord) ⟨haccepts, hrejects⟩

/--
Deadline acceptance evaluates to false for the nonterminal machine, but the
machine reaches neither verdict and decides neither Boolean answer.
-/
theorem timeoutRelationMachine_negativeControl {N budget : Nat}
    (y : Bitstring N) :
    (((timeoutRelationMachine.run budget
        (initialConfig timeoutRelationMachine budget y)).state ==
          timeoutRelationMachine.accept) = false) ∧
      ¬ DecidesWithin timeoutRelationMachine budget y true ∧
      ¬ DecidesWithin timeoutRelationMachine budget y false := by
  exact ⟨by
      simpa [timeoutRelationMachine] using
        (nonterminal_acceptFlag_false (budget := budget) y),
    by
      simpa [timeoutRelationMachine] using
        (nonterminal_not_decidesWithin_true (budget := budget) y),
    by
      simpa [timeoutRelationMachine] using
        (nonterminal_not_decidesWithin_false (budget := budget) y)⟩

/-- In particular, timeout cannot verify even the constantly-false relation. -/
theorem timeoutRelationMachine_not_verifies (verifierExponent : Nat) :
    ¬ VerifiesRelation timeoutRelationMachine verifierExponent falseRelation := by
  intro hverify
  have hdecides := hverify 0 emptyRawWord
  rw [encodedRelationLanguage_falseRelation] at hdecides
  exact (nonterminal_not_decidesWithin_false
    (budget := polyClock verifierExponent 0) emptyRawWord) (by
      simpa [timeoutRelationMachine] using hdecides)

/-- A concrete sanity instance: the constant-false language is in `UniformNP`. -/
theorem uniformNP_constFalse : UniformNP constFalse := by
  refine ⟨falseRelation, falseRelationMachine, 0, 0,
    falseRelationMachine_verifies 0, ?_⟩
  intro n x
  change false = true ↔
    ∃ m, ∃ w : Bitstring m, m ≤ polyClock 0 n ∧ false = true
  constructor
  · intro h
    exact Bool.noConfusion h
  · rintro ⟨m, w, hm, h⟩
    exact Bool.noConfusion h

end Pnp3.Complexity.Uniform.V1
