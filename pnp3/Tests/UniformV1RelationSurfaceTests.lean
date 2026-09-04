import Complexity.Uniform.V1.RelationExamples

/-!
# Named public-surface tests for Uniform V1 relation semantics and `UniformNP`

Every authored source theorem is restated below with its complete proposition.
The wrappers are deliberately named and their types are not inferred aliases.
-/

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding

namespace Pnp3.Tests.UniformV1Relation

-- Pin every new public definition and abbreviation.
#check WitnessRelation
#check encodedRelationLanguage
#check VerifiesRelation
#check UniformNP
#check trueRelation
#check falseRelation
#check trueRelationMachine
#check falseRelationMachine
#check timeoutRelationMachine
#check emptyRawWord

theorem check_encodedRelationLanguage_encodePair
    (R : WitnessRelation) {n m : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    encodedRelationLanguage R (pairLength n m) (encodePair x w) =
      R n m x w := by
  exact encodedRelationLanguage_encodePair R x w

theorem check_encodedRelationLanguage_malformed
    (R : WitnessRelation) {N : Nat} (y : Bitstring N)
    (hdecode : decodePair y = none) :
    encodedRelationLanguage R N y = false := by
  exact encodedRelationLanguage_malformed R y hdecode

theorem check_verifiesRelation_encodePair
    {M : UniformTM} {verifierExponent : Nat} {R : WitnessRelation}
    (h : VerifiesRelation M verifierExponent R)
    {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    DecidesWithin M (polyClock verifierExponent (pairLength n m))
      (encodePair x w) (R n m x w) := by
  exact verifiesRelation_encodePair h x w

theorem check_verifiesRelation_rejects_malformed
    {M : UniformTM} {verifierExponent : Nat} {R : WitnessRelation}
    (h : VerifiesRelation M verifierExponent R)
    {N : Nat} (y : Bitstring N) (hdecode : decodePair y = none) :
    RejectsWithin M (polyClock verifierExponent N) y := by
  exact verifiesRelation_rejects_malformed h y hdecode

theorem check_verifiesRelation_rejects_encodePair
    {M : UniformTM} {verifierExponent : Nat} {R : WitnessRelation}
    (h : VerifiesRelation M verifierExponent R)
    {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (hR : R n m x w = false) :
    RejectsWithin M (polyClock verifierExponent (pairLength n m))
      (encodePair x w) := by
  exact verifiesRelation_rejects_encodePair h x w hR

theorem check_verifiesRelation_accepts_encodePair
    {M : UniformTM} {verifierExponent : Nat} {R : WitnessRelation}
    (h : VerifiesRelation M verifierExponent R)
    {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (hR : R n m x w = true) :
    AcceptsWithin M (polyClock verifierExponent (pairLength n m))
      (encodePair x w) := by
  exact verifiesRelation_accepts_encodePair h x w hR

theorem check_verifiesRelation_unique
    {M : UniformTM} {verifierExponent : Nat} {R S : WitnessRelation}
    (hR : VerifiesRelation M verifierExponent R)
    (hS : VerifiesRelation M verifierExponent S) :
    R = S := by
  exact verifiesRelation_unique hR hS

theorem check_uniformNP_iff (L : Language) :
    UniformNP L ↔
      ∃ R : WitnessRelation,
      ∃ M : UniformTM,
      ∃ verifierExponent : Nat,
      ∃ witnessExponent : Nat,
        (∀ N (y : Bitstring N),
          DecidesWithin M (polyClock verifierExponent N) y
            (encodedRelationLanguage R N y)) ∧
        ∀ n (x : Bitstring n),
          L n x = true ↔
            ∃ m, ∃ w : Bitstring m,
              m ≤ polyClock witnessExponent n ∧
              R n m x w = true := by
  exact uniformNP_iff L

theorem check_trueRelationMachine_decides_encodePair
    {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    DecidesWithin trueRelationMachine
      (polyClock 0 (pairLength n m)) (encodePair x w)
      (trueRelation n m x w) := by
  exact trueRelationMachine_decides_encodePair x w

theorem check_falseRelationMachine_decides_encodePair
    {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    DecidesWithin falseRelationMachine
      (polyClock 0 (pairLength n m)) (encodePair x w)
      (falseRelation n m x w) := by
  exact falseRelationMachine_decides_encodePair x w

theorem check_encodedRelationLanguage_falseRelation
    {N : Nat} (y : Bitstring N) :
    encodedRelationLanguage falseRelation N y = false := by
  exact encodedRelationLanguage_falseRelation y

theorem check_falseRelationMachine_verifies (verifierExponent : Nat) :
    VerifiesRelation falseRelationMachine verifierExponent falseRelation := by
  exact falseRelationMachine_verifies verifierExponent

theorem check_emptyRawWord_malformed :
    decodePair emptyRawWord = none := by
  exact emptyRawWord_malformed

theorem check_trueRelationMachine_not_verifies
    (verifierExponent : Nat) :
    ¬ VerifiesRelation
      trueRelationMachine verifierExponent trueRelation := by
  exact trueRelationMachine_not_verifies verifierExponent

theorem check_timeoutRelationMachine_negativeControl
    {N budget : Nat} (y : Bitstring N) :
    (((timeoutRelationMachine.run budget
        (initialConfig timeoutRelationMachine budget y)).state ==
          timeoutRelationMachine.accept) = false) ∧
      ¬ DecidesWithin timeoutRelationMachine budget y true ∧
      ¬ DecidesWithin timeoutRelationMachine budget y false := by
  exact timeoutRelationMachine_negativeControl y

theorem check_timeoutRelationMachine_not_verifies
    (verifierExponent : Nat) :
    ¬ VerifiesRelation
      timeoutRelationMachine verifierExponent falseRelation := by
  exact timeoutRelationMachine_not_verifies verifierExponent

theorem check_uniformNP_constFalse : UniformNP constFalse := by
  exact uniformNP_constFalse

end Pnp3.Tests.UniformV1Relation
