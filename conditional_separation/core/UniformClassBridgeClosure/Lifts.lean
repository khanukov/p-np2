import UniformClassBridgeClosure.Transfer
namespace UniformClassBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing PairEncoding
/-- SAME relation, every raw encoded word, fixed compiled table/exponent. -/
theorem verifier (M : UniformTM) (c : Nat) (R : WitnessRelation) (h:VerifiesRelation M c R) :
    Ordinary.Verifies (StandardTMBridgeClosure.compile M) (some (M.accept,0)) (some (M.reject,0)) (4*c+4) R := by
  intro N y
  exact (operational M c N y _ (h N y)).1
/-- One-way same-language lift; finite control and clock precede all inputs. -/
theorem p_lift (L : Language) (h:UniformP L) : Ordinary.UniformP L := by
  obtain ⟨M,c,correct⟩:=h
  refine ⟨Option (Fin M.stateCount × Fin 4),inferInstance,inferInstance,
    StandardTMBridgeClosure.compile M,some (M.accept,0),some (M.reject,0),4*c+4,?_⟩
  intro N y
  exact (operational M c N y (L N y) (correct N y)).1
/-- Explicit parameter-preserving verifier/witness lift: R and witnessExponent
are FREE fixed parameters of the conclusion, not newly existential choices. -/
theorem np_parameters (L : Language) (R : WitnessRelation) (M : UniformTM)
    (c witnessExponent : Nat) (correct:VerifiesRelation M c R)
    (witnesses:∀ n (x : Bitstring n),L n x=true ↔
      ∃ m,∃ w : Bitstring m,m ≤ polyClock witnessExponent n ∧ R n m x w=true) :
    Ordinary.Verifies (StandardTMBridgeClosure.compile M) (some (M.accept,0)) (some (M.reject,0)) (4*c+4) R ∧
    ∀ n (x : Bitstring n),L n x=true ↔
      ∃ m,∃ w : Bitstring m,m ≤ n^witnessExponent+witnessExponent ∧ R n m x w=true :=
  ⟨verifier M c R correct,witnesses⟩
/-- The very SAME R and witnessExponent are retained; only the verifier clock
changes transparently to 4*c+4. No current PartA verifier is assumed here. -/
theorem np_lift (L : Language) (h:UniformNP L) : Ordinary.UniformNP L := by
  obtain ⟨R,M,c,witnessExponent,correct,witnesses⟩:=h
  obtain ⟨verified,sameWitnesses⟩:=np_parameters L R M c witnessExponent correct witnesses
  exact ⟨R,Option (Fin M.stateCount × Fin 4),inferInstance,inferInstance,
    StandardTMBridgeClosure.compile M,some (M.accept,0),some (M.reject,0),4*c+4,
    witnessExponent,verified,sameWitnesses⟩
/-- Malformed words reach literal halting reject, not timeout/default false. -/
theorem malformed (M : UniformTM) (c : Nat) (R : WitnessRelation) (h:VerifiesRelation M c R)
    (N : Nat) (y : Bitstring N) (bad:decodePair y=none) :
    Ordinary.Decides (StandardTMBridgeClosure.compile M) (some (M.accept,0)) (some (M.reject,0))
      (N^(4*c+4)+(4*c+4)) y false := by
  have result:=verifier M c R h N y
  simpa only [bad] using result
/-- Canonical pair correctness uses the original lengths/query/witness. -/
theorem canonical (M : UniformTM) (c : Nat) (R : WitnessRelation) (h:VerifiesRelation M c R)
    (n m : Nat) (x : Bitstring n) (w : Bitstring m) :
    Ordinary.Decides (StandardTMBridgeClosure.compile M) (some (M.accept,0)) (some (M.reject,0))
      ((pairLength n m)^(4*c+4)+(4*c+4)) (encodePair x w) (R n m x w) := by
  have result:=verifier M c R h (pairLength n m) (encodePair x w)
  change Ordinary.Decides _ _ _ _ _ (encodedRelationLanguage R _ _) at result
  simpa only [encodedRelationLanguage_encodePair] using result
example : Target.Transfer ∧ Target.Lifts := ⟨operational,verifier,p_lift,np_lift⟩
#print axioms verifier
#print axioms p_lift
#print axioms np_parameters
#print axioms np_lift
#print axioms malformed
#print axioms canonical
end UniformClassBridgeClosure
