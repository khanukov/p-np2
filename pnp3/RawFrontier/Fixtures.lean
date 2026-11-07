import RawFrontier.Syntactic
import RawFrontier.Capacity
namespace RawFrontier.Fixtures
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open FixedGammaTargetRegisterDecrement (borrow decBit)
attribute [local irreducible] UniformTM.run
/-- Three real raw-origin negative words: empty content, missing gamma, and
n255 capacity overflow. These use generic execution proofs, not host timeouts. -/
theorem negative_words (k : Nat) :
    (∃ t, t ≤ 512 ∧
      ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) 64
        (encodePair (Fin.elim0 : Bitstring 0) Fin.elim0))).state=(AllArityCursor.machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k 0 0 Fin.elim0 Fin.elim0=false) ∧
    (let x : Bitstring 16 := fun i => if i.val < 8 then (178:Nat).testBit (7-i.val) else false
      ∃ t, t ≤ 147968 ∧
        ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) 18496
          (encodePair x (Fin.elim0 : Bitstring 0)))).state=(AllArityCursor.machine k).reject ∧
        PartAEndpoint.thresholdContentWitnessRelation k 16 0 x Fin.elim0=false) ∧
    (let x : Bitstring 25 := fun i => if i.val < 8 then (178:Nat).testBit (7-i.val) else i.val==16
      ∃ t, t ≤ 346112 ∧
        ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) 43264
          (encodePair x (Fin.elim0 : Bitstring 0)))).state=(AllArityCursor.machine k).reject ∧
        PartAEndpoint.thresholdContentWitnessRelation k 25 0 x Fin.elim0=false) := by
  refine ⟨?_,?_,?_⟩
  · obtain ⟨t,price,reject,_first,_safe,sound,_tape,_head⟩ := syntactic_reject k
      (Fin.elim0 : Bitstring 0) Fin.elim0 (Or.inl (by decide))
    exact ⟨t,price,reject,sound⟩
  · dsimp only
    let x : Bitstring 16 := fun i => if i.val < 8 then (178:Nat).testBit (7-i.val) else false
    obtain ⟨t,price,reject,_first,_safe,sound,_tape,_head⟩ := syntactic_reject k x
      (Fin.elim0 : Bitstring 0) (Or.inr (by decide))
    exact ⟨t,price,reject,sound⟩
  · dsimp only
    let x : Bitstring 25 := fun i => if i.val < 8 then (178:Nat).testBit (7-i.val) else i.val==16
    have digits : ∀ j, j ≤ 8 → (255:Nat).testBit (8-j)=decBit x (Fin.elim0 : Bitstring 0) 8
        (borrow x (Fin.elim0 : Bitstring 0) 8) j := by
      intro j hj
      interval_cases j <;> decide
    have high : ∀ b, 8 < b → (255:Nat).testBit b=false :=
      (FixedGammaTargetUnaryCountdownIteration.high_iff_lt 255 8).2 (by decide)
    obtain ⟨t,price,reject,_first,_safe,sound,_head,_tape⟩ := capacity_reject k x
      (Fin.elim0 : Bitstring 0) (by decide) (by decide) (by decide) digits high (by decide)
    exact ⟨t,price,reject,sound⟩
theorem check_negative_words (k : Nat) :
    (∃ t, t ≤ 512 ∧
      ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) 64
        (encodePair (Fin.elim0 : Bitstring 0) Fin.elim0))).state=(AllArityCursor.machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k 0 0 Fin.elim0 Fin.elim0=false) ∧
    (let x : Bitstring 16 := fun i => if i.val < 8 then (178:Nat).testBit (7-i.val) else false
      ∃ t, t ≤ 147968 ∧
        ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) 18496
          (encodePair x (Fin.elim0 : Bitstring 0)))).state=(AllArityCursor.machine k).reject ∧
        PartAEndpoint.thresholdContentWitnessRelation k 16 0 x Fin.elim0=false) ∧
    (let x : Bitstring 25 := fun i => if i.val < 8 then (178:Nat).testBit (7-i.val) else i.val==16
      ∃ t, t ≤ 346112 ∧
        ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) 43264
          (encodePair x (Fin.elim0 : Bitstring 0)))).state=(AllArityCursor.machine k).reject ∧
        PartAEndpoint.thresholdContentWitnessRelation k 25 0 x Fin.elim0=false) := @RawFrontier.Fixtures.negative_words k
end RawFrontier.Fixtures
#print axioms RawFrontier.Fixtures.negative_words
#print axioms RawFrontier.Fixtures.check_negative_words
