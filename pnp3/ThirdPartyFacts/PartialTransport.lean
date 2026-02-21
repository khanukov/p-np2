import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Core.BooleanBasics
import Facts.LocalityLift.Exports
import Models.Model_PartialMCSP

namespace Pnp3
namespace ThirdPartyFacts

/-- Normal form for partial-input length arithmetic. -/
@[simp] lemma two_pow_mul_two_eq_two_mul_two_pow (n : Nat) :
    2 ^ n * 2 = 2 * 2 ^ n := by
  omega

@[simp] lemma partialInputLen_nf (n : Nat) :
    Models.Partial.inputLen n = 2 * 2 ^ n := by
  simp [Models.Partial.inputLen, Models.Partial.tableLen, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

@[simp] lemma card_cast {α β : Type} (h : α = β) (s : Finset α) :
    (cast (congrArg Finset h) s).card = s.card := by
  cases h
  rfl

/-- Reindex a restriction along an equality of lengths. -/
def castRestriction {n m : Nat} (h : n = m)
    (r : Facts.LocalityLift.Restriction n) :
    Facts.LocalityLift.Restriction m := by
  cases h
  simpa using r

/-- Reindex a bit-vector along an equality of lengths. -/
def castBitVec {n m : Nat} (h : n = m) (x : Core.BitVec n) : Core.BitVec m := by
  cases h
  simpa using x

@[simp] lemma castBitVec_rfl {n : Nat} (x : Core.BitVec n) :
    castBitVec (rfl : n = n) x = x := rfl

@[simp] lemma castRestriction_rfl {n : Nat} (r : Facts.LocalityLift.Restriction n) :
    castRestriction (rfl : n = n) r = r := rfl

@[simp] lemma castRestriction_alive_card {n m : Nat}
    (h : n = m) (r : Facts.LocalityLift.Restriction n) :
    (castRestriction h r).alive.card = r.alive.card := by
  cases h
  rfl

/--
Transport stability of `decide` through a length cast of restrictions.
-/
theorem stable_of_stable_cast
    {n m : Nat} (h : n = m)
    (decide : Core.BitVec m → Bool)
    (r : Facts.LocalityLift.Restriction n)
    (hstable :
      ∀ x : Core.BitVec n,
        decide (castBitVec h (r.apply x)) = decide (castBitVec h x)) :
    ∀ x : Core.BitVec m,
      decide ((castRestriction h r).apply x) = decide x := by
  cases h
  intro x
  simpa using hstable x

end ThirdPartyFacts
end Pnp3
