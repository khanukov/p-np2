import Complexity.Uniform.V1.Relation

/-!
# Versioned advice-free `UniformNP`

`UniformNP` lives in the same `Uniform.V1` namespace as the finite machine,
clock, `UniformP`, and pair encoding that define its semantics. The defining
existentials choose one relation, one finite verifier, one verifier clock
exponent, and one independent witness-length exponent before any input is
quantified.
-/

namespace Pnp3.Complexity.Uniform.V1

/--
Advice-free uniform NP with total raw-word verifier correctness.

* `M` is one fixed finite `UniformTM`.
* `verifierExponent` is fixed and clocks `M` by the actual encoded input
  length.
* `witnessExponent` is independently fixed and bounds witness length in the
  original input length.
* `false` is interpreted by `DecidesWithin` as literal rejection.
-/
def UniformNP (L : Language) : Prop :=
  ∃ R : WitnessRelation,
  ∃ M : UniformTM,
  ∃ verifierExponent : Nat,
  ∃ witnessExponent : Nat,
    VerifiesRelation M verifierExponent R ∧
    ∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ m, ∃ w : Bitstring m,
          m ≤ polyClock witnessExponent n ∧
          R n m x w = true

/-- An explicit restatement that pins the intended quantifier order. -/
theorem uniformNP_iff (L : Language) :
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
  rfl

end Pnp3.Complexity.Uniform.V1
