import Pnp4.Frontier.ContractExpansion.QueryComposition

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Query circuit builder interface (downstream decision→search extraction)

Second reusable brick of the downstream extraction.  The previous brick
(`QueryComposition.composeDeciderWithQuery`) composes a `C_DAG` decider with a
*bare function* `Fin queryBits → C_DAG.Family inputBits` of query-bit circuits.
This file adds the missing **semantics**: a `QueryCircuitBuilder` packages, at
every target length `n`, the intended query string `queryValue n x` together
with one `C_DAG` circuit per query bit *and a proof that those circuits actually
compute that query string*, plus a uniform per-bit size bound.

This is exactly the data the next layers will need: a concrete prefix-query
serialization is just a `QueryCircuitBuilder` whose `queryValue` is a serialized
`PrefixInput`, and the greedy decision steps will read off `queryValue`.

Scope discipline — generic semantic wrapper, not an endpoint:

* **no** `PrefixExtensionLanguage` / `PrefixParser` / `PrefixInput` logic
  (this layer is deliberately route-agnostic);
* **no** greedy witness-bit construction;
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.

It only lifts `composeDeciderWithQuery` (and its `eval`/`size` lemmas) to act on
a semantically-specified family of query-bit circuits.
-/

/--
A circuit builder for query strings.

At target length `n`, an original input has `inputBits n` bits and the query
string has `queryBits n` bits.  The builder provides both the semantic query
value `queryValue n x` and one `C_DAG` circuit `queryBitCircuit n i` computing
each query bit `i`, with a correctness proof and a uniform per-bit size bound.
-/
structure QueryCircuitBuilder
    (inputBits queryBits : Nat → Nat) where
  /-- The intended query string computed from the original input. -/
  queryValue :
    ∀ n : Nat,
      AlgorithmsToLowerBounds.BitVec (inputBits n) →
        AlgorithmsToLowerBounds.BitVec (queryBits n)
  /-- A `C_DAG` circuit over the original input computing the `i`-th query bit. -/
  queryBitCircuit :
    ∀ n : Nat,
      Fin (queryBits n) →
        C_DAG.Family (inputBits n)
  /-- Each query-bit circuit really computes the corresponding query bit. -/
  queryBit_correct :
    ∀ n : Nat,
      ∀ i : Fin (queryBits n),
      ∀ x : AlgorithmsToLowerBounds.BitVec (inputBits n),
        C_DAG.eval (queryBitCircuit n i) x = queryValue n x i
  /-- A uniform per-bit circuit-size bound at each length. -/
  sizeBound : Nat → Nat
  /-- Every query-bit circuit respects the per-bit size bound. -/
  size_le :
    ∀ n : Nat,
      ∀ i : Fin (queryBits n),
        C_DAG.size (queryBitCircuit n i) ≤ sizeBound n

namespace QueryCircuitBuilder

/-- Compose a decider over the query bits with the builder's query-bit circuits,
yielding a `C_DAG` circuit over the original input. -/
def compose
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.Family (inputBits n) :=
  composeDeciderWithQuery decider (builder.queryBitCircuit n)

/-- Evaluating the composed circuit on `x` runs the decider on the builder's
intended query string `queryValue n x`. -/
@[simp] theorem eval_compose
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n))
    (x : AlgorithmsToLowerBounds.BitVec (inputBits n)) :
    C_DAG.eval (builder.compose n decider) x =
      C_DAG.eval decider (builder.queryValue n x) := by
  unfold compose
  rw [eval_composeDeciderWithQuery]
  congr 1
  funext i
  exact builder.queryBit_correct n i x

/-- The composed circuit is no larger than the decider plus the total size of
the builder's query-bit circuits. -/
theorem size_compose_le
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.size (builder.compose n decider) ≤
      C_DAG.size decider + ∑ i, C_DAG.size (builder.queryBitCircuit n i) := by
  unfold compose
  exact size_composeDeciderWithQuery_le decider (builder.queryBitCircuit n)

/-- Closed-form size bound using the uniform per-bit `sizeBound`: the composed
circuit is no larger than the decider plus `queryBits n * sizeBound n`. -/
theorem size_compose_le_bound
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.size (builder.compose n decider) ≤
      C_DAG.size decider + (queryBits n) * builder.sizeBound n := by
  calc
    C_DAG.size (builder.compose n decider)
        ≤ C_DAG.size decider + ∑ i, C_DAG.size (builder.queryBitCircuit n i) :=
          builder.size_compose_le n decider
    _ ≤ C_DAG.size decider + ∑ _i : Fin (queryBits n), builder.sizeBound n :=
          Nat.add_le_add_left
            (Finset.sum_le_sum (fun i _hi => builder.size_le n i)) _
    _ = C_DAG.size decider + (queryBits n) * builder.sizeBound n := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end QueryCircuitBuilder

end ContractExpansion
end Frontier
end Pnp4
