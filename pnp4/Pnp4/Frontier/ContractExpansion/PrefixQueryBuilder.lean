import Pnp4.Frontier.ContractExpansion.QueryBuilder
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Prefix query builder surface (downstream decision→search extraction)

Third reusable brick.  It instantiates the *generic* `QueryCircuitBuilder`
(merged in #1495) toward the prefix-extension route, **as an interface/contract
only**: it pins the generic builder to the prefix shape (original input =
`problem.instanceBits`, query string = the parser's ambient length `parser.M`)
and adds a *round-trip* contract relating the builder's semantic `queryValue` to
the prefix parser.

Concretely, a `PrefixQueryBuilder problem parser` is a
`QueryCircuitBuilder problem.instanceBits parser.M` whose serialized query string
`queryValue n x` parses back, via `parsePrefixInput parser`, to a genuine
`PrefixInput` about the instance `x` at target length `n`.  This is exactly the
data a later prefix-query serialization must supply, expressed without yet
committing a byte-level encoding.

Scope discipline — interface/contract only:

* connects to the generic `QueryCircuitBuilder` purely as a contract; it does
  **not** construct a concrete serializer (that is the next, parser-specific
  step that will instantiate this interface from `encodeTreeMCSPPrefixFields`);
* **no** greedy witness-bit construction;
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.

The `PrefixExtensionLanguage` *semantics* (i.e. that a decider for the language
composed with this builder is correct on promise inputs) is deliberately left to
a later layer; this file only fixes the query/circuit *shape* and the parsing
contract.
-/

/--
A prefix-route query circuit builder.

It is a generic `QueryCircuitBuilder` whose original input is the instance
(`problem.instanceBits n` bits) and whose query string is the parser's ambient
length (`parser.M n` bits), together with the round-trip contract that the
serialized query string is a genuine prefix-input about the instance.
-/
structure PrefixQueryBuilder
    (problem : SearchMCSPCompressionProblem)
    (parser : PrefixParser problem) where
  /-- The underlying generic query-circuit builder, pinned to the prefix shape. -/
  builder : QueryCircuitBuilder problem.instanceBits parser.M
  /-- Round-trip contract: at each length `n`, the serialized query string
  `builder.queryValue n x` parses (via `parser`) to a prefix-input whose target
  length is `n` and whose instance is `x`. -/
  parses_back :
    ∀ (n : Nat) (x : PrefixBitVec (problem.instanceBits n)),
      ∃ input : PrefixInput problem (parser.M n),
        parsePrefixInput parser (builder.queryValue n x) = some input
          ∧ input.n = n
          ∧ HEq input.x x

namespace PrefixQueryBuilder

variable {problem : SearchMCSPCompressionProblem} {parser : PrefixParser problem}

/-- The serialized prefix-query string produced from an instance `x`. -/
def queryValue (pqb : PrefixQueryBuilder problem parser)
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n)) :
    PrefixBitVec (parser.M n) :=
  pqb.builder.queryValue n x

/-- Compose a decider for the `parser.M n`-bit prefix-query language with the
builder, yielding a `C_DAG` circuit over the original instance bits. -/
def compose (pqb : PrefixQueryBuilder problem parser)
    (n : Nat) (decider : C_DAG.Family (parser.M n)) :
    C_DAG.Family (problem.instanceBits n) :=
  pqb.builder.compose n decider

/-- Evaluating the composed circuit on `x` runs the decider on the serialized
prefix query `queryValue n x`.  Inherited from `QueryCircuitBuilder.eval_compose`. -/
@[simp] theorem eval_compose (pqb : PrefixQueryBuilder problem parser)
    (n : Nat) (decider : C_DAG.Family (parser.M n))
    (x : PrefixBitVec (problem.instanceBits n)) :
    C_DAG.eval (pqb.compose n decider) x =
      C_DAG.eval decider (pqb.queryValue n x) :=
  pqb.builder.eval_compose n decider x

/-- The composed circuit is no larger than the decider plus the total size of
the builder's query-bit circuits.  Inherited from
`QueryCircuitBuilder.size_compose_le`. -/
theorem size_compose_le (pqb : PrefixQueryBuilder problem parser)
    (n : Nat) (decider : C_DAG.Family (parser.M n)) :
    C_DAG.size (pqb.compose n decider) ≤
      C_DAG.size decider + ∑ i, C_DAG.size (pqb.builder.queryBitCircuit n i) :=
  pqb.builder.size_compose_le n decider

/-- The round-trip contract, as a named accessor: the serialized query string
parses back to a prefix-input about `x` at target length `n`. -/
theorem queryValue_parses (pqb : PrefixQueryBuilder problem parser)
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n)) :
    ∃ input : PrefixInput problem (parser.M n),
      parsePrefixInput parser (pqb.queryValue n x) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  pqb.parses_back n x

end PrefixQueryBuilder

end ContractExpansion
end Frontier
end Pnp4
