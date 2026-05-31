import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixQueryCircuits
import Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Concrete zero-prefix `PrefixQueryBuilder` instance (downstream extraction)

Sixth reusable brick.  The previous bricks supplied, separately, the *generic*
builder interfaces (`QueryCircuitBuilder`, `PrefixQueryBuilder`), the *semantic*
zero-prefix query string with its parser round-trip
(`zeroPrefixQueryValue`, `zeroPrefixQueryValue_parses`), and the *per-bit query
circuits* (`zeroPrefixQueryBitCircuit` + eval/size).  This file wires them
together into a fully concrete `PrefixQueryBuilder` for the tree-MCSP prefix
parser, specialized to the zero-prefix (`i = 0`) case.

Concretely:

* `zeroPrefixQueryCircuitBuilder codec` is the generic `QueryCircuitBuilder`
  whose query value is `zeroPrefixQueryValue codec`, whose per-bit circuits are
  `zeroPrefixQueryBitCircuit codec`, and whose uniform per-bit size bound is `2`;
* `treeMCSPZeroPrefixQueryBuilder threshold codec` packages it as a
  `PrefixQueryBuilder` for `treeMCSPConcretePrefixParser`, with the round-trip
  contract discharged by `zeroPrefixQueryValue_parses`.

This is the first fully-assembled `PrefixQueryBuilder` *instance* (every previous
prefix-route brick was an interface or a single component).

Scope discipline — concrete builder instance only:

* this is still the *zero-prefix* serialization (`i = 0`); the prefix-state
  `(i, p)` generalization is a later brick;
* **no** greedy witness-bit construction;
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

/--
The generic query-circuit builder for the zero-prefix tree-MCSP query: instance
bits are the truth table (`tableLen n`), query bits are the parser's ambient
length (`treeMCSPPrefixM codec n`), assembled from the zero-prefix per-bit
circuits and their eval/size lemmas.
-/
def zeroPrefixQueryCircuitBuilder
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :
    QueryCircuitBuilder
      (fun n => Pnp3.Models.Partial.tableLen n)
      (fun n => treeMCSPPrefixM codec n) where
  queryValue := zeroPrefixQueryValue codec
  queryBitCircuit := zeroPrefixQueryBitCircuit codec
  queryBit_correct := fun n i x => eval_zeroPrefixQueryBitCircuit codec n x i
  sizeBound := fun _ => 2
  size_le := fun n i => size_zeroPrefixQueryBitCircuit_le codec n i

/--
The concrete zero-prefix `PrefixQueryBuilder` instance for the tree-MCSP prefix
parser: the generic builder above, packaged with the parser round-trip contract
from `zeroPrefixQueryValue_parses`.
-/
def treeMCSPZeroPrefixQueryBuilder
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold) :
    PrefixQueryBuilder
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPConcretePrefixParser threshold codec) where
  builder := zeroPrefixQueryCircuitBuilder codec
  parses_back := fun n x => zeroPrefixQueryValue_parses codec n x

/--
The instance's serialized query value is exactly `zeroPrefixQueryValue`
(definitional sanity check that the wiring did not reshape the semantics).
-/
theorem treeMCSPZeroPrefixQueryBuilder_queryValue
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (treeMCSPZeroPrefixQueryBuilder threshold codec).queryValue n x =
      zeroPrefixQueryValue codec n x :=
  rfl

end ContractExpansion
end Frontier
end Pnp4
