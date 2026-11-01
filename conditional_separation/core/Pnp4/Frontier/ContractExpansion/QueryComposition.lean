import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter
import Complexity.DagCompose

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# DAG query composition for the decision→search extraction

First reusable brick of the downstream *decision→search extraction*: composing a
DAG-decider for a query language with DAG-circuits that compute each query bit
from the original input.

The frozen `pnp3` composition layer (`Complexity.DagCompose`) already provides
the workhorse `DagCircuit.substInputs` together with its `eval` and `size`
correctness lemmas.  Here we phrase the single composition step the extraction
needs *in `pnp4`'s own `C_DAG` circuit-family view*, so that downstream
extraction modules never have to reach across into the raw `pnp3` `DagCircuit`
API.

`C_DAG` is only an adapter: `C_DAG.Family n` is definitionally
`Pnp3.ComplexityInterfaces.DagCircuit n`, and `C_DAG.eval`/`C_DAG.size` are the
frozen `DagCircuit` evaluator and size measure.  So this file introduces **no**
new circuit semantics.

Scope discipline — this is a *reusable primitive*, not an endpoint:

* **no** `PrefixExtensionLanguage` parser/serialization logic;
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge or endpoint wrapper;
* **no** `P ≠ NP` / `NP ⊄ P/poly` consequence.

It proves exactly one thing: *a DAG-decider composed with DAG query-builders is
again a `C_DAG` circuit, with the expected `eval` and a `size` bound.*
-/

/-- **DAG query composition.**

Given a `C_DAG` decider over `queryBits` query bits and, for each query bit, a
`C_DAG` circuit computing that bit from the original `inputBits`-bit input,
produce the `C_DAG` circuit over the original input that first computes every
query bit and then runs the decider.

This is exactly the frozen `pnp3` input-substitution `DagCircuit.substInputs`,
re-exposed through the `C_DAG` family view (`C_DAG.Family _` is definitionally
`DagCircuit _`). -/
def composeDeciderWithQuery
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    C_DAG.Family inputBits :=
  Pnp3.ComplexityInterfaces.DagCircuit.substInputs decider queryBit

/-- Evaluating the composed circuit on `x` runs the decider on the bit-vector
whose `j`-th coordinate is the `j`-th query circuit evaluated on `x`.

Direct re-export of `DagCircuit.eval_substInputs` through the `C_DAG` view. -/
@[simp] theorem eval_composeDeciderWithQuery
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits)
    (x : AlgorithmsToLowerBounds.BitVec inputBits) :
    C_DAG.eval (composeDeciderWithQuery decider queryBit) x =
      C_DAG.eval decider (fun j => C_DAG.eval (queryBit j) x) :=
  Pnp3.ComplexityInterfaces.DagCircuit.eval_substInputs decider queryBit x

/-- The composed circuit is no larger than the decider plus the total size of
the query-bit circuits.

Direct re-export of `DagCircuit.size_substInputs_le` through the `C_DAG` view. -/
theorem size_composeDeciderWithQuery_le
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    C_DAG.size (composeDeciderWithQuery decider queryBit) ≤
      C_DAG.size decider + ∑ j, C_DAG.size (queryBit j) :=
  Pnp3.ComplexityInterfaces.DagCircuit.size_substInputs_le decider queryBit

end ContractExpansion
end Frontier
end Pnp4
