import Pnp4.Frontier.ContractExpansion.PrefixParserConvention

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Concrete zero-prefix tree-MCSP serializer round-trip (downstream extraction)

Fourth reusable brick.  The previous bricks were generic/contract-level
(`QueryCircuitBuilder`, `PrefixQueryBuilder`).  This file supplies the *concrete
semantic serializer* half of a future `PrefixQueryBuilder` instance for the
tree-MCSP prefix convention, **without any circuits yet**.

It defines the *zero-prefix* query string for an instance `x` (the serialized
prefix-input whose active prefix length is `i = 0`, i.e. no witness bits fixed)
and shows it round-trips through the concrete parser: it parses back to a genuine
`PrefixInput` whose target length is `n` and whose instance is `x`.  This is
exactly the `PrefixQueryBuilder.parses_back` contract shape, instantiated for the
tree-MCSP parser via the already-proved encoder/parser inverse
`parse_encodeTreeMCSPPrefixFields`.

Scope discipline — semantic serializer round-trip only:

* **no** `queryBitCircuit` / per-bit `C_DAG` circuits (next brick);
* **no** `QueryCircuitBuilder` / `PrefixQueryBuilder` instance (later brick);
* **no** greedy witness-bit construction;
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/--
The canonical raw fields for the *zero-prefix* tree-MCSP query at instance `x`:
target length `n`, truth table `x`, and an empty active prefix (`i = 0`, so the
prefix payload `p : PrefixBitVec 0` is the empty function).
-/
def zeroPrefixFields
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    CanonicalRawTreeMCSPPrefixFields codec where
  n := n
  x := x
  i := 0
  prefixLength_le := Nat.zero_le _
  p := fun i => i.elim0

/--
The serialized zero-prefix query string for instance `x`, of the parser's
ambient length `treeMCSPPrefixM codec n`.
-/
def zeroPrefixQueryValue
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    PrefixBitVec (treeMCSPPrefixM codec n) :=
  encodeTreeMCSPPrefixFields codec (zeroPrefixFields codec n x)

/--
The concrete parser round-trips the zero-prefix query string back to its
canonical parsed input.  Direct instance of `parse_encodeTreeMCSPPrefixFields`.
-/
theorem parse_zeroPrefixQueryValue
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    parseTreeMCSPPrefixInput threshold codec (zeroPrefixQueryValue codec n x) =
      some (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec
        (zeroPrefixFields codec n x)) :=
  parse_encodeTreeMCSPPrefixFields codec (zeroPrefixFields codec n x)

/--
Round-trip in the `PrefixQueryBuilder.parses_back` contract shape: the zero-prefix
query string parses to a prefix-input about `x` at target length `n`.

`input.n = n` and `HEq input.x x` hold definitionally because the parsed input is
the canonical `toPrefixInput`, whose `n`/`x` fields are exactly the raw `n`/`x`.
-/
theorem zeroPrefixQueryValue_parses
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    ∃ input : PrefixInput
        (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n),
      parseTreeMCSPPrefixInput threshold codec (zeroPrefixQueryValue codec n x) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  ⟨CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec (zeroPrefixFields codec n x),
    parse_zeroPrefixQueryValue codec n x, rfl, HEq.rfl⟩

end ContractExpansion
end Frontier
end Pnp4
