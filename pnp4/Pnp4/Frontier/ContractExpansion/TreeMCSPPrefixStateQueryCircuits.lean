import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSerializer
import Pnp4.Frontier.ContractExpansion.QueryComposition

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Prefix-state `(i, p)` query circuits, in the shared-bundle shape

Block 4 of the downstream decision→search extraction, written directly in the
**Option ①** architecture selected by the size-feasibility gate (`#1498`).

Block 2 (`zeroPrefixQueryBitCircuit`) handled the zero-prefix case `i = 0`: per-bit
`C_DAG` circuits over the instance bits (`tableLen n`).  This file generalizes to a
prefix-state `(i, p)` — an active witness prefix of length `i` with payload `p` —
**without re-embedding `p` as independent circuits**.  Instead the per-bit circuit
reads `tableLen n + i` inputs: the first `tableLen n` are the real instance bits,
the last `i` are the *prior bundle outputs* (the greedy bits `0..i-1`).  The payload
region of the query string is therefore an `inputProj` onto a prior-output input
(`Fin.natAdd`), exactly the head-circuit shape that plugs into the shared-bundle
greedy step `DagCircuit.snocBundleSubst` (added in `#1498`):

* x-slice region → `inputProj (Fin.castAdd i ·)` (a real instance bit);
* payload region → `inputProj (Fin.natAdd (tableLen n) ·)` (a prior bundle output);
* tag / gamma / index / pad regions → constants (the index field now encodes the
  *actual* prefix length `i`).

So each query-bit circuit is again a `constCircuit` or an `inputProj` (size `≤ 2`),
and evaluating the family on an input `Fin.append x p` reproduces the canonical
serialized prefix-state query string `encodeTreeMCSPPrefixFields` for `(n, x, i, p)`.
The parser round-trip is a direct instance of the already-proved general
`parse_encodeTreeMCSPPrefixFields`.

Scope discipline — prefix-state query value + per-bit circuits only:

* **no** `QueryCircuitBuilder` / `PrefixQueryBuilder` instance over `tableLen n + i`
  inputs (a later brick);
* **no** greedy recursion / `snocBundleSubst` threading;
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/--
Canonical raw fields for the prefix-state `(i, p)`: instance `x`, active prefix
length `i ≤ codec.witnessBits n`, prefix payload `p`.  Generalizes
`zeroPrefixFields` (the `i = 0` case).
-/
def prefixStateFields
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i) :
    CanonicalRawTreeMCSPPrefixFields codec where
  n := n
  x := x
  i := i
  prefixLength_le := hi
  p := p

/--
The serialized prefix-state query string for `(i, p)` about instance `x`, of the
parser's ambient length `treeMCSPPrefixM codec n`.  Generalizes
`zeroPrefixQueryValue`.
-/
def prefixStateQueryValue
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i) :
    PrefixBitVec (treeMCSPPrefixM codec n) :=
  encodeTreeMCSPPrefixFields codec (prefixStateFields codec n i hi x p)

/--
The concrete parser round-trips the prefix-state query string back to its
canonical parsed input.  Direct instance of `parse_encodeTreeMCSPPrefixFields`.
-/
theorem parse_prefixStateQueryValue
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i) :
    parseTreeMCSPPrefixInput threshold codec (prefixStateQueryValue codec n i hi x p) =
      some (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec
        (prefixStateFields codec n i hi x p)) :=
  parse_encodeTreeMCSPPrefixFields codec (prefixStateFields codec n i hi x p)

/--
Round-trip in the `PrefixQueryBuilder.parses_back` contract shape: the prefix-state
query string parses to a prefix-input about `x` at target length `n`.

`input.n = n` and `HEq input.x x` hold definitionally because the parsed input is
the canonical `toPrefixInput`, whose `n`/`x` fields are exactly the raw `n`/`x`.
-/
theorem prefixStateQueryValue_parses
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i) :
    ∃ input : PrefixInput
        (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n),
      parseTreeMCSPPrefixInput threshold codec (prefixStateQueryValue codec n i hi x p) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  ⟨CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec (prefixStateFields codec n i hi x p),
    parse_prefixStateQueryValue codec n i hi x p, rfl, HEq.rfl⟩

/--
The bundle-shape `C_DAG` circuit (over `tableLen n + i` inputs) computing the
`j`-th bit of the prefix-state query string `prefixStateQueryValue codec n i hi x p`.

This mirrors `encodeTreeMCSPPrefixFields` for general `(i, p)`: tag/gamma/index/pad
are constants (the index field is the big-endian code of the *actual* `i`), the
x-slice reads a real instance bit via `inputProj (Fin.castAdd i ·)`, and the
witness-prefix payload reads a prior bundle output via
`inputProj (Fin.natAdd (tableLen n) ·)`.  The prefix-length bound
`_hi : i ≤ codec.witnessBits n` is required in the signature so the circuit API
cannot be instantiated outside the parser/round-trip contract: an out-of-range `i`
would truncate the `idxWidth`-wide index field and spill payload bits into the
region the parser treats as mandatory zero padding, yielding a circuit family that
provably cannot parse as a valid prefix input.  The circuit *body* does not
otherwise depend on it.
-/
def prefixStateQueryBitCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (_hi : i ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n + i) :=
  if hTag : j.1 < tagLen then
    Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _
      (natBitBE treePrefixTag tagLen ⟨j.1, hTag⟩)
  else
    let gammaOffset := tagLen
    if hGamma : j.1 < gammaOffset + gammaLen n then
      Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _
        (gammaBit n ⟨j.1 - gammaOffset, by omega⟩)
    else
      let xOffset := tagLen + gammaLen n
      if hX : j.1 < xOffset + Pnp3.Models.Partial.tableLen n then
        Pnp3.ComplexityInterfaces.DagCircuit.inputProj
          (Fin.castAdd i ⟨j.1 - xOffset, by omega⟩)
      else
        let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
        if hI : j.1 < iOffset + idxWidth codec.witnessBits n then
          Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _
            (natBitBE i (idxWidth codec.witnessBits n) ⟨j.1 - iOffset, by omega⟩)
        else
          let pOffset := iOffset + idxWidth codec.witnessBits n
          if hP : j.1 < pOffset + i then
            Pnp3.ComplexityInterfaces.DagCircuit.inputProj
              (Fin.natAdd (Pnp3.Models.Partial.tableLen n) ⟨j.1 - pOffset, by omega⟩)
          else
            Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _ false

/--
Each prefix-state query-bit circuit really computes the corresponding bit of the
semantic prefix-state query string, when fed the combined input
`Fin.append x p` (real instance bits followed by the prior-output payload).  The
proof is a region-by-region case split matching the `encodeTreeMCSPPrefixFields`
cascade; the x-slice and payload regions discharge via `Fin.append_left` /
`Fin.append_right`.
-/
theorem eval_prefixStateQueryBitCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (prefixStateQueryBitCircuit codec n i hi j) (Fin.append x p) =
      prefixStateQueryValue codec n i hi x p j := by
  simp only [prefixStateQueryValue, prefixStateFields, encodeTreeMCSPPrefixFields,
    prefixStateQueryBitCircuit]
  split_ifs with hTag hGamma hX hI hP <;>
    simp only [C_DAG,
      Pnp3.ComplexityInterfaces.DagCircuit.eval_constCircuit,
      Pnp3.ComplexityInterfaces.DagCircuit.eval_inputProj,
      Fin.append_left, Fin.append_right]

/--
Every prefix-state query-bit circuit has size at most `2` (a `constCircuit` has
size `2`, an `inputProj` has size `1`) — uniform in `j`, `i`, and the prior
outputs, as required for the shared-bundle greedy step to stay polynomial.
-/
theorem size_prefixStateQueryBitCircuit_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.size (prefixStateQueryBitCircuit codec n i hi j) ≤ 2 := by
  simp only [prefixStateQueryBitCircuit]
  split_ifs <;> simp [C_DAG]

end ContractExpansion
end Frontier
end Pnp4
