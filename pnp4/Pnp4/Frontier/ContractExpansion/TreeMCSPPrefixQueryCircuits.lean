import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSerializer
import Pnp4.Frontier.ContractExpansion.QueryComposition

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Zero-prefix query-bit circuits (downstream decision→search extraction)

Fifth reusable brick.  The previous brick
(`TreeMCSPPrefixSerializer.zeroPrefixQueryValue`) gave the *semantic* zero-prefix
query string and its parser round-trip, **without any circuits**.  This file
supplies the missing per-bit `C_DAG` circuits: for each query-bit position `j`,
a small `C_DAG` circuit over the instance bits (`tableLen n`) that computes the
`j`-th bit of `zeroPrefixQueryValue codec n x`, together with a correctness proof
and a uniform per-bit size bound (`≤ 2`).

These are exactly the `queryBitCircuit`/`queryBit_correct`/`size_le` data a
`QueryCircuitBuilder` needs; the concrete builder instance is the next brick.

The construction is a direct mirror of `encodeTreeMCSPPrefixFields` specialized to
the zero-prefix case `i = 0`: every encoded bit is either a constant (the version
tag byte, the Elias-gamma length code of `n`, the all-zero index field, and the
empty/padding suffix) or exactly one coordinate of the truth table `x` (the
`tableLen n`-wide x-slice).  So each query-bit circuit is a `constCircuit` or an
`inputProj`.

Scope discipline — per-bit query circuits only:

* **no** `QueryCircuitBuilder` / `PrefixQueryBuilder` instance (next brick);
* **no** prefix-state `(i, p)` generalization;
* **no** greedy witness-bit construction;
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/--
The `C_DAG` circuit (over the instance bits `tableLen n`) computing the `j`-th bit
of the zero-prefix query string `zeroPrefixQueryValue codec n x`.

This mirrors `encodeTreeMCSPPrefixFields` for `i = 0`: the tag, gamma, index, and
(empty) prefix/pad regions are constants, while the x-slice region reads one
coordinate of the instance via `inputProj`.
-/
def zeroPrefixQueryBitCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
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
          ⟨j.1 - xOffset, by omega⟩
      else
        let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
        if hI : j.1 < iOffset + idxWidth codec.witnessBits n then
          Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _
            (natBitBE 0 (idxWidth codec.witnessBits n) ⟨j.1 - iOffset, by omega⟩)
        else
          Pnp3.ComplexityInterfaces.DagCircuit.constCircuit _ false

/--
Each zero-prefix query-bit circuit really computes the corresponding bit of the
semantic zero-prefix query string.  The proof is a region-by-region case split
that exactly matches the `encodeTreeMCSPPrefixFields` cascade for `i = 0`.
-/
theorem eval_zeroPrefixQueryBitCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (zeroPrefixQueryBitCircuit codec n j) x =
      zeroPrefixQueryValue codec n x j := by
  simp only [zeroPrefixQueryValue, zeroPrefixFields, encodeTreeMCSPPrefixFields,
    zeroPrefixQueryBitCircuit]
  -- The encoder cascade carries an extra (vacuous, `i = 0`) prefix-payload region
  -- that the circuit has no branch for; that branch contradicts `hI` and is closed
  -- by `omega`, the rest reduce via the leaf `eval` lemmas.
  split_ifs with hTag hGamma hX hI hP <;>
    first
      | (exfalso; omega)
      | simp [C_DAG,
          Pnp3.ComplexityInterfaces.DagCircuit.eval_constCircuit,
          Pnp3.ComplexityInterfaces.DagCircuit.eval_inputProj]

/--
Every zero-prefix query-bit circuit has size at most `2` (a `constCircuit` has
size `2`, an `inputProj` has size `1`).
-/
theorem size_zeroPrefixQueryBitCircuit_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.size (zeroPrefixQueryBitCircuit codec n j) ≤ 2 := by
  simp only [zeroPrefixQueryBitCircuit]
  split_ifs <;> simp [C_DAG]

end ContractExpansion
end Frontier
end Pnp4
