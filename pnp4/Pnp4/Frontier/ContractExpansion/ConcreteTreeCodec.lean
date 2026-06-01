import Pnp4.Frontier.ContractExpansion.CircuitDecodeDepthFree
import Pnp4.Frontier.ContractExpansion.ConcreteCodecGap
import Pnp4.Frontier.ContractExpansion.WitnessGrowthReduction
import Pnp4.Frontier.ContractExpansion.PrefixParserConvention

namespace Pnp4
namespace Frontier
namespace ContractExpansion

/-!
# A concrete `TreeCircuitWitnessCodec`

Block 12e of the downstream extraction effort — the **final assembly**.  This is the
**first concrete `TreeCircuitWitnessCodec`** in the development, closing the
"no concrete codec exists" finding from Block 12a (`ConcreteCodecGap.lean`).

All the encoder-level ingredients are now in hand:

* a native prefix-free encoder/decoder over `Pnp3.Models.Circuit` and a round-trip
  for **all** `n` (`CircuitTreeBridge.lean`, after the `h_pos` removal);
* a depth-free decoder `decodeCircuitFull` (`CircuitDecodeDepthFree.lean`);
* matching encoding-length **upper** and **lower** bounds
  (`CircuitEncodingLength.lean`, `CircuitDecodeDepthFree.lean`);
* the packing reduction `SelfDelimitingCircuitCode.toCodec` (`ConcreteCodecGap.lean`).

Assembly choices:

* **width schedule** `width n := bitLength n`, valid because `n < 2 ^ bitLength n`
  (`nat_lt_two_pow_bitLength`);
* **witness width** `witnessBits n := (bitLength n + 4) · threshold n`, which
  dominates the encoding length of every circuit of size `≤ threshold n` (upper
  bound `(bitLength n + 4) · size`).

`treeCircuitWitnessCodec threshold` is then `(treeSelfDelimitingCode threshold).toCodec`.

Finally, **under the explicit assumption** `PolyBoundedInTable threshold` (the
threshold is polynomial in the truth-table length), the codec's `witnessBits` is
`PolyBoundedInTable`, so it packages as a `PolynomialWitnessCodec` — which (Block 10a)
yields the full `TreeMCSPExtractionGrowthAssumptions`.  This is the point at which the
growth premise becomes the *single* honest assumption `PolyBoundedInTable threshold`.

Scope discipline — concrete codec construction only:

* `PolyBoundedInTable threshold` is an **explicit assumption** for the
  `PolynomialWitnessCodec` packaging — **not** proved here;
* **no** `NoPolynomialBoundedSearchSolver` / lower-bound proof, **no** NP-verifier
  construction, **no** `SearchMCSPMagnificationContract` change, **no** endpoint.
-/

/-- The concrete self-delimiting circuit code for the tree-MCSP codec: encode through
the bridge at width `bitLength n`, decode with the depth-free decoder, and bound the
length by `(bitLength n + 4) · threshold n`. -/
def treeSelfDelimitingCode (threshold : Nat → Nat) : SelfDelimitingCircuitCode threshold where
  witnessBits := fun n => (bitLength n + 4) * threshold n
  enc := fun n c => encodeCircuit (bitLength n) (Nat.le_of_lt (nat_lt_two_pow_bitLength n)) c
  dec := fun n bits => decodeCircuitFull n (bitLength n) bits
  dec_enc := fun n c rest =>
    decodeCircuitFull_encodeCircuit n (bitLength n)
      (Nat.le_of_lt (nat_lt_two_pow_bitLength n)) c rest
  enc_len_le := fun n c h =>
    le_trans
      (length_encodeCircuit_le (bitLength n) (Nat.le_of_lt (nat_lt_two_pow_bitLength n)) c)
      (Nat.mul_le_mul (le_refl _) h)

/-- **The concrete tree-circuit witness codec.**  Assembled from the self-delimiting
code by the zero-padding packing reduction. -/
def treeCircuitWitnessCodec (threshold : Nat → Nat) : TreeCircuitWitnessCodec threshold :=
  (treeSelfDelimitingCode threshold).toCodec

/-- The truth-table length dominates `bitLength`: `bitLength n ≤ n ≤ tableLen n`. -/
theorem polyBoundedInTable_bitLength : PolyBoundedInTable bitLength :=
  PolyBoundedInTable.of_le
    (fun n => le_trans (bitLength_le_self n) (Nat.le_of_lt Nat.lt_two_pow_self))
    polyBoundedInTable_tableLen

/-- Under `PolyBoundedInTable threshold`, the concrete codec's witness width
`(bitLength n + 4) · threshold n` is polynomially bounded in the truth-table length. -/
theorem polyBoundedInTable_treeWitnessBits_of_thresholdPoly
    (threshold : Nat → Nat) (hT : PolyBoundedInTable threshold) :
    PolyBoundedInTable (treeCircuitWitnessCodec threshold).witnessBits := by
  show PolyBoundedInTable (fun n => (bitLength n + 4) * threshold n)
  exact (polyBoundedInTable_bitLength.add (PolyBoundedInTable.const 4)).mul hT

/-- **Concrete `PolynomialWitnessCodec`, under the single threshold-growth premise.**
Given `PolyBoundedInTable threshold`, the concrete codec packages as a
`PolynomialWitnessCodec`, hence (via `toGrowthAssumptions`) yields the full extraction
growth assumptions for a *concrete* codec. -/
def treePolynomialWitnessCodec (threshold : Nat → Nat) (hT : PolyBoundedInTable threshold) :
    PolynomialWitnessCodec threshold where
  codec := treeCircuitWitnessCodec threshold
  witness_poly := polyBoundedInTable_treeWitnessBits_of_thresholdPoly threshold hT

end ContractExpansion
end Frontier
end Pnp4
