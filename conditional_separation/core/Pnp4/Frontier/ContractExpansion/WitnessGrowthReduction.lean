import Pnp4.Frontier.ContractExpansion.ExtractedScheduleGrowth

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Witness-growth reduction for the extraction growth assumptions

Block 10a of the downstream decision→search extraction.

`TreeMCSPExtractionGrowthAssumptions codec` (Block 9d) bundles **two** explicit
polynomial growth assumptions:

* `witness_poly : PolyBoundedInTable codec.witnessBits`;
* `ambient_poly : PolyBoundedInTable (treeMCSPPrefixM codec)`.

An audit of the concrete tree-MCSP machinery shows there is **no concrete
`TreeCircuitWitnessCodec`** in the development — `witnessBits : Nat → Nat` is an
abstract field — so the witness-length growth genuinely *must* stay an explicit
assumption.  But the ambient length is **concrete**:

```
treeMCSPPrefixM codec n =
  tagLen + gammaLen n + tableLen n + idxWidth codec.witnessBits n + codec.witnessBits n
```

with `gammaLen n = 2·bitLength (n+1) − 1`, `idxWidth W n = bitLength (W n)`, and
`bitLength m = log₂ m + 1`.  Each summand is `PolyBoundedInTable` *given only* the
witness-length assumption, so **`ambient_poly` is provable from `witness_poly`**.

This file proves that reduction (collapsing the growth obligation from two
assumptions to one) and packages the single honest assumption as a small explicit
interface `PolynomialWitnessCodec`.  Nothing here proves the witness-length bound
itself — that is the one remaining (engineering/arithmetic) growth assumption,
kept explicit rather than hidden.

Scope discipline — growth-assumption reduction only:

* the witness-length growth `PolyBoundedInTable codec.witnessBits` is the single
  remaining **explicit assumption** — **not** proved here;
* **no** `SearchMCSPMagnificationContract` change, **no** `NoPolynomialBoundedSearchSolver`
  / lower-bound proof, **no** NP-membership, **no** endpoint or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/-! ### Structural poly-bounds for the concrete length functions -/

/-- `bitLength m ≤ m` for all `m`: from `2 ^ log₂ m ≤ m` (for `m ≠ 0`) and
`log₂ m + 1 ≤ 2 ^ log₂ m`. -/
theorem bitLength_le_self : ∀ m : Nat, bitLength m ≤ m := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [bitLength]
  · have hne : m ≠ 0 := hm.ne'
    have h1 : (2 : Nat) ^ (Nat.log2 m) ≤ m := Nat.log2_self_le hne
    have h2 : Nat.log2 m + 1 ≤ 2 ^ (Nat.log2 m) := Nat.lt_two_pow_self
    unfold bitLength
    rw [if_neg hne]
    omega

/-- The truth-table length is (trivially) polynomially bounded in itself. -/
theorem polyBoundedInTable_tableLen :
    PolyBoundedInTable (fun n => Pnp3.Models.Partial.tableLen n) :=
  ⟨1, fun n => by rw [pow_one]; exact Nat.le_succ _⟩

/-- The active-prefix-width field is poly-bounded whenever the underlying width
function is: `idxWidth W n = bitLength (W n) ≤ W n`. -/
theorem polyBoundedInTable_idxWidth {W : Nat → Nat} (hW : PolyBoundedInTable W) :
    PolyBoundedInTable (idxWidth W) :=
  PolyBoundedInTable.of_le (fun n => bitLength_le_self (W n)) hW

/-- The Elias-gamma length is poly-bounded in the truth-table length:
`gammaLen n ≤ 2·bitLength (n+1) ≤ 2·(n+1) ≤ 2·tableLen n`. -/
theorem polyBoundedInTable_gammaLen : PolyBoundedInTable gammaLen := by
  refine PolyBoundedInTable.of_le
    (g := fun n => 2 * Pnp3.Models.Partial.tableLen n) ?_ ?_
  · intro n
    show gammaLen n ≤ 2 * Pnp3.Models.Partial.tableLen n
    have hb : bitLength (n + 1) ≤ n + 1 := bitLength_le_self (n + 1)
    have ht : n + 1 ≤ Pnp3.Models.Partial.tableLen n := Nat.lt_two_pow_self
    unfold gammaLen
    omega
  · exact (PolyBoundedInTable.const 2).mul polyBoundedInTable_tableLen

/-! ### The reduction: ambient growth from witness growth -/

/-- **Ambient growth from witness growth.**  If the witness length is poly-bounded
in the truth-table length, so is the whole concrete ambient length
`treeMCSPPrefixM codec`. -/
theorem polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly
    (codec : TreeCircuitWitnessCodec threshold)
    (hW : PolyBoundedInTable codec.witnessBits) :
    PolyBoundedInTable (treeMCSPPrefixM codec) := by
  have h :=
    ((((PolyBoundedInTable.const tagLen).add polyBoundedInTable_gammaLen).add
        polyBoundedInTable_tableLen).add (polyBoundedInTable_idxWidth hW)).add hW
  unfold treeMCSPPrefixM
  exact h

/-- **Growth assumptions from the single witness-length assumption.**  The full
`TreeMCSPExtractionGrowthAssumptions` follows from `PolyBoundedInTable
codec.witnessBits` alone — the ambient half is proved, not assumed. -/
theorem treeMCSPExtractionGrowthAssumptions_of_witnessPoly
    (codec : TreeCircuitWitnessCodec threshold)
    (hW : PolyBoundedInTable codec.witnessBits) :
    TreeMCSPExtractionGrowthAssumptions codec :=
  { witness_poly := hW
    ambient_poly := polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly codec hW }

/-! ### The minimal explicit interface -/

/-- A tree-circuit witness codec packaged with the single honest growth assumption:
its witness length is polynomially bounded in the truth-table length.  This is the
*only* growth premise the extraction pipeline needs (the ambient-length premise is
derived). -/
structure PolynomialWitnessCodec (threshold : Nat → Nat) where
  codec : TreeCircuitWitnessCodec threshold
  witness_poly : PolyBoundedInTable codec.witnessBits

/-- Every `PolynomialWitnessCodec` yields the full extraction growth assumptions. -/
def PolynomialWitnessCodec.toGrowthAssumptions
    (P : PolynomialWitnessCodec threshold) :
    TreeMCSPExtractionGrowthAssumptions P.codec :=
  treeMCSPExtractionGrowthAssumptions_of_witnessPoly P.codec P.witness_poly

end ContractExpansion
end Frontier
end Pnp4
