import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Input-tape layout for the prefix-extension verifier Turing machine

Phase 6 (first brick) of the NP-verifier track — see `TM_VERIFIER_STRATEGY.md`.

The verifier TM reads `concatBitstring query cert`, where `query : Bitstring N` is the parsed
prefix-language instance and `cert : Bitstring (certificateLength N 1)` is the certificate.  This
module fixes the **data-independent** tape layout (the input length and the certificate / witness
region offsets) and proves the basic fit lemmas the per-phase TM programs will rely on.

No Turing machine is built here; this is layout arithmetic only (`Classical`-free).
-/

/-- Length of the verifier's input tape: the length-`N` query followed by the certificate of length
`certificateLength N 1 = N + 1`. -/
def prefixVerifierInputLen (N : Nat) : Nat :=
  N + Pnp3.ComplexityInterfaces.certificateLength N 1

/-- The input tape has length `2 N + 1`. -/
theorem prefixVerifierInputLen_eq (N : Nat) :
    prefixVerifierInputLen N = 2 * N + 1 := by
  unfold prefixVerifierInputLen
  simp only [Pnp3.ComplexityInterfaces.certificateLength, pow_one]
  omega

/-- The certificate region starts immediately after the length-`N` query. -/
def prefixVerifierCertStart (N : Nat) : Nat := N

/--
The witness prefix occupies the first `codec.witnessBits n` cells of the certificate region;
under the parser length convention (`N = treeMCSPPrefixM codec n`) it fits inside the input tape.
This is the on-tape counterpart of `extractWitness_eq`: the verifier can address the witness bits
without running past the input.
-/
theorem prefixVerifierWitnessRegion_within_input
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n N : Nat) (hM : N = treeMCSPPrefixM codec n) :
    prefixVerifierCertStart N + codec.witnessBits n ≤ prefixVerifierInputLen N := by
  unfold prefixVerifierCertStart prefixVerifierInputLen
  have h := witnessBits_le_certificateLength codec n N hM
  omega

/-!
## Reading the concatenated verifier input

The verifier TM is run on `concatBitstring query cert`; `initialConfig` loads that string onto the
tape, so reading tape cell `j` returns `query j` for `j < N` and `cert (j - N)` for `N ≤ j`.  These
projection lemmas characterize `concatBitstring` bit-by-bit.  Because `concatBitstring` is
`noncomputable` (its right half is defined via `Classical.choose`), the projections are *not*
definitional and must be proved; they are the foundation of any future
`accepts M (concatBitstring x w) = …` reasoning.
-/

/-- On the left block, the concatenation reads as the instance `x`. -/
theorem concatBitstring_left {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (i : Fin (n + m)) (h : (i : Nat) < n) :
    Pnp3.ComplexityInterfaces.concatBitstring x w i = x ⟨(i : Nat), h⟩ := by
  unfold Pnp3.ComplexityInterfaces.concatBitstring
  rw [dif_pos h]

/-- On the right block, the concatenation reads as the certificate `w`. -/
theorem concatBitstring_right {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (i : Fin (n + m)) (h : n ≤ (i : Nat)) :
    Pnp3.ComplexityInterfaces.concatBitstring x w i
      = w ⟨(i : Nat) - n, by omega⟩ := by
  have hnlt : ¬ (i : Nat) < n := by omega
  unfold Pnp3.ComplexityInterfaces.concatBitstring
  rw [dif_neg hnlt]
  refine congrArg w (Fin.ext ?_)
  show Classical.choose (Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnlt)) = (i : Nat) - n
  have hspec := Classical.choose_spec (Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnlt))
  omega

/-!
### Tape reading at the start of a verifier run

Composing the existing `@[simp]` lemma `TM.initial_tape_input` with the projections above: when any
Turing machine `M` is started on `concatBitstring x w`, a tape cell in the left block reads the
instance `x` and a cell in the right block reads the certificate `w`.  These are the exact statements
a per-phase verifier program will use to relate a read bit back to `query` / `cert`.
-/

/-- A left-block tape cell, at the start of a run on `concatBitstring x w`, reads the instance. -/
theorem verifierTape_left {n m : Nat} (M : Pnp3.Internal.PsubsetPpoly.TM)
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) (hj : (j : Nat) < n) :
    (M.initialConfig (Pnp3.ComplexityInterfaces.concatBitstring x w)).tape j
      = x ⟨(j : Nat), hj⟩ := by
  have hlt : (j : Nat) < n + m := by omega
  rw [Pnp3.Internal.PsubsetPpoly.TM.initial_tape_input (M := M)
        (Pnp3.ComplexityInterfaces.concatBitstring x w) hlt]
  exact concatBitstring_left x w ⟨(j : Nat), hlt⟩ hj

/-- A right-block tape cell, at the start of a run on `concatBitstring x w`, reads the certificate. -/
theorem verifierTape_right {n m : Nat} (M : Pnp3.Internal.PsubsetPpoly.TM)
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) (hj1 : n ≤ (j : Nat)) (hj2 : (j : Nat) < n + m) :
    (M.initialConfig (Pnp3.ComplexityInterfaces.concatBitstring x w)).tape j
      = w ⟨(j : Nat) - n, by omega⟩ := by
  rw [Pnp3.Internal.PsubsetPpoly.TM.initial_tape_input (M := M)
        (Pnp3.ComplexityInterfaces.concatBitstring x w) hj2]
  exact concatBitstring_right x w ⟨(j : Nat), hj2⟩ hj1

/-!
### Query field offsets

The canonical query block (length `treeMCSPPrefixM codec n`) is laid out as
`tag ++ gamma(n) ++ x ++ idx ++ (prefix ++ pad)`.  These offsets name the start of each field, so a
parse-phase program can seek to the right tape position.  They partition the query block exactly
(`queryPrefixOffset + witnessBits = treeMCSPPrefixM`).
-/

/-- Start of the truth-table (`x`) field: after the tag and the Elias-gamma block for `n`. -/
def queryXOffset (n : Nat) : Nat := tagLen + gammaLen n

/-- Start of the prefix-length index field: after `x`. -/
def queryIdxOffset (n : Nat) : Nat :=
  queryXOffset n + Pnp3.Models.Partial.tableLen n

/-- Start of the witness-prefix field: after the index. -/
def queryPrefixOffset {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  queryIdxOffset n + idxWidth codec.witnessBits n

/-- The witness-prefix field runs to the end of the query block. -/
theorem queryPrefixOffset_add_witnessBits
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) (n : Nat) :
    queryPrefixOffset codec n + codec.witnessBits n = treeMCSPPrefixM codec n := by
  unfold queryPrefixOffset queryIdxOffset queryXOffset treeMCSPPrefixM
  omega

/-- Every query-field offset lies within the query block. -/
theorem queryPrefixOffset_le
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) (n : Nat) :
    queryPrefixOffset codec n ≤ treeMCSPPrefixM codec n := by
  have := queryPrefixOffset_add_witnessBits codec n
  omega

/-- The gamma field occupies `[tagLen, queryXOffset n)` and its end (`= tagLen + gammaLen n`) lies
within the query block.  This is the layout precondition for the gamma-decode phase: the head stays
inside the query while scanning the Elias-gamma block for `n`. -/
theorem queryXOffset_le_treeMCSPPrefixM
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) (n : Nat) :
    queryXOffset n ≤ treeMCSPPrefixM codec n := by
  unfold queryXOffset treeMCSPPrefixM
  omega

/-- The truth-table (`x`) field ends at `queryIdxOffset codec n`, which lies within the query block —
the layout precondition for the (later) instance-reading phase. -/
theorem queryIdxOffset_le_treeMCSPPrefixM
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) (n : Nat) :
    queryIdxOffset n ≤ treeMCSPPrefixM codec n := by
  unfold queryIdxOffset queryXOffset treeMCSPPrefixM
  omega

/-- The Elias-gamma block for `n` (length `gammaLen n`, starting at offset `tagLen`) fits entirely
within the query block.  Restatement of `queryXOffset_le_treeMCSPPrefixM` in terms of the raw field
length, matching the `tableLen_le_treeMCSPPrefixM` / `witnessBits_le_treeMCSPPrefixM` family. -/
theorem gammaLen_le_treeMCSPPrefixM
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) (n : Nat) :
    tagLen + gammaLen n ≤ treeMCSPPrefixM codec n :=
  queryXOffset_le_treeMCSPPrefixM codec n

/-- The instance size is strictly smaller than the query length: the `x` field has `2 ^ n` cells and
`n < 2 ^ n`, so `n < treeMCSPPrefixM codec n`.  Equivalently, the instance size is logarithmic in the
query length (`2 ^ n ≤ N`).  This bounds the gamma-decode design's search/counter range — a candidate
`n`, and its `bitLength N`-bit binary counter, fit within the input. -/
theorem instanceSize_lt_treeMCSPPrefixM
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) (n : Nat) :
    n < treeMCSPPrefixM codec n := by
  have h1 : Pnp3.Models.Partial.tableLen n ≤ treeMCSPPrefixM codec n :=
    tableLen_le_treeMCSPPrefixM codec n
  have h2 : n < Pnp3.Models.Partial.tableLen n := by
    unfold Pnp3.Models.Partial.tableLen
    exact Nat.lt_two_pow_self
  omega

end ContractExpansion
end Frontier
end Pnp4
