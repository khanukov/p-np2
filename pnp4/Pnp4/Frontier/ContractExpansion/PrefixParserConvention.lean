import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- Version/domain separator for the first tree-MCSP prefix parser convention. -/
def treePrefixTag : Nat := 178

/-- The tree-MCSP prefix convention uses one byte for its fixed tag. -/
def tagLen : Nat := 8

/--
Bit-length convention used by the prefix parser.

For `k > 0`, this is `⌊log₂ k⌋ + 1`; for `k = 0` it is `0`.  The parser
convention only feeds `gammaLen` with `n + 1`, but `idxWidth` deliberately uses
`bitLength 0 = 0` so zero-witness codecs have an empty prefix-length field.
-/
def bitLength (k : Nat) : Nat :=
  if k = 0 then 0 else Nat.log2 k + 1

/-- Elias-gamma code length for the positive integer `n + 1`. -/
def gammaLen (n : Nat) : Nat :=
  2 * bitLength (n + 1) - 1

/-- Width of the active-prefix-length field for a codec with witness width `W(n)`. -/
def idxWidth
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  bitLength (codec.witnessBits n)

/-- Ambient length of the tree-MCSP prefix encoding for target parameter `n`. -/
def treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
    idxWidth codec n + codec.witnessBits n

/-- The truth-table payload is literally present in the ambient prefix input. -/
theorem tableLen_le_treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤ treeMCSPPrefixM codec n := by
  simp [treeMCSPPrefixM]
  omega

/-- Offset of the self-delimiting `n` field. -/
def treeMCSPPrefixNOffset : Nat := tagLen

/-- Offset of the truth-table payload after the tag and Elias-gamma `n` code. -/
def treeMCSPPrefixXOffset (n : Nat) : Nat :=
  tagLen + gammaLen n

/-- Offset of the active-prefix-length field. -/
def treeMCSPPrefixIOffset (n : Nat) : Nat :=
  treeMCSPPrefixXOffset n + Pnp3.Models.Partial.tableLen n

/-- Offset of the fixed witness-prefix block. -/
def treeMCSPPrefixPayloadOffset
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  treeMCSPPrefixIOffset n + idxWidth codec n

/-- Most-significant-bit-first bit of a natural number in a fixed-width field. -/
def natMSBBit (width value : Nat) (j : Fin width) : Bool :=
  Nat.testBit value (width - 1 - j.1)

/-- Fixed-width most-significant-bit-first vector for a natural number. -/
def natMSBBits (width value : Nat) : PrefixBitVec width :=
  fun j => natMSBBit width value j

/-- Elias-gamma bits for `n + 1`, most significant bit first. -/
def gammaBits (n : Nat) : PrefixBitVec (gammaLen n) :=
  fun j =>
    let width := bitLength (n + 1)
    if _h : j.1 < width - 1 then
      false
    else
      Nat.testBit (n + 1) (gammaLen n - 1 - j.1)

/-- Tag slice read from an input whose length has already been identified as `M(n)`. -/
def treeMCSPPrefixTagSlice
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (n : Nat)
    (hM : m = treeMCSPPrefixM codec n) : PrefixBitVec tagLen :=
  fun k => y ⟨k.1, by
    subst m
    have hk : k.1 < tagLen := k.2
    simp [treeMCSPPrefixM]
    omega⟩

/-- Gamma-code slice read from an input whose length is `M(n)`. -/
def treeMCSPPrefixGammaSlice
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (n : Nat)
    (hM : m = treeMCSPPrefixM codec n) : PrefixBitVec (gammaLen n) :=
  fun k => y ⟨treeMCSPPrefixNOffset + k.1, by
    subst m
    have hk : k.1 < gammaLen n := k.2
    simp [treeMCSPPrefixNOffset, treeMCSPPrefixM]
    omega⟩

/-- Truth-table slice read from an input whose length is `M(n)`. -/
def treeMCSPPrefixXSlice
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (n : Nat)
    (hM : m = treeMCSPPrefixM codec n) : PrefixBitVec (Pnp3.Models.Partial.tableLen n) :=
  fun k => y ⟨treeMCSPPrefixXOffset n + k.1, by
    subst m
    have hk : k.1 < Pnp3.Models.Partial.tableLen n := k.2
    simp [treeMCSPPrefixXOffset, treeMCSPPrefixM]
    omega⟩

/-- Active-prefix-length slice read from an input whose length is `M(n)`. -/
def treeMCSPPrefixISlice
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (n : Nat)
    (hM : m = treeMCSPPrefixM codec n) : PrefixBitVec (idxWidth codec n) :=
  fun k => y ⟨treeMCSPPrefixIOffset n + k.1, by
    subst m
    have hk : k.1 < idxWidth codec n := k.2
    simp [treeMCSPPrefixIOffset, treeMCSPPrefixXOffset, treeMCSPPrefixM]
    omega⟩

/-- Active prefix payload slice read from the fixed witness-prefix block. -/
def treeMCSPPrefixPSlice
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (hM : m = treeMCSPPrefixM codec n) : PrefixBitVec i :=
  fun k => y ⟨treeMCSPPrefixPayloadOffset codec n + k.1, by
    subst m
    have hk : k.1 < i := k.2
    have hkw : k.1 < codec.witnessBits n := Nat.lt_of_lt_of_le hk hi
    simp [treeMCSPPrefixPayloadOffset, treeMCSPPrefixIOffset,
      treeMCSPPrefixXOffset, treeMCSPPrefixM]
    omega⟩

/-- Zero-padding suffix predicate for the inactive part of the fixed witness block. -/
def treeMCSPPrefixPadIsZero
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (hM : m = treeMCSPPrefixM codec n) : Prop :=
  ∀ k : Fin (codec.witnessBits n - i),
    y ⟨treeMCSPPrefixPayloadOffset codec n + i + k.1, by
      subst m
      have hk : k.1 < codec.witnessBits n - i := k.2
      have hsum : i + k.1 < codec.witnessBits n := by omega
      simp [treeMCSPPrefixPayloadOffset, treeMCSPPrefixIOffset,
        treeMCSPPrefixXOffset, treeMCSPPrefixM]
      omega⟩ = false

/--
Canonical tree-MCSP prefix input predicate.

This is the Lean counterpart of the P1P-02 convention.  It ties a parsed
`PrefixInput` to the ambient bit-vector by checking the tag byte, the gamma code
for `n`, the literal truth-table slice, the fixed-width `i` slice, the active
prefix payload, and the zero inactive suffix.  It is intentionally only parser
infrastructure; it contains no lower-bound, NP-membership, or runtime claim.
-/
structure CanonicalTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) : Prop where
  length_matches : m = treeMCSPPrefixM codec input.n
  tag_field : input.tag = treePrefixTag
  tag_bits : treeMCSPPrefixTagSlice codec y input.n length_matches =
    natMSBBits tagLen treePrefixTag
  gamma_bits : treeMCSPPrefixGammaSlice codec y input.n length_matches =
    gammaBits input.n
  x_bits : input.x = treeMCSPPrefixXSlice codec y input.n length_matches
  i_bits : treeMCSPPrefixISlice codec y input.n length_matches =
    natMSBBits (idxWidth codec input.n) input.i
  p_bits : input.p =
    treeMCSPPrefixPSlice codec y input.n input.i input.prefixLength_le length_matches
  pad_length : input.padBits = codec.witnessBits input.n - input.i
  pad_input_zero : ∀ k : Fin input.padBits, input.pad k = false
  pad_wire_zero : treeMCSPPrefixPadIsZero codec y input.n input.i
    input.prefixLength_le length_matches

/--
Noncomputable specification parser for the canonical tree-MCSP prefix convention.

The implementation is deliberately specification-level: it accepts exactly when
there exists a `PrefixInput` satisfying `CanonicalTreeMCSPPrefixInput`.  This is
meaningful parser infrastructure (not an always-rejecting smoke artifact), while
leaving TM-level runtime proofs staged for later work.
-/
noncomputable def parseTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m) :
    Option (PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) := by
  classical
  exact
    if h : ∃ input, CanonicalTreeMCSPPrefixInput codec y input then
      some h.choose
    else
      none

/-- Pack the canonical parser in the generic `PrefixParser` interface. -/
noncomputable def treeMCSPConcretePrefixParser
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :
    PrefixParser (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) where
  tag := treePrefixTag
  M := treeMCSPPrefixM codec
  parse := parseTreeMCSPPrefixInput codec

/-- Successful parsing obeys the exact P1P-02 ambient-length convention. -/
theorem parseTreeMCSPPrefixInput_length_convention
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (hparse : parseTreeMCSPPrefixInput codec y = some input) :
    m = treeMCSPPrefixM codec input.n := by
  classical
  unfold parseTreeMCSPPrefixInput at hparse
  by_cases h : ∃ input, CanonicalTreeMCSPPrefixInput codec y input
  · simp [h] at hparse
    cases hparse
    exact h.choose_spec.length_matches
  · simp [h] at hparse

/-- Parser failure is rejected by the generic prefix-extension language theorem. -/
theorem parseTreeMCSPPrefixInput_malformed_rejected
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (hparse : parseTreeMCSPPrefixInput codec y = none) :
    PrefixExtensionLanguage (treeMCSPConcretePrefixParser codec) m y = false := by
  exact PrefixExtensionLanguage_rejects_malformed
    (treeMCSPConcretePrefixParser codec) y hparse

/-- Canonical witnesses are accepted by the specification parser. -/
theorem parseTreeMCSPPrefixInput_of_canonical
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (hcanon : CanonicalTreeMCSPPrefixInput codec y input) :
    ∃ parsed,
      parseTreeMCSPPrefixInput codec y = some parsed ∧
        CanonicalTreeMCSPPrefixInput codec y parsed := by
  classical
  unfold parseTreeMCSPPrefixInput
  have h : ∃ input, CanonicalTreeMCSPPrefixInput codec y input := ⟨input, hcanon⟩
  refine ⟨h.choose, ?_, h.choose_spec⟩
  simp [h]

end ContractExpansion
end Frontier
end Pnp4
