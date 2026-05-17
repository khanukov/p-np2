import Mathlib.Tactic
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- Version/domain separator for the first concrete tree-MCSP prefix format. -/
def treePrefixTag : Nat := 178

/-- The tree-MCSP prefix tag is serialized as one octet. -/
def tagLen : Nat := 8

/--
Binary length of a natural number, with `0` assigned length `0`.

For the prefix convention we use this only on positive numbers (`n + 1`) or on
witness-block lengths.  Keeping the zero case at `0` makes the empty-width
`i` field for `W(n)=0` definitionally convenient.
-/
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- Length of the Elias-gamma code for `n + 1`. -/
def gammaLen (n : Nat) : Nat :=
  2 * bitLength (n + 1) - 1

/-- Width of the unsigned active-prefix-length field for a witness block. -/
def idxWidth
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  bitLength (codec.witnessBits n)

/--
Concrete ambient length for the tree-MCSP prefix parser convention.

The fixed witness-prefix block has length `codec.witnessBits n`; the active
prefix length `i` only decides how that block is split between payload and
canonical zero padding, so it does not appear in `M(n)`.
-/
def treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
    idxWidth codec n + codec.witnessBits n

/-- The truth-table slice is an explicit addend of the prefix ambient length. -/
theorem tableLen_le_treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤ treeMCSPPrefixM codec n := by
  simp [treeMCSPPrefixM]
  omega

/-- The all-zero bit-vector of a given length. -/
def zeroPrefixBitVec (n : Nat) : PrefixBitVec n :=
  fun _ => false

/-- Interpret a natural number as a fixed-width big-endian bit field. -/
def natField (width value : Nat) : PrefixBitVec width :=
  fun j => Nat.testBit value (width - 1 - j.val)

/-- The fixed tree-prefix tag field. -/
def treePrefixTagField : PrefixBitVec tagLen :=
  natField tagLen treePrefixTag

/-- Elias-gamma field for `n + 1`, in the convention documented by P1P-02. -/
def gammaField (n : Nat) : PrefixBitVec (gammaLen n) :=
  fun j =>
    if j.val < bitLength (n + 1) - 1 then
      false
    else
      Nat.testBit (n + 1) (gammaLen n - 1 - j.val)

/--
Read a field bit at an ambient coordinate.

If the coordinate is outside the half-open interval `[offset, offset + len)`,
this helper returns `false`; callers combine several fields by checking them in
layout order, so outside-field values are never used on the successful branch.
-/
def fieldBitAt {m len : Nat}
    (field : PrefixBitVec len)
    (offset : Nat)
    (j : Fin m) : Bool :=
  if h : offset ≤ j.val ∧ j.val < offset + len then
    field ⟨j.val - offset, by omega⟩
  else
    false

/-- Canonicality predicate for parsed tree-MCSP prefix inputs. -/
def CanonicalTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) : Prop :=
  input.tag = treePrefixTag ∧
    m = treeMCSPPrefixM codec input.n ∧
    input.padBits = codec.witnessBits input.n - input.i ∧
    (∀ k : Fin input.padBits, input.pad k = false)

/--
Encode the fields carried by a `PrefixInput` according to the P1P-02 layout.

This encoder is intentionally total on `PrefixInput`; the parser below only
accepts encodings paired with the `CanonicalTreeMCSPPrefixInput` predicate, so
noncanonical tags, ambient lengths, or padding do not become accepted inputs.
-/
def encodeTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    {m : Nat}
    (input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) : PrefixBitVec m :=
  fun j =>
    let gammaOffset := tagLen
    let xOffset := gammaOffset + gammaLen input.n
    let iOffset := xOffset +
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)).instanceBits input.n
    let pOffset := iOffset + idxWidth codec input.n
    let padOffset := pOffset + input.i
    if hTag : j.val < tagLen then
      treePrefixTagField ⟨j.val, hTag⟩
    else if hGamma : gammaOffset ≤ j.val ∧ j.val < xOffset then
      gammaField input.n ⟨j.val - gammaOffset, by omega⟩
    else if hX : xOffset ≤ j.val ∧ j.val < iOffset then
      input.x ⟨j.val - xOffset, by omega⟩
    else if hI : iOffset ≤ j.val ∧ j.val < pOffset then
      natField (idxWidth codec input.n) input.i ⟨j.val - iOffset, by omega⟩
    else if hP : pOffset ≤ j.val ∧ j.val < padOffset then
      input.p ⟨j.val - pOffset, by omega⟩
    else if hPad : padOffset ≤ j.val ∧ j.val < padOffset + input.padBits then
      input.pad ⟨j.val - padOffset, by omega⟩
    else
      false

/-- A raw ambient string is the canonical encoding of a parsed input. -/
def EncodesTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) : Prop :=
  CanonicalTreeMCSPPrefixInput codec input ∧
    y = encodeTreeMCSPPrefixInput (codec := codec) input

/--
Specification-first parser for the concrete tree-MCSP prefix convention.

The parser accepts exactly strings that are the canonical P1P-02 encoding of
some `PrefixInput`.  This lands the serialization convention without pretending
that the repository already has executable dependent bit-slicing and gamma
runtime proofs; those can refine this spec parser in a later implementation.
-/
noncomputable def parseTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m) :
    Option (PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) := by
  classical
  exact
    if h : ∃ input : PrefixInput
        (treeMCSPSearchProblem threshold
          (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m,
        EncodesTreeMCSPPrefixInput codec y input then
      some (Classical.choose h)
    else
      none

/-- Successful parsing returns a canonical input whose encoding is the input string. -/
theorem parseTreeMCSPPrefixInput_some_encoded
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (hparse : parseTreeMCSPPrefixInput codec y = some input) :
    EncodesTreeMCSPPrefixInput codec y input := by
  classical
  unfold parseTreeMCSPPrefixInput at hparse
  by_cases h : ∃ input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m,
      EncodesTreeMCSPPrefixInput codec y input
  · simp [h] at hparse
    cases hparse
    exact Classical.choose_spec h
  · simp [h] at hparse

/-- Any successful parse obeys the ambient-length convention `m = M(input.n)`. -/
theorem parseTreeMCSPPrefixInput_length_convention
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (hparse : parseTreeMCSPPrefixInput codec y = some input) :
    m = treeMCSPPrefixM codec input.n := by
  have henc := parseTreeMCSPPrefixInput_some_encoded codec y input hparse
  exact henc.1.2.1

/-- If the ambient length is not any allowed `M(n)`, parsing rejects. -/
theorem parseTreeMCSPPrefixInput_bad_length_rejection
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (hlen : ∀ n : Nat, m ≠ treeMCSPPrefixM codec n) :
    parseTreeMCSPPrefixInput codec y = none := by
  classical
  unfold parseTreeMCSPPrefixInput
  by_cases h : ∃ input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m,
      EncodesTreeMCSPPrefixInput codec y input
  · rcases h with ⟨input, henc⟩
    exact (False.elim (hlen input.n henc.1.2.1))
  · simp [h]

/-- Package the concrete convention parser behind the generic R1-B interface. -/
noncomputable def treeMCSPConcretePrefixParser
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :
    PrefixParser
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) where
  tag := treePrefixTag
  M := treeMCSPPrefixM codec
  parse := parseTreeMCSPPrefixInput codec

/-- Parser failures are rejected by the prefix-extension language. -/
theorem parseTreeMCSPPrefixInput_malformed_rejected
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (hparse : parseTreeMCSPPrefixInput codec y = none) :
    PrefixExtensionLanguage (treeMCSPConcretePrefixParser codec) m y = false := by
  exact PrefixExtensionLanguage_rejects_malformed
    (treeMCSPConcretePrefixParser codec) y hparse

/-- The packaged parser inherits the concrete ambient-length convention. -/
theorem treeMCSPConcretePrefixParser_length_convention
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (hparse : parsePrefixInput (treeMCSPConcretePrefixParser codec) y = some input) :
    m = treeMCSPPrefixM codec input.n := by
  exact parseTreeMCSPPrefixInput_length_convention codec y input hparse

end ContractExpansion
end Frontier
end Pnp4
