import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
Progress classification: infrastructure.

This module fixes the arithmetic part of the P1P-02 tree-MCSP prefix-parser
convention and exposes a narrow, non-fake hook for the future byte-level parser.
It does not prove NP membership, a lower bound, a source theorem, or any
P-vs-NP endpoint.  The dependent bit-slicing parser itself remains an explicit
implementation field rather than being replaced by an always-rejecting parser.
-/

/-- Version/domain-separation tag for the tree-MCSP prefix serialization. -/
def treePrefixTag : Nat := 178

/-- The tag field is exactly one byte. -/
def tagLen : Nat := 8

/--
Binary bit length used by the convention.

`bitLength 0 = 0`, while positive numbers have the usual binary width
`⌊log₂ n⌋ + 1`.  The parser convention uses this for Elias-gamma lengths and
for the fixed-width active-prefix-length field.
-/
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- Length of the Elias-gamma encoding of `n + 1`. -/
def gammaLen (n : Nat) : Nat :=
  2 * bitLength (n + 1) - 1

/--
Width of the unsigned field that stores the active prefix length `i`.

For a codec with witness block length `W(n)`, the parser must represent every
value in `[0, W(n)]`.  The P1P-02 convention therefore uses the binary width of
`W(n)` itself, with the special case `W(n)=0` giving an empty field that decodes
to zero.
-/
def idxWidth
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  bitLength (codec.witnessBits n)

/--
Canonical ambient length for the P1P-02 tree-MCSP prefix serialization.

The final `codec.witnessBits n` addend is the fixed-size `p ++ pad` block, so
the active prefix length `i` does not change the ambient input length.
-/
def treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n + idxWidth codec n +
    codec.witnessBits n

/--
The truth-table block is explicitly included in the P1P-02 ambient length.

This is the load-bearing arithmetic fact needed before truth-table scanning can
be measured against the ambient serialized input length rather than against the
smaller target parameter `n`.
-/
theorem tableLen_le_treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤ treeMCSPPrefixM codec n := by
  simp [treeMCSPPrefixM]
  omega

/-- Local spelling for the concrete tree-MCSP prefix problem induced by a codec. -/
abbrev TreeMCSPConcretePrefixProblem
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) : SearchMCSPCompressionProblem :=
  treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)

/--
Canonicality predicate for already parsed tree-MCSP prefix inputs.

It records only the serialization invariants that are visible at the
`PrefixInput` boundary: the fixed tag, the single-length convention, the exact
inactive padding length, and all-zero pad bits.  It deliberately does not assert
semantic extendability or any runtime/NP property.
-/
def CanonicalTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (input : PrefixInput (TreeMCSPConcretePrefixProblem codec) m) : Prop :=
  input.tag = treePrefixTag ∧
    m = treeMCSPPrefixM codec input.n ∧
    input.padBits = codec.witnessBits input.n - input.i ∧
    (∀ k : Fin input.padBits, input.pad k = false)

/--
Non-fake implementation hook for the future byte-level parser.

A value of this structure must provide an actual `parse` function and its
successful-parse length theorem.  This module intentionally does not fabricate a
`parse := fun _ => none`; workers implementing dependent bit slicing should fill
this structure with the real tag/gamma/slice/pad parser.
-/
structure TreeMCSPConcretePrefixParserImpl
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold) where
  parse : ∀ {m : Nat}, PrefixBitVec m →
    Option (PrefixInput (TreeMCSPConcretePrefixProblem codec) m)
  length_convention_matches_M :
    ∀ {m : Nat}, ∀ y : PrefixBitVec m,
      ∀ input : PrefixInput (TreeMCSPConcretePrefixProblem codec) m,
        parse y = some input → m = treeMCSPPrefixM codec input.n

/-- Entry point name for the staged concrete parser implementation. -/
def parseTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    (impl : TreeMCSPConcretePrefixParserImpl threshold codec)
    {m : Nat}
    (y : PrefixBitVec m) :
    Option (PrefixInput (TreeMCSPConcretePrefixProblem codec) m) :=
  impl.parse y

/-- Package a supplied P1P-02 parser implementation as the generic R1-B parser. -/
def treeMCSPConcretePrefixParser
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (impl : TreeMCSPConcretePrefixParserImpl threshold codec) :
    PrefixParser (TreeMCSPConcretePrefixProblem codec) where
  tag := treePrefixTag
  M := treeMCSPPrefixM codec
  parse := impl.parse

/-- Successful parsing obeys the P1P-02 single-length convention. -/
theorem parseTreeMCSPPrefixInput_length_convention
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    (impl : TreeMCSPConcretePrefixParserImpl threshold codec)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput (TreeMCSPConcretePrefixProblem codec) m)
    (hparse : parseTreeMCSPPrefixInput impl y = some input) :
    m = treeMCSPPrefixM codec input.n :=
  impl.length_convention_matches_M y input hparse

/--
Malformed inputs, represented by parser failure, are rejected by the generic
prefix-extension language for the packaged P1P-02 parser.
-/
theorem parseTreeMCSPPrefixInput_malformed_rejected
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    (impl : TreeMCSPConcretePrefixParserImpl threshold codec)
    {m : Nat}
    (y : PrefixBitVec m)
    (hparse : parseTreeMCSPPrefixInput impl y = none) :
    PrefixExtensionLanguage (treeMCSPConcretePrefixParser codec impl) m y = false := by
  exact PrefixExtensionLanguage_rejects_malformed
    (treeMCSPConcretePrefixParser codec impl) y hparse

/--
Runtime-aware package produced from a real parser implementation.

The polynomial-time parser field remains a named external obligation supplied by
the caller; this definition does not instantiate it with `True` or otherwise
turn the staged runtime claim into a fake proof.
-/
def treeMCSPRuntimeAwarePrefixParser
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (impl : TreeMCSPConcretePrefixParserImpl threshold codec)
    (parser_polynomial_time_in_M : Prop) :
    RuntimeAwarePrefixParser (TreeMCSPConcretePrefixProblem codec)
      (treeMCSPPrefixM codec) where
  parser := treeMCSPConcretePrefixParser codec impl
  parser_polynomial_time_in_M := parser_polynomial_time_in_M
  malformed_inputs_rejected := by
    intro m y hparse
    exact PrefixExtensionLanguage_rejects_malformed
      (treeMCSPConcretePrefixParser codec impl) y hparse
  length_convention_matches_M := by
    intro m y input hparse
    exact impl.length_convention_matches_M y input hparse

end ContractExpansion
end Frontier
end Pnp4
