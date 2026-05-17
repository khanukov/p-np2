import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- Version/domain tag for the canonical tree-MCSP prefix serialization. -/
def treePrefixTag : Nat := 178

/-- The tag occupies exactly one byte. -/
def tagLen : Nat := 8

/--
Binary length of a natural number, with `bitLength 0 = 0`.

For the prefix convention this is used only on positive quantities (`n + 1`)
and on witness-block lengths.  The definition via `Nat.log2` keeps the helper
small while matching the usual unsigned binary width.
-/
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- Length of the Elias-gamma code used for the natural number `n` as `n + 1`. -/
def gammaLen (n : Nat) : Nat :=
  2 * bitLength (n + 1) - 1

/-- Width of the unsigned active-prefix-length field for a witness block. -/
def idxWidth (W : Nat → Nat) (n : Nat) : Nat :=
  bitLength (W n)

/--
Canonical ambient length for the tree-MCSP prefix parser convention.

The serialized layout is:
`tag ++ gamma(n+1) ++ x ++ i ++ (p ++ pad)`, where the final witness-prefix
block always has total length `codec.witnessBits n`.
-/
def treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) : Nat :=
  tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
    idxWidth codec.witnessBits n + codec.witnessBits n

/-- The truth-table component is explicitly included in the concrete `M(n)`. -/
theorem tableLen_le_treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤ treeMCSPPrefixM codec n := by
  unfold treeMCSPPrefixM
  omega


/-- Big-endian bit of a fixed-width unsigned natural-number field.

`index = 0` addresses the most-significant bit.  The helper is total in the
index so it can be used directly inside dependent bit-vector lambdas; callers
supply indices in the intended range by construction.
-/
def natBitBE (value width index : Nat) : Bool :=
  (value / 2 ^ (width - 1 - index)) % 2 = 1

/-- Bit of the canonical Elias-gamma encoding of `n + 1`.

The parser convention writes `z = bitLength (n+1)-1` leading zero bits, one
terminator bit, and then the low `z` payload bits of `n+1` in big-endian order.
This definition is deliberately computable and does not recover fields by
inverting the parser.
-/
def gammaBit (n index : Nat) : Bool :=
  let z := bitLength (n + 1) - 1
  if index < z then
    false
  else if index = z then
    true
  else
    natBitBE ((n + 1) - 2 ^ z) z (index - (z + 1))

/-- Read one bit at a natural offset, rejecting offsets outside the vector. -/
def readBit? {m : Nat} (y : PrefixBitVec m) (offset : Nat) : Option Bool :=
  if h : offset < m then some (y ⟨offset, h⟩) else none

/-- Read a big-endian unsigned natural from a fixed-width field. -/
def readNatBE {m : Nat} (y : PrefixBitVec m) (offset width : Nat) : Option Nat :=
  match width with
  | 0 => some 0
  | k + 1 => do
      let b ← readBit? y offset
      let rest ← readNatBE y (offset + 1) k
      some ((if b then 2 ^ k else 0) + rest)

/-- Slice a dependent bit-vector field from an ambient prefix string. -/
def sliceBits? {m : Nat} (y : PrefixBitVec m) (offset width : Nat) :
    Option (PrefixBitVec width) :=
  if h : offset + width ≤ m then
    some (fun j => y ⟨offset + j.1, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 offset) h⟩)
  else
    none

/-- Check that a fixed slice consists only of zero bits. -/
def allZeroSlice? {m : Nat} (y : PrefixBitVec m) (offset width : Nat) : Option Bool :=
  match width with
  | 0 => some true
  | k + 1 => do
      let b ← readBit? y offset
      let rest ← allZeroSlice? y (offset + 1) k
      some ((!b) && rest)

/-- Search for the unary terminator of an Elias-gamma code and decode it. -/
def decodeGammaAux? {m : Nat} (y : PrefixBitVec m) (offset fuel zeros : Nat) :
    Option (Nat × Nat) :=
  match fuel with
  | 0 => none
  | fuel' + 1 => do
      let b ← readBit? y (offset + zeros)
      if b then
        let payload ← readNatBE y (offset + zeros + 1) zeros
        let value := 2 ^ zeros + payload
        some (value - 1, 2 * zeros + 1)
      else
        decodeGammaAux? y offset fuel' (zeros + 1)

/-- Decode the Elias-gamma representation of `n + 1` at a given offset. -/
def decodeGamma? {m : Nat} (y : PrefixBitVec m) (offset : Nat) : Option (Nat × Nat) :=
  decodeGammaAux? y offset (m + 1) 0

/-- Predicate recording the canonical zero-padding convention for parsed inputs. -/
def CanonicalTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) : Prop :=
  input.tag = treePrefixTag ∧
    m = treeMCSPPrefixM codec input.n ∧
      input.padBits = codec.witnessBits input.n - input.i ∧
        ∀ j : Fin input.padBits, input.pad j = false

/--
Concrete parser for the P1P-02 tree-MCSP prefix convention.

This is deliberately only parser/serialization infrastructure.  It performs the
version-tag check, gamma decoding, exact ambient-length check, dependent slices,
active-prefix bound check, and zero-padding check.  It does not assert any
polynomial-time verifier theorem or NP-membership result.
-/
def parseTreeMCSPPrefixInput
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m) :
    Option (PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) := do
  let tag ← readNatBE y 0 tagLen
  if _htag : tag = treePrefixTag then
    let decoded ← decodeGamma? y tagLen
    let n := decoded.1
    let consumedGamma := decoded.2
    if _hlen : m = treeMCSPPrefixM codec n then
      let xOffset := tagLen + consumedGamma
      let x ← sliceBits? y xOffset (Pnp3.Models.Partial.tableLen n)
      let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
      let i ← readNatBE y iOffset (idxWidth codec.witnessBits n)
      if hi : i ≤ codec.witnessBits n then
        let pOffset := iOffset + idxWidth codec.witnessBits n
        let p ← sliceBits? y pOffset i
        let padOffset := pOffset + i
        let padWidth := codec.witnessBits n - i
        let pad ← sliceBits? y padOffset padWidth
        let padZero ← allZeroSlice? y padOffset padWidth
        if _hpad : padZero = true then
          some {
            tag := tag
            n := n
            x := x
            i := i
            prefixLength_le := hi
            p := p
            padBits := padWidth
            pad := pad
          }
        else
          none
      else
        none
    else
      none
  else
    none

/-- The concrete parser packaged in the existing `PrefixParser` interface. -/
def treeMCSPConcretePrefixParser
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold) :
    PrefixParser (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) where
  tag := treePrefixTag
  M := treeMCSPPrefixM codec
  parse := parseTreeMCSPPrefixInput threshold codec


/--
Computable canonical encoder for parsed tree-MCSP prefix inputs.

The encoder normalizes the serialization to the P1P-02 layout: the version tag
and gamma-coded target length are regenerated, the truth table and active
prefix payload are copied from `input`, the active-prefix-length field is
encoded as an unsigned fixed-width integer, and all inactive witness-prefix bits
are written as zero.  In particular, this is an encoder for the canonical byte
layout, not a parser inverse obtained by `Classical.choose` or by inspecting a
successful parse.
-/
def encodeTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) :
    PrefixBitVec (treeMCSPPrefixM codec input.n) :=
  fun j =>
    let n := input.n
    let xOffset := tagLen + gammaLen n
    let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
    let pOffset := iOffset + idxWidth codec.witnessBits n
    if htag : j.1 < tagLen then
      natBitBE treePrefixTag tagLen j.1
    else if hgamma : j.1 < xOffset then
      gammaBit n (j.1 - tagLen)
    else if hx : j.1 < iOffset then
      input.x ⟨j.1 - xOffset, by
        simpa [treeMCSPSearchProblem, n] using
          (by omega : j.1 - xOffset < Pnp3.Models.Partial.tableLen n)⟩
    else if hi : j.1 < pOffset then
      natBitBE input.i (idxWidth codec.witnessBits n) (j.1 - iOffset)
    else
      let r := j.1 - pOffset
      if hp : r < input.i then
        input.p ⟨r, hp⟩
      else
        false

/--
Successful parses obey the concrete single-length convention `m = M(input.n)`.

This is the R1-B2a runtime-budget hook for the P1P-02 parser convention: the
parser has no trailing-garbage or alternate-padding acceptance mode, so every
accepted input length is exactly the canonical ambient length for the decoded
parameter.
-/
theorem parseTreeMCSPPrefixInput_length_convention
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (h : parseTreeMCSPPrefixInput threshold codec y = some input) :
    m = treeMCSPPrefixM codec input.n := by
  unfold parseTreeMCSPPrefixInput at h
  generalize hTagOpt : readNatBE y 0 tagLen = tagOpt at h
  cases tagOpt with
  | none => simp at h
  | some tag =>
      by_cases htag : tag = treePrefixTag
      · simp [htag] at h
        generalize hDecodedOpt : decodeGamma? y tagLen = decodedOpt at h
        cases decodedOpt with
        | none => simp at h
        | some decoded =>
            by_cases hlen : m = treeMCSPPrefixM codec decoded.1
            · simp [hlen] at h
              generalize hXOpt : sliceBits? y (tagLen + decoded.2)
                  (Pnp3.Models.Partial.tableLen decoded.1) = xOpt at h
              cases xOpt with
              | none => simp at h
              | some x =>
                  generalize hIOpt : readNatBE y
                      (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1)
                      (idxWidth codec.witnessBits decoded.1) = iOpt at h
                  cases iOpt with
                  | none => simp at h
                  | some i =>
                      by_cases hi : i ≤ codec.witnessBits decoded.1
                      · simp [hi] at h
                        generalize hPOpt : sliceBits? y
                            (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1 +
                              idxWidth codec.witnessBits decoded.1) i = pOpt at h
                        cases pOpt with
                        | none => simp at h
                        | some p =>
                            generalize hPadOpt : sliceBits? y
                                (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1 +
                                    idxWidth codec.witnessBits decoded.1 + i)
                                (codec.witnessBits decoded.1 - i) = padOpt at h
                            cases padOpt with
                            | none => simp at h
                            | some pad =>
                                generalize hPadZeroOpt : allZeroSlice? y
                                    (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1 +
                                        idxWidth codec.witnessBits decoded.1 + i)
                                    (codec.witnessBits decoded.1 - i) = padZeroOpt at h
                                cases padZeroOpt with
                                | none => simp at h
                                | some padZero =>
                                    by_cases hpad : padZero = true
                                    · simp [hpad] at h
                                      cases h
                                      exact hlen
                                    · simp [hpad] at h
                      · simp [hi] at h
            · simp [hlen] at h
      · simp [htag] at h

/-- A wrong version tag is rejected before any dependent field slicing occurs. -/
theorem parseTreeMCSPPrefixInput_bad_tag
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    {tag : Nat}
    (htag : readNatBE y 0 tagLen = some tag)
    (hbad : tag ≠ treePrefixTag) :
    parseTreeMCSPPrefixInput threshold codec y = none := by
  simp [parseTreeMCSPPrefixInput, htag, hbad]

/-- Parser failures are nonmembers of the prefix-extension language. -/
theorem parseTreeMCSPPrefixInput_malformed_rejected
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (hparse : parseTreeMCSPPrefixInput threshold codec y = none) :
    PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec) m y = false := by
  exact PrefixExtensionLanguage_rejects_malformed
    (treeMCSPConcretePrefixParser threshold codec) y hparse


/--
Concrete runtime-aware parser package, parameterized by the still-open parser
runtime obligation.

Supplying `parser_polynomial_time_in_M` remains future work; this constructor
only wires in the already proved malformed-input and length-convention facts and
therefore does not manufacture a fake runtime theorem.
-/
def treeMCSPRuntimeAwarePrefixParser
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    (parser_polynomial_time_in_M : Prop) :
    RuntimeAwarePrefixParser
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec) where
  parser := treeMCSPConcretePrefixParser threshold codec
  parser_polynomial_time_in_M := parser_polynomial_time_in_M
  malformed_inputs_rejected := by
    intro m y hparse
    exact parseTreeMCSPPrefixInput_malformed_rejected threshold codec y hparse
  length_convention_matches_M := by
    intro m y input hparse
    exact parseTreeMCSPPrefixInput_length_convention threshold codec y input hparse

end ContractExpansion
end Frontier
end Pnp4
