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

/-- Big-endian bit view of a natural number at a raw index in a fixed-width field. -/
def natBitBEAt (value width idx : Nat) : Bool :=
  (value / 2 ^ (width - 1 - idx)) % 2 = 1

/-- Big-endian bit view of a natural number restricted to a fixed width. -/
def natBitBE (value width : Nat) (j : Fin width) : Bool :=
  natBitBEAt value width j.1

/--
The canonical Elias-gamma bit for the natural number `n` encoded as `n + 1`.

The first `bitLength (n + 1) - 1` positions are the unary zero prefix, the next
position is the terminator, and the remaining positions are the low payload
bits of `n + 1` in big-endian order.  This is executable and uses only the
explicit field convention, not parser inversion or choice.
-/
def gammaBit (n : Nat) (j : Fin (gammaLen n)) : Bool :=
  let zeros := bitLength (n + 1) - 1
  if j.1 < zeros then
    false
  else if j.1 = zeros then
    true
  else
    natBitBEAt (n + 1 - 2 ^ zeros) zeros (j.1 - (zeros + 1))

/-- Read a component bit at an offset, returning `false` off the component. -/
def componentBit {M len : Nat}
    (offset : Nat)
    (bits : PrefixBitVec len)
    (j : Fin M) : Bool :=
  if h : offset ≤ j.1 ∧ j.1 < offset + len then
    bits ⟨j.1 - offset, by omega⟩
  else
    false

/--
Computable canonical encoder for raw tree-MCSP prefix fields.

The output length is definitionally `treeMCSPPrefixM codec n`.  The final
witness-prefix block has fixed size `codec.witnessBits n`: the first `i` bits
come from `p`, and every inactive padding bit is encoded as zero.
-/
def encodeTreeMCSPPrefixFields
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (i : Nat)
    (_hi : i ≤ codec.witnessBits n)
    (p : PrefixBitVec i) :
    PrefixBitVec (treeMCSPPrefixM codec n) :=
  fun j =>
    if htag : j.1 < tagLen then
      natBitBE treePrefixTag tagLen ⟨j.1, htag⟩
    else if hgamma : tagLen ≤ j.1 ∧ j.1 < tagLen + gammaLen n then
      gammaBit n ⟨j.1 - tagLen, by omega⟩
    else
      let xOffset := tagLen + gammaLen n
      let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
      let pOffset := iOffset + idxWidth codec.witnessBits n
      if hx : xOffset ≤ j.1 ∧ j.1 < xOffset + Pnp3.Models.Partial.tableLen n then
        x ⟨j.1 - xOffset, by omega⟩
      else if hiField : iOffset ≤ j.1 ∧ j.1 < iOffset + idxWidth codec.witnessBits n then
        natBitBE i (idxWidth codec.witnessBits n) ⟨j.1 - iOffset, by omega⟩
      else if hp : pOffset ≤ j.1 ∧ j.1 < pOffset + i then
        p ⟨j.1 - pOffset, by omega⟩
      else
        false

/-- Canonical encoder for an already parsed input whose fields satisfy the raw convention. -/
def encodeTreeMCSPPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) :
    PrefixBitVec (treeMCSPPrefixM codec input.n) :=
  encodeTreeMCSPPrefixFields codec input.n input.x input.i input.prefixLength_le input.p

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


/--
Successful concrete parsing enforces the single ambient-length convention.

This is the serialization-side fact required by the R1-B2a runtime interface:
the parser accepts no trailing garbage and no alternate padding convention, so
the ambient string length is exactly `treeMCSPPrefixM codec input.n` for the
decoded target parameter.
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
  cases htagRead : readNatBE y 0 tagLen with
  | none => simp [htagRead] at h
  | some tag =>
      by_cases htag : tag = treePrefixTag
      · cases hgamma : decodeGamma? y tagLen with
        | none => simp [htagRead, htag, hgamma] at h
        | some decoded =>
            let n := decoded.1
            by_cases hlen : m = treeMCSPPrefixM codec n
            · let xOffset := tagLen + decoded.2
              cases hx : sliceBits? y xOffset (Pnp3.Models.Partial.tableLen n) with
              | none => simp [htagRead, htag, hgamma, hlen, hx, n, xOffset] at h
              | some x =>
                  let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
                  cases hiRead : readNatBE y iOffset (idxWidth codec.witnessBits n) with
                  | none => simp [htagRead, htag, hgamma, hlen, hx, hiRead, n, xOffset, iOffset] at h
                  | some i =>
                      by_cases hi : i ≤ codec.witnessBits n
                      · let pOffset := iOffset + idxWidth codec.witnessBits n
                        cases hp : sliceBits? y pOffset i with
                        | none => simp [htagRead, htag, hgamma, hlen, hx, hiRead, hi, hp, n, xOffset, iOffset, pOffset] at h
                        | some p =>
                            let padOffset := pOffset + i
                            let padWidth := codec.witnessBits n - i
                            cases hpad : sliceBits? y padOffset padWidth with
                            | none => simp [htagRead, htag, hgamma, hlen, hx, hiRead, hi, hp, hpad, n, xOffset, iOffset, pOffset, padOffset, padWidth] at h
                            | some pad =>
                                cases hzeroRead : allZeroSlice? y padOffset padWidth with
                                | none => simp [htagRead, htag, hgamma, hlen, hx, hiRead, hi, hp, hpad, hzeroRead, n, xOffset, iOffset, pOffset, padOffset, padWidth] at h
                                | some padZero =>
                                    by_cases hzero : padZero = true
                                    · simp [htagRead, htag, hgamma, hlen, hx, hiRead, hi, hp, hpad, hzeroRead, hzero, n, xOffset, iOffset, pOffset, padOffset, padWidth] at h
                                      cases h
                                      exact hlen
                                    · simp [htagRead, htag, hgamma, hlen, hx, hiRead, hi, hp, hpad, hzeroRead, hzero, n, xOffset, iOffset, pOffset, padOffset, padWidth] at h
                      · simp [htagRead, htag, hgamma, hlen, hx, hiRead, hi, n, xOffset, iOffset] at h
            · simp [htagRead, htag, hgamma, hlen, n] at h
      · simp [htagRead, htag] at h

/-- The concrete parser packaged in the existing `PrefixParser` interface. -/
def treeMCSPConcretePrefixParser
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold) :
    PrefixParser (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) where
  tag := treePrefixTag
  M := treeMCSPPrefixM codec
  parse := parseTreeMCSPPrefixInput threshold codec

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

/--
The concrete parser satisfies the runtime-interface length-convention field.

This theorem intentionally packages only the proved length fact; it does not
claim a parser running-time bound or instantiate `RuntimeAwarePrefixParser`,
whose `parser_polynomial_time_in_M` field remains a separate real obligation.
-/
theorem treeMCSPConcretePrefixParser_length_convention_matches_M
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold) :
    ∀ {m : Nat}, ∀ y : PrefixBitVec m,
      ∀ input : PrefixInput
        (treeMCSPSearchProblem threshold
          (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m,
        parsePrefixInput (treeMCSPConcretePrefixParser threshold codec) y = some input →
          m = (treeMCSPConcretePrefixParser threshold codec).M input.n := by
  intro m y input h
  exact parseTreeMCSPPrefixInput_length_convention threshold codec y input h

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

end ContractExpansion
end Frontier
end Pnp4
