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


/--
Canonical raw fields for the tree-MCSP prefix serialization.

The parser ultimately produces a `PrefixInput`, but an encoder should not have to
invert the parser or choose hidden data.  This structure exposes exactly the
canonical payloads that are written into the byte/gamma/table/index/witness
layout.  The proof `prefixLength_le` is the same bound required by `PrefixInput`,
and the witness block is split into an active prefix `p` followed by implicit
zero padding of length `codec.witnessBits n - i`.
-/
structure CanonicalRawTreeMCSPPrefixFields
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) where
  n : Nat
  x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)
  i : Nat
  prefixLength_le : i ≤ codec.witnessBits n
  p : PrefixBitVec i

/-- Big-endian bit `j` of a fixed-width natural-number field. -/
def natBitBE (value width : Nat) (j : Fin width) : Bool :=
  value / 2 ^ (width - 1 - j.1) % 2 = 1

/--
Bit `j` of the Elias-gamma code for `n + 1`.

For the positive value `n + 1`, the first `bitLength (n + 1) - 1` bits are the
unary zero prefix.  The remaining bits are the ordinary big-endian representation
of `n + 1` in exactly `bitLength (n + 1)` bits.
-/
def gammaBit (n : Nat) (j : Fin (gammaLen n)) : Bool :=
  let zeros := bitLength (n + 1) - 1
  if hj : j.1 < zeros then
    false
  else
    natBitBE (n + 1) (bitLength (n + 1)) ⟨j.1 - zeros, by
      have hlen : gammaLen n = zeros + bitLength (n + 1) := by
        unfold gammaLen
        omega
      rw [hlen] at j
      omega⟩

/--
Computable encoder for canonical raw tree-MCSP prefix fields.

The output has the canonical ambient length by construction.  Its layout is
`tag ++ gamma(n+1) ++ x ++ i ++ p ++ zero-pad`, matching the parser convention.
This is intentionally just serialization infrastructure: it uses no
`Classical.choose`, no noncomputable parser inversion, and no runtime or
NP-membership claim.
-/
def encodeTreeMCSPPrefixFields
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (fields : CanonicalRawTreeMCSPPrefixFields codec) :
    PrefixBitVec (treeMCSPPrefixM codec fields.n) :=
  fun j =>
    if hTag : j.1 < tagLen then
      natBitBE treePrefixTag tagLen ⟨j.1, hTag⟩
    else
      let gammaOffset := tagLen
      if hGamma : j.1 < gammaOffset + gammaLen fields.n then
        gammaBit fields.n ⟨j.1 - gammaOffset, by omega⟩
      else
        let xOffset := tagLen + gammaLen fields.n
        if hX : j.1 < xOffset + Pnp3.Models.Partial.tableLen fields.n then
          fields.x ⟨j.1 - xOffset, by omega⟩
        else
          let iOffset := xOffset + Pnp3.Models.Partial.tableLen fields.n
          if hI : j.1 < iOffset + idxWidth codec.witnessBits fields.n then
            natBitBE fields.i (idxWidth codec.witnessBits fields.n) ⟨j.1 - iOffset, by omega⟩
          else
            let pOffset := iOffset + idxWidth codec.witnessBits fields.n
            if hP : j.1 < pOffset + fields.i then
              fields.p ⟨j.1 - pOffset, by omega⟩
            else
              false

/-- The raw-field encoder's length is the canonical `M(n)` by its result type. -/
theorem encodeTreeMCSPPrefixFields_length_convention
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (fields : CanonicalRawTreeMCSPPrefixFields codec) :
    (treeMCSPPrefixM codec fields.n) = treeMCSPPrefixM codec fields.n := by
  rfl

/--
Canonical parsed input represented by canonical raw fields.

This is the target object for the intended parser/encoder round trip: it uses
the fixed tree-prefix tag, copies the raw `n`, truth table `x`, active prefix
length `i`, bound proof, and prefix payload `p`, and fills the inactive suffix
with exactly `codec.witnessBits n - i` zero bits.  The definition is fully
computable and does not invert the parser.
-/
def CanonicalRawTreeMCSPPrefixFields.toPrefixInput
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (fields : CanonicalRawTreeMCSPPrefixFields codec) :
    PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec fields.n) where
  tag := treePrefixTag
  n := fields.n
  x := fields.x
  i := fields.i
  prefixLength_le := fields.prefixLength_le
  p := fields.p
  padBits := codec.witnessBits fields.n - fields.i
  pad := fun _ => false

/-- The first committed decoder lemma for P1P-02L3: the encoder writes the byte tag. -/
theorem readNatBE_encode_tag
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (fields : CanonicalRawTreeMCSPPrefixFields codec) :
    readNatBE (encodeTreeMCSPPrefixFields codec fields) 0 tagLen = some treePrefixTag := by
  have h0 : 0 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  have h1 : 1 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  have h2 : 2 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  have h3 : 3 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  have h4 : 4 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  have h5 : 5 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  have h6 : 6 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  have h7 : 7 < treeMCSPPrefixM codec fields.n := by unfold treeMCSPPrefixM tagLen; omega
  simp [readNatBE, readBit?, encodeTreeMCSPPrefixFields, tagLen, treePrefixTag, natBitBE,
    h0, h1, h2, h3, h4, h5, h6, h7]

/-- The encoded truth-table slice is exactly the raw `x` field. -/
theorem sliceBits_encode_x
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (fields : CanonicalRawTreeMCSPPrefixFields codec) :
    sliceBits? (encodeTreeMCSPPrefixFields codec fields)
      (tagLen + gammaLen fields.n) (Pnp3.Models.Partial.tableLen fields.n) =
      some fields.x := by
  unfold sliceBits?
  have hWithin : tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n ≤
      treeMCSPPrefixM codec fields.n := by
    unfold treeMCSPPrefixM
    omega
  simp [hWithin]
  funext j
  unfold encodeTreeMCSPPrefixFields
  have hnotTag : ¬ tagLen + gammaLen fields.n + j.1 < tagLen := by omega
  have hx : tagLen + gammaLen fields.n + j.1 <
      tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n := by
    exact Nat.add_lt_add_left j.2 (tagLen + gammaLen fields.n)
  simp [hnotTag, hx]

/-- The encoded active witness-prefix slice is exactly the raw `p` field. -/
theorem sliceBits_encode_p
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (fields : CanonicalRawTreeMCSPPrefixFields codec) :
    sliceBits? (encodeTreeMCSPPrefixFields codec fields)
      (tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
        idxWidth codec.witnessBits fields.n) fields.i =
      some fields.p := by
  unfold sliceBits?
  have hWithin : tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
      idxWidth codec.witnessBits fields.n + fields.i ≤ treeMCSPPrefixM codec fields.n := by
    unfold treeMCSPPrefixM
    exact Nat.add_le_add_left fields.prefixLength_le _
  simp [hWithin]
  funext j
  unfold encodeTreeMCSPPrefixFields
  have hnotTag : ¬ tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
      idxWidth codec.witnessBits fields.n + j.1 < tagLen := by omega
  have hnotGamma : ¬ tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
      idxWidth codec.witnessBits fields.n + j.1 < tagLen + gammaLen fields.n := by omega
  have hnotX : ¬ tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
      idxWidth codec.witnessBits fields.n + j.1 <
        tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n := by omega
  have hnotI : ¬ tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
      idxWidth codec.witnessBits fields.n + j.1 <
        tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
          idxWidth codec.witnessBits fields.n := by omega
  have hp : tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
      idxWidth codec.witnessBits fields.n + j.1 <
        tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
          idxWidth codec.witnessBits fields.n + fields.i := by
    exact Nat.add_lt_add_left j.2 _
  simp [hnotTag, hnotGamma, hnotX, hnotI, hp]

/--
P1P-02L3 partial-progress marker.

The full canonical theorem
`parseTreeMCSPPrefixInput threshold codec (encodeTreeMCSPPrefixFields codec fields)
 = some (fields.toPrefixInput codec)` remains open.  The landed partial lemmas
above isolate the already-verified tag, table slice, and active-prefix slice;
the remaining proof work is the generic Elias-gamma round trip and big-endian
index-field round trip, plus dependent proof-field normalization in the final
`PrefixInput` equality.
-/
theorem parse_encodeTreeMCSPPrefixFields_partial_obligation
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (fields : CanonicalRawTreeMCSPPrefixFields codec) :
    readNatBE (encodeTreeMCSPPrefixFields codec fields) 0 tagLen = some treePrefixTag ∧
      sliceBits? (encodeTreeMCSPPrefixFields codec fields)
        (tagLen + gammaLen fields.n) (Pnp3.Models.Partial.tableLen fields.n) = some fields.x ∧
      sliceBits? (encodeTreeMCSPPrefixFields codec fields)
        (tagLen + gammaLen fields.n + Pnp3.Models.Partial.tableLen fields.n +
          idxWidth codec.witnessBits fields.n) fields.i = some fields.p := by
  exact ⟨readNatBE_encode_tag codec fields, sliceBits_encode_x codec fields,
    sliceBits_encode_p codec fields⟩

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
Successful parses obey the concrete single-length-per-target convention.

This is the R1-B2a hook: if the concrete parser returns a `PrefixInput`, then
the ambient input length is exactly the canonical `treeMCSPPrefixM` for the
parsed target parameter.
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
  | none =>
      simp [htagRead] at h
  | some tag =>
      simp [htagRead] at h
      by_cases htag : tag = treePrefixTag
      · simp [htag] at h
        cases hgamma : decodeGamma? y tagLen with
        | none =>
            simp [hgamma] at h
        | some decoded =>
            simp [hgamma] at h
            by_cases hlen : m = treeMCSPPrefixM codec decoded.1
            · simp [hlen] at h
              cases hx : sliceBits? y (tagLen + decoded.2) (Pnp3.Models.Partial.tableLen decoded.1) with
              | none =>
                  simp [hx] at h
              | some x =>
                  simp [hx] at h
                  cases hiRead : readNatBE y (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1)
                      (idxWidth codec.witnessBits decoded.1) with
                  | none =>
                      simp [hiRead] at h
                  | some i =>
                      simp [hiRead] at h
                      by_cases hi : i ≤ codec.witnessBits decoded.1
                      · simp [hi] at h
                        cases hp : sliceBits? y
                            (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1 +
                              idxWidth codec.witnessBits decoded.1) i with
                        | none =>
                            simp [hp] at h
                        | some p =>
                            simp [hp] at h
                            cases hpad : sliceBits? y
                                (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1 +
                                  idxWidth codec.witnessBits decoded.1 + i)
                                (codec.witnessBits decoded.1 - i) with
                            | none =>
                                simp [hpad] at h
                            | some pad =>
                                simp [hpad] at h
                                cases hzero : allZeroSlice? y
                                    (tagLen + decoded.2 + Pnp3.Models.Partial.tableLen decoded.1 +
                                      idxWidth codec.witnessBits decoded.1 + i)
                                    (codec.witnessBits decoded.1 - i) with
                                | none =>
                                    simp [hzero] at h
                                | some padZero =>
                                    simp [hzero] at h
                                    by_cases hz : padZero = true
                                    · simp [hz] at h
                                      cases h
                                      exact hlen
                                    · simp [hz] at h
                      · simp [hi] at h
            · simp [hlen] at h
      · simp [htag] at h

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
Concrete runtime-aware parser package, with only the parser-local facts filled.

The polynomial-time parser field remains an explicit staged proposition supplied
by the caller; this definition does not manufacture a `True` runtime proof and
does not claim NP membership.
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
