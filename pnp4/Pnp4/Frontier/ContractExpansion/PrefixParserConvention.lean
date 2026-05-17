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

/-- Positive naturals have a positive binary length. -/
theorem bitLength_pos_of_pos
    {n : Nat} (h : 0 < n) :
    0 < bitLength n := by
  unfold bitLength
  simp [Nat.ne_of_gt h]

/-- Every natural fits in its own `bitLength`-wide unsigned binary field. -/
theorem nat_lt_two_pow_bitLength
    (n : Nat) :
    n < 2 ^ bitLength n := by
  by_cases hn : n = 0
  · simp [bitLength, hn]
  · unfold bitLength
    simp [hn, Nat.lt_log2_self]

/-- A standalone big-endian field as a dependent bit-vector. -/
def natBEField (value width : Nat) : PrefixBitVec width :=
  fun j => natBitBE value width j

/--
`readNatBE` depends only on the bits in the width-many positions that it reads.

The two offsets may live in different ambient vectors; this is the small
transport lemma used to compare an in-place field inside a parser input with a
standalone `natBEField`.
-/
theorem readNatBE_eq_of_readBit_eq
    {m₁ m₂ : Nat}
    (y₁ : PrefixBitVec m₁)
    (y₂ : PrefixBitVec m₂)
    (offset₁ offset₂ width : Nat)
    (h : ∀ t : Nat, t < width →
      readBit? y₁ (offset₁ + t) = readBit? y₂ (offset₂ + t)) :
    readNatBE y₁ offset₁ width = readNatBE y₂ offset₂ width := by
  induction width generalizing offset₁ offset₂ with
  | zero =>
      simp [readNatBE]
  | succ k ih =>
      rw [readNatBE, readNatBE]
      have hb : readBit? y₁ offset₁ = readBit? y₂ offset₂ := by
        simpa using h 0 (Nat.zero_lt_succ k)
      rw [hb]
      cases readBit? y₂ offset₂ <;> simp
      have hrec : readNatBE y₁ (offset₁ + 1) k = readNatBE y₂ (offset₂ + 1) k := by
        apply ih
        intro t ht
        have := h (t + 1) (Nat.succ_lt_succ ht)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      rw [hrec]

/--
The tail of a `(k+1)`-bit big-endian field is the standalone `k`-bit field for
`value % 2^k`.  This is the bit-level step in the reader inversion induction.
-/
theorem readNatBE_natBEField_tail
    (value k : Nat) :
    readNatBE (natBEField value (k + 1)) 1 k =
      readNatBE (natBEField (value % 2 ^ k) k) 0 k := by
  apply readNatBE_eq_of_readBit_eq
  intro t ht
  unfold readBit? natBEField natBitBE
  have ht1 : 1 + t < k + 1 := by omega
  have ht0 : t < k := ht
  simp [ht1, ht0]
  have he : k - 1 - t < k := by omega
  have hbit : (value % 2 ^ k).testBit (k - 1 - t) =
      value.testBit (k - 1 - t) := by
    rw [Nat.testBit_mod_two_pow]
    simp [he]
  rw [show k - (1 + t) = k - 1 - t by omega]
  simpa [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two] using hbit.symm

/--
Reading a standalone `natBEField` at offset zero recovers the encoded value,
provided the value fits in the declared fixed width.
-/
theorem readNatBE_natBEField_zero
    (value width : Nat)
    (h : value < 2 ^ width) :
    readNatBE (natBEField value width) 0 width = some value := by
  induction width generalizing value with
  | zero =>
      have hv : value = 0 := by omega
      simp [readNatBE, hv]
  | succ k ih =>
      rw [readNatBE]
      have h0 : 0 < k + 1 := Nat.zero_lt_succ k
      simp [readBit?, natBEField, h0]
      have htail : readNatBE (natBEField value (k + 1)) 1 k =
          readNatBE (natBEField (value % 2 ^ k) k) 0 k :=
        readNatBE_natBEField_tail value k
      rw [htail]
      have hmod : value % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      rw [ih (value % 2 ^ k) hmod]
      have hq : value / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
        rw [Nat.pow_succ] at h
        simpa [Nat.mul_comm] using h
      have hq_le : value / 2 ^ k ≤ 1 := Nat.lt_succ_iff.mp hq
      have hq_cases : value / 2 ^ k = 0 ∨ value / 2 ^ k = 1 := by
        rcases Nat.eq_zero_or_pos (value / 2 ^ k) with hzero | hpos
        · exact Or.inl hzero
        · exact Or.inr (Nat.le_antisymm hq_le hpos)
      simp only [Option.bind_some, Option.some.injEq]
      rcases hq_cases with hq0 | hq1
      · have hbit : natBitBE value (k + 1) ⟨0, h0⟩ = false := by
          unfold natBitBE
          simp [hq0]
        change (if natBitBE value (k + 1) ⟨0, h0⟩ then 2 ^ k else 0) +
          value % 2 ^ k = value
        rw [hbit]
        simp
        have hdecomp := Nat.mod_add_div value (2 ^ k)
        calc
          value % 2 ^ k = value % 2 ^ k + 2 ^ k * (value / 2 ^ k) := by
            rw [hq0]
            simp
          _ = value := hdecomp
      · have hbit : natBitBE value (k + 1) ⟨0, h0⟩ = true := by
          unfold natBitBE
          simp [hq1]
        change (if natBitBE value (k + 1) ⟨0, h0⟩ then 2 ^ k else 0) +
          value % 2 ^ k = value
        rw [hbit]
        simp
        have hdecomp := Nat.mod_add_div value (2 ^ k)
        calc
          2 ^ k + value % 2 ^ k = value % 2 ^ k + 2 ^ k * (value / 2 ^ k) := by
            rw [hq1]
            omega
          _ = value := hdecomp

/--
One-step big-endian digit identity used by the slice reader proof.

Selecting the `k`-th big-endian digit (i.e. `a / 2^k % 2`) and adding `a % 2^k`
recovers `a % 2^(k+1)`.  This is the arithmetic core of the inductive step in
`readNatBE_natBEField_slice` below.

Ported from PR #1338 to make sub-slice reads of `natBEField` available without
re-deriving them from `readNatBE_eq_of_readBit_eq` at every call site.
-/
theorem be_digit_step (a k : Nat) :
    (if a / 2 ^ k % 2 = 1 then 2 ^ k else 0) + a % 2 ^ k =
      a % 2 ^ (k + 1) := by
  have hpow2 : 2 ^ (k + 1) = 2 ^ k * 2 := by
    rw [Nat.pow_succ]
  have hq : (a % (2 ^ k * 2)) / 2 ^ k = a / 2 ^ k % 2 := by
    simpa using (Nat.mod_mul_right_div_self a (2 ^ k) 2)
  have hr : (a % (2 ^ k * 2)) % 2 ^ k = a % 2 ^ k := by
    exact Nat.mod_mul_right_mod a (2 ^ k) 2
  have hq_lt : (a / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide : 0 < 2)
  have hq_cases : a / 2 ^ k % 2 = 0 ∨ a / 2 ^ k % 2 = 1 := by
    omega
  calc
    (if a / 2 ^ k % 2 = 1 then 2 ^ k else 0) + a % 2 ^ k
        = (a % (2 ^ k * 2)) / 2 ^ k * 2 ^ k +
            (a % (2 ^ k * 2)) % 2 ^ k := by
            rcases hq_cases with hzero | hone
            · simp [hzero, hq, hr]
            · simp [hone, hq, hr]
    _ = a % (2 ^ k * 2) := by
          rw [Nat.div_add_mod']
    _ = a % 2 ^ (k + 1) := by
          rw [hpow2]

/--
Reading a bounded sub-slice of a stand-alone big-endian field returns exactly
the natural represented by that slice: the quotient drops the low bits to the
right of the slice; the modulo forgets the high bits to the left of it.

This generalises `readNatBE_natBEField_zero` (the `offset = 0`, `len = width`
case) and is the lemma a future P1P-02L₅ worker needs to decode the Elias-gamma
payload, which lives at a non-zero offset inside its enclosing field.

Ported from PR #1338 to extend the proof library landed by PR #1339.
-/
theorem readNatBE_natBEField_slice
    (value width offset len : Nat)
    (hfit : offset + len ≤ width) :
    readNatBE (natBEField value width) offset len =
      some ((value / 2 ^ (width - (offset + len))) % 2 ^ len) := by
  induction len generalizing offset with
  | zero =>
      simp [readNatBE, Nat.mod_one]
  | succ k ih =>
      have hoff : offset < width := by omega
      have hfitRest : offset + 1 + k ≤ width := by omega
      let shift := width - (offset + (k + 1))
      have hsub : width - 1 - offset = shift + k := by omega
      have hrest : width - (offset + 1 + k) = shift := by omega
      have hpowadd : 2 ^ (shift + k) = 2 ^ shift * 2 ^ k := by
        rw [Nat.pow_add]
      simp [readNatBE, readBit?, natBEField, natBitBE, hoff,
        ih (offset + 1) hfitRest, hsub, hrest, hpowadd]
      rw [show width - (offset + (k + 1)) = shift by rfl]
      rw [← Nat.div_div_eq_div_mul]
      exact be_digit_step (value / 2 ^ shift) k

/-- Values bounded by the witness length fit in the parser's index-width field. -/
theorem prefixLength_lt_two_pow_idxWidth
    {W : Nat → Nat} {n i : Nat}
    (hi : i ≤ W n) :
    i < 2 ^ idxWidth W n := by
  unfold idxWidth
  exact Nat.lt_of_le_of_lt hi (nat_lt_two_pow_bitLength (W n))

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

/-- Positive values dominate the top place value of their `bitLength` field. -/
theorem two_pow_bitLength_pred_le
    {a : Nat} (ha : 0 < a) :
    2 ^ (bitLength a - 1) ≤ a := by
  unfold bitLength
  have hne : a ≠ 0 := Nat.ne_of_gt ha
  simp [hne, Nat.log2_self_le hne]

/-- The gamma length is the zero-prefix length plus the full binary payload. -/
theorem gammaLen_eq_zeros_add_bitLength (n : Nat) :
    gammaLen n = (bitLength (n + 1) - 1) + bitLength (n + 1) := by
  unfold gammaLen
  have hpos : 0 < bitLength (n + 1) := bitLength_pos_of_pos (Nat.succ_pos n)
  omega

/-- Equivalent arithmetic form of `gammaLen`: `2 * zeros + 1`. -/
theorem gammaLen_eq_two_mul_zeros_add_one (n : Nat) :
    gammaLen n = 2 * (bitLength (n + 1) - 1) + 1 := by
  unfold gammaLen
  have hpos : 0 < bitLength (n + 1) := bitLength_pos_of_pos (Nat.succ_pos n)
  omega

/-- Gamma-code positions before the unary terminator are zero bits. -/
theorem gammaBit_zero_prefix
    (n : Nat) {j : Fin (gammaLen n)}
    (hj : j.1 < bitLength (n + 1) - 1) :
    gammaBit n j = false := by
  unfold gammaBit
  simp [hj]

/-- The first non-zero bit after the unary zero prefix is the gamma terminator. -/
theorem gammaBit_terminator (n : Nat) :
    gammaBit n ⟨bitLength (n + 1) - 1, by
      rw [gammaLen_eq_zeros_add_bitLength]
      exact Nat.lt_add_of_pos_right (bitLength_pos_of_pos (Nat.succ_pos n))⟩ = true := by
  unfold gammaBit natBitBE
  let L := bitLength (n + 1)
  let zeros := L - 1
  have hLpos : 0 < L := by
    exact bitLength_pos_of_pos (Nat.succ_pos n)
  have hnot : ¬ zeros < zeros := by omega
  simp
  have hpow_le : 2 ^ zeros ≤ n + 1 := by
    simpa [L, zeros] using two_pow_bitLength_pred_le (a := n + 1) (Nat.succ_pos n)
  have hlt : n + 1 < 2 ^ (zeros + 1) := by
    have hfit := nat_lt_two_pow_bitLength (n + 1)
    have hL : L = zeros + 1 := by omega
    simpa [L, hL] using hfit
  have hq_lt : (n + 1) / 2 ^ zeros < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos zeros)]
    simpa [Nat.pow_succ, Nat.mul_comm] using hlt
  have hq_pos : 0 < (n + 1) / 2 ^ zeros := by
    exact Nat.div_pos hpow_le (Nat.two_pow_pos zeros)
  have hq : (n + 1) / 2 ^ zeros = 1 := by
    omega
  exact show (n + 1) / 2 ^ zeros % 2 = 1 by simp [hq]

/-- `gammaBit` agrees with the underlying big-endian payload field after the unary prefix. -/
theorem gammaBit_payload_eq_natBitBE
    (n : Nat) {t : Nat}
    (ht : t < bitLength (n + 1)) :
    gammaBit n ⟨(bitLength (n + 1) - 1) + t, by
      rw [gammaLen_eq_zeros_add_bitLength]
      exact Nat.add_lt_add_left ht _⟩ =
      natBitBE (n + 1) (bitLength (n + 1)) ⟨t, ht⟩ := by
  unfold gammaBit
  let zeros := bitLength (n + 1) - 1
  have hnot : ¬ zeros + t < zeros := by omega
  simp [zeros, hnot]

/-- Reading the binary payload portion of a gamma code recovers the low `zeros` bits. -/
theorem readNatBE_gammaBit_payload (n : Nat) :
    readNatBE
      (fun j : Fin (gammaLen n) => gammaBit n j)
      (bitLength (n + 1))
      (bitLength (n + 1) - 1) =
    some ((n + 1) % 2 ^ (bitLength (n + 1) - 1)) := by
  let L := bitLength (n + 1)
  let zeros := L - 1
  have hLpos : 0 < L := by
    exact bitLength_pos_of_pos (Nat.succ_pos n)
  have hL : L = zeros + 1 := by omega
  calc
    readNatBE
        (fun j : Fin (gammaLen n) => gammaBit n j)
        (bitLength (n + 1))
        (bitLength (n + 1) - 1) =
        readNatBE (natBEField (n + 1) L) 1 zeros := by
      apply readNatBE_eq_of_readBit_eq
      intro t ht
      unfold readBit? natBEField
      have hGamma : bitLength (n + 1) + t < gammaLen n := by
        rw [gammaLen_eq_zeros_add_bitLength]
        omega
      have hNat : 1 + t < L := by omega
      simp [hGamma, hNat]
      have hg := gammaBit_payload_eq_natBitBE n (t := 1 + t) (by omega)
      convert hg using 3; omega
    _ = some (((n + 1) / 2 ^ (L - (1 + zeros))) % 2 ^ zeros) := by
      exact readNatBE_natBEField_slice (n + 1) L 1 zeros (by omega)
    _ = some ((n + 1) % 2 ^ (bitLength (n + 1) - 1)) := by
      have hzero : L - (1 + zeros) = 0 := by omega
      simp [L, zeros, hzero]

/-- The gamma payload plus its implicit leading one reconstructs `n + 1`. -/
theorem gamma_payload_value (n : Nat) :
    2 ^ (bitLength (n + 1) - 1) +
      (n + 1) % 2 ^ (bitLength (n + 1) - 1) = n + 1 := by
  let L := bitLength (n + 1)
  let zeros := L - 1
  have hLpos : 0 < L := by
    exact bitLength_pos_of_pos (Nat.succ_pos n)
  have hpow_le : 2 ^ zeros ≤ n + 1 := by
    simpa [L, zeros] using two_pow_bitLength_pred_le (a := n + 1) (Nat.succ_pos n)
  have hlt : n + 1 < 2 ^ (zeros + 1) := by
    have hfit := nat_lt_two_pow_bitLength (n + 1)
    have hL : L = zeros + 1 := by omega
    simpa [L, hL] using hfit
  have hq_lt : (n + 1) / 2 ^ zeros < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos zeros)]
    simpa [Nat.pow_succ, Nat.mul_comm] using hlt
  have hq_pos : 0 < (n + 1) / 2 ^ zeros := by
    exact Nat.div_pos hpow_le (Nat.two_pow_pos zeros)
  have hq : (n + 1) / 2 ^ zeros = 1 := by
    omega
  have hdecomp := Nat.mod_add_div (n + 1) (2 ^ zeros)
  calc
    2 ^ (bitLength (n + 1) - 1) +
        (n + 1) % 2 ^ (bitLength (n + 1) - 1)
        = (n + 1) % 2 ^ zeros + 2 ^ zeros * ((n + 1) / 2 ^ zeros) := by
          simp [L, zeros, hq]
          omega
    _ = n + 1 := hdecomp

/-- General recursion invariant: enough fuel decodes from any point in the zero run. -/
theorem decodeGammaAux_gammaBit_from
    (n fuel zeros : Nat)
    (hzeros : zeros ≤ bitLength (n + 1) - 1)
    (hfuel : bitLength (n + 1) - 1 - zeros < fuel) :
    decodeGammaAux?
      (fun j : Fin (gammaLen n) => gammaBit n j)
      0 fuel zeros = some (n, gammaLen n) := by
  induction fuel generalizing zeros with
  | zero => omega
  | succ fuel' ih =>
      rw [decodeGammaAux?]
      have hLpos : 0 < bitLength (n + 1) := bitLength_pos_of_pos (Nat.succ_pos n)
      have hread : readBit? (fun j : Fin (gammaLen n) => gammaBit n j) (0 + zeros) =
          some (gammaBit n ⟨zeros, by
            rw [gammaLen_eq_zeros_add_bitLength]
            omega⟩) := by
        unfold readBit?
        have hb : zeros < gammaLen n := by
          rw [gammaLen_eq_zeros_add_bitLength]
          omega
        simp [hb]
      rw [hread]
      by_cases hz : zeros < bitLength (n + 1) - 1
      · have hbit : gammaBit n ⟨zeros, by
            rw [gammaLen_eq_zeros_add_bitLength]
            omega⟩ = false := by
          exact gammaBit_zero_prefix n hz
        simp [hbit]
        apply ih
        · omega
        · have hstep : bitLength (n + 1) - 1 - (zeros + 1) + 1 =
              bitLength (n + 1) - 1 - zeros := by omega
          omega
      · have hzeq : zeros = bitLength (n + 1) - 1 := by omega
        subst hzeq
        simp [gammaBit_terminator]
        rw [show bitLength (n + 1) - 1 + 1 = bitLength (n + 1) by omega]
        rw [readNatBE_gammaBit_payload]
        simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq]
        constructor
        · have hv := gamma_payload_value n
          omega
        · rw [gammaLen_eq_two_mul_zeros_add_one]

/-- `decodeGammaAux?` inverts the standalone gamma encoder with the parser's initial fuel. -/
theorem decodeGammaAux_gammaBit (n : Nat) :
    decodeGammaAux?
      (fun j : Fin (gammaLen n) => gammaBit n j)
      0
      (gammaLen n + 1)
      0 = some (n, gammaLen n) := by
  apply decodeGammaAux_gammaBit_from
  · omega
  · have hlen : gammaLen n = 2 * (bitLength (n + 1) - 1) + 1 :=
      gammaLen_eq_two_mul_zeros_add_one n
    omega

/-- `decodeGamma?` inverts the standalone Elias-gamma encoder. -/
theorem decodeGamma_gammaBit (n : Nat) :
    decodeGamma?
      (fun j : Fin (gammaLen n) => gammaBit n j)
      0 = some (n, gammaLen n) := by
  unfold decodeGamma?
  exact decodeGammaAux_gammaBit n

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
  calc
    readNatBE (encodeTreeMCSPPrefixFields codec fields) 0 tagLen =
        readNatBE (natBEField treePrefixTag tagLen) 0 tagLen := by
      apply readNatBE_eq_of_readBit_eq
      intro t ht
      unfold readBit? natBEField
      have hm : t < treeMCSPPrefixM codec fields.n := by
        have ht8 : t < 8 := by simpa [tagLen] using ht
        unfold treeMCSPPrefixM
        omega
      simp [hm, ht, encodeTreeMCSPPrefixFields]
    _ = some treePrefixTag := by
      exact readNatBE_natBEField_zero treePrefixTag tagLen (by norm_num [treePrefixTag, tagLen])

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
