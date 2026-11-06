import Pnp4.Frontier.ContractExpansion.ContentPrefixExtension

/-!
# Content-indexed virtual-zero-tail reader core

This module implements the strict tree-prefix readers over a physical source
`z : PrefixBitVec N` and a separate logical length `T`.  Reads below `T` use
`padRead`, so physical positions at or beyond `N` are virtual zeroes; reads at
or beyond `T` still fail.  No `PrefixBitVec T` is constructed by these
implementations.

Each reader, and the complete parser assembled from them, is proved equal to
the frozen operation applied to `padWord z T`.  Thus the equalities include
every successful result and every failure branch.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

namespace VirtualZeroTailReader

/-- Strict logical read backed by the physical source and its virtual zero tail. -/
def readBit? {N : Nat} (z : PrefixBitVec N) (T offset : Nat) : Option Bool :=
  if _h : offset < T then some (padRead z offset) else none

/-- Exact equality with the frozen strict bit reader on the padded word. -/
@[simp] theorem readBit?_eq_padWord
    {N T : Nat} (z : PrefixBitVec N) (offset : Nat) :
    VirtualZeroTailReader.readBit? z T offset =
      _root_.Pnp4.Frontier.ContractExpansion.readBit? (padWord z T) offset := by
  unfold VirtualZeroTailReader.readBit?
    _root_.Pnp4.Frontier.ContractExpansion.readBit?
  by_cases h : offset < T
  · simp [h, padWord]
  · simp [h]

/-- Big-endian natural read; recursion is structurally bounded by `width`. -/
def readNatBE {N : Nat} (z : PrefixBitVec N) (T offset : Nat) :
    Nat → Option Nat
  | 0 => some 0
  | k + 1 => do
      let b ← readBit? z T offset
      let rest ← readNatBE z T (offset + 1) k
      some ((if b then 2 ^ k else 0) + rest)

/-- Exact equality with the frozen big-endian reader on the padded word. -/
@[simp] theorem readNatBE_eq_padWord
    {N T : Nat} (z : PrefixBitVec N) (offset width : Nat) :
    VirtualZeroTailReader.readNatBE z T offset width =
      _root_.Pnp4.Frontier.ContractExpansion.readNatBE
        (padWord z T) offset width := by
  induction width generalizing offset with
  | zero => rfl
  | succ k ih =>
      simp [VirtualZeroTailReader.readNatBE,
        _root_.Pnp4.Frontier.ContractExpansion.readNatBE, ih]

/--
Return a function-valued slice without enumerating it.  Its guard is the exact
strict logical range condition used by the frozen slice.
-/
def sliceBits? {N : Nat} (z : PrefixBitVec N) (T offset width : Nat) :
    Option (PrefixBitVec width) :=
  if _h : offset + width ≤ T then
    some (fun j => padRead z (offset + j.1))
  else
    none

/-- Exact extensional equality with the frozen slice on the padded word. -/
@[simp] theorem sliceBits?_eq_padWord
    {N T : Nat} (z : PrefixBitVec N) (offset width : Nat) :
    VirtualZeroTailReader.sliceBits? z T offset width =
      _root_.Pnp4.Frontier.ContractExpansion.sliceBits?
        (padWord z T) offset width := by
  unfold VirtualZeroTailReader.sliceBits?
    _root_.Pnp4.Frontier.ContractExpansion.sliceBits?
  by_cases h : offset + width ≤ T
  · simp [h, padWord]
  · simp [h]

/--
All-zero scan; recursion is bounded by `width` and range failures remain
failures.  As in the frozen recursive operation, width zero returns `some true`
at every offset; positive widths perform strict reads.
-/
def allZeroSlice? {N : Nat} (z : PrefixBitVec N) (T offset : Nat) :
    Nat → Option Bool
  | 0 => some true
  | k + 1 => do
      let b ← readBit? z T offset
      let rest ← allZeroSlice? z T (offset + 1) k
      some ((!b) && rest)

/-- Exact equality with the frozen strict all-zero scan on the padded word. -/
@[simp] theorem allZeroSlice?_eq_padWord
    {N T : Nat} (z : PrefixBitVec N) (offset width : Nat) :
    VirtualZeroTailReader.allZeroSlice? z T offset width =
      _root_.Pnp4.Frontier.ContractExpansion.allZeroSlice?
        (padWord z T) offset width := by
  induction width generalizing offset with
  | zero => rfl
  | succ k ih =>
      simp [VirtualZeroTailReader.allZeroSlice?,
        _root_.Pnp4.Frontier.ContractExpansion.allZeroSlice?, ih]

/-- Elias-gamma decoder whose only search loop is structurally bounded by `fuel`. -/
def decodeGammaAux? {N : Nat} (z : PrefixBitVec N) (T offset : Nat) :
    Nat → Nat → Option (Nat × Nat)
  | 0, _zeros => none
  | fuel + 1, zeros => do
      let b ← readBit? z T (offset + zeros)
      if b then
        let payload ← readNatBE z T (offset + zeros + 1) zeros
        let value := 2 ^ zeros + payload
        some (value - 1, 2 * zeros + 1)
      else
        decodeGammaAux? z T offset fuel (zeros + 1)

/-- Exact decoder-state equality for every fuel and zero-count state. -/
@[simp] theorem decodeGammaAux?_eq_padWord
    {N T : Nat} (z : PrefixBitVec N) (offset fuel zeros : Nat) :
    VirtualZeroTailReader.decodeGammaAux? z T offset fuel zeros =
      _root_.Pnp4.Frontier.ContractExpansion.decodeGammaAux?
        (padWord z T) offset fuel zeros := by
  induction fuel generalizing zeros with
  | zero => rfl
  | succ fuel ih =>
      simp [VirtualZeroTailReader.decodeGammaAux?,
        _root_.Pnp4.Frontier.ContractExpansion.decodeGammaAux?, ih]

/-- Prefix-search fuel supplied to public gamma decoding. -/
def gammaLoopBound (T : Nat) : Nat := T + 1

/-- Public gamma decoder with exactly `gammaLoopBound T` units of fuel. -/
def decodeGamma? {N : Nat} (z : PrefixBitVec N) (T offset : Nat) :
    Option (Nat × Nat) :=
  decodeGammaAux? z T offset (gammaLoopBound T) 0

/-- Exact equality with the frozen public decoder on the padded word. -/
@[simp] theorem decodeGamma?_eq_padWord
    {N T : Nat} (z : PrefixBitVec N) (offset : Nat) :
    VirtualZeroTailReader.decodeGamma? z T offset =
      _root_.Pnp4.Frontier.ContractExpansion.decodeGamma?
        (padWord z T) offset := by
  simp [VirtualZeroTailReader.decodeGamma?,
    VirtualZeroTailReader.gammaLoopBound,
    _root_.Pnp4.Frontier.ContractExpansion.decodeGamma?]

/-- Decode the content header with logical length exactly `2 * N + 1`. -/
def contentHeader? {N : Nat} (z : PrefixBitVec N) : Option (Nat × Nat) :=
  decodeGamma? z (2 * N + 1) tagLen

/-- The content header is the frozen gamma operation on the explicit padded word. -/
theorem contentHeader?_eq_padWord
    {N : Nat} (z : PrefixBitVec N) :
    VirtualZeroTailReader.contentHeader? z =
      _root_.Pnp4.Frontier.ContractExpansion.decodeGamma?
        (padWord z (2 * N + 1)) tagLen := by
  simpa only [VirtualZeroTailReader.contentHeader?] using
    (VirtualZeroTailReader.decodeGamma?_eq_padWord
      (T := 2 * N + 1) z tagLen)

/-- Exact equality with the frozen content-header operation. -/
@[simp] theorem contentHeader?_eq
    {N : Nat} (z : PrefixBitVec N) :
    VirtualZeroTailReader.contentHeader? z =
      _root_.Pnp4.Frontier.ContractExpansion.contentHeader? z := by
  simpa only [_root_.Pnp4.Frontier.ContractExpansion.contentHeader?] using
    (VirtualZeroTailReader.contentHeader?_eq_padWord z)

/--
The complete strict tree-prefix parser over physical source `z` and independent
logical length `T`.  Its order of reads and guards is the frozen order: tag,
gamma header, exact convention length, table, index, active prefix, inactive
padding, and the inactive-padding zero check.
-/
def parseTreeMCSPPrefixInput
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    {N : Nat} (z : PrefixBitVec N) (T : Nat) :
    Option (PrefixInput
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) T) := do
  let tag ← readNatBE z T 0 tagLen
  if _htag : tag = treePrefixTag then
    let decoded ← decodeGamma? z T tagLen
    let n := decoded.1
    let consumedGamma := decoded.2
    if _hlen : T = treeMCSPPrefixM codec n then
      let xOffset := tagLen + consumedGamma
      let x ← sliceBits? z T xOffset (Pnp3.Models.Partial.tableLen n)
      let iOffset := xOffset + Pnp3.Models.Partial.tableLen n
      let i ← readNatBE z T iOffset (idxWidth codec.witnessBits n)
      if hi : i ≤ codec.witnessBits n then
        let pOffset := iOffset + idxWidth codec.witnessBits n
        let p ← sliceBits? z T pOffset i
        let padOffset := pOffset + i
        let padWidth := codec.witnessBits n - i
        let pad ← sliceBits? z T padOffset padWidth
        let padZero ← allZeroSlice? z T padOffset padWidth
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
Exact equality with the complete frozen parser on `padWord z T`; in particular,
the equality covers all successful results and all rejection/failure branches.
-/
@[simp] theorem parseTreeMCSPPrefixInput_eq_padWord
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    {N : Nat} (z : PrefixBitVec N) (T : Nat) :
    VirtualZeroTailReader.parseTreeMCSPPrefixInput threshold codec z T =
      _root_.Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput
        threshold codec (padWord z T) := by
  simp only [VirtualZeroTailReader.parseTreeMCSPPrefixInput,
    _root_.Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput,
    VirtualZeroTailReader.readNatBE_eq_padWord,
    VirtualZeroTailReader.decodeGamma?_eq_padWord,
    VirtualZeroTailReader.sliceBits?_eq_padWord,
    VirtualZeroTailReader.allZeroSlice?_eq_padWord]

/-! Explicit syntactic loop bounds. -/

/-- Declared structural width for later `readNatBE` cost accounting. -/
def readNatBELoopBound (width : Nat) : Nat := width

/-- Declared structural width for later `allZeroSlice?` cost accounting. -/
def allZeroLoopBound (width : Nat) : Nat := width

/-- The content-header gamma loop has exactly `2 * N + 2` fuel. -/
@[simp] theorem contentHeader_gammaLoopBound (N : Nat) :
    gammaLoopBound (2 * N + 1) = 2 * N + 2 := by
  unfold gammaLoopBound
  omega

end VirtualZeroTailReader

end ContractExpansion
end Frontier
end Pnp4
