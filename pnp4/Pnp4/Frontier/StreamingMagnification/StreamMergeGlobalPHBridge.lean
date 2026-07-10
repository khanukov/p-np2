import Pnp4.Frontier.StreamingMagnification.FinitePHClosure
import Pnp4.Frontier.StreamingMagnification.StreamMergeRequestCodec

/-!
# Global Stream-Merge row and the repaired finite EAE projection

This module turns the self-delimiting Stream-Merge request and the three
successive certificate carriers into one actual matrix `Language`.  On a full
matrix input it deterministically recovers the unique base request length,
splits the concatenated request/choice/query/inner fields, parses the request,
and runs the padded row predicate.  Malformed total lengths and malformed
requests evaluate to `false`.

The result is a semantic equality with
`FinitePHClosure.EAEProject 64 64 64`.  It constructs no `OperationalTM` and
proves no polynomial running-time or `UniformP` membership theorem for the
global row.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeGlobalPHBridge

open Pnp3.ComplexityInterfaces
open StreamMergeCertificatePadding
open StreamMergeRequestCodec

/-! ## The unique successive-certificate total length -/

/-- Total matrix-input length after the outer, middle and inner suffixes. -/
def fullInputLength (baseLength : Nat) : Nat :=
  innerInputLength baseLength + innerCertificateLength baseLength

theorem outerCertificateLength_mono {left right : Nat}
    (h : left ≤ right) :
    outerCertificateLength left ≤ outerCertificateLength right := by
  exact certificateLength_mono_input h

theorem middleInputLength_mono {left right : Nat}
    (h : left ≤ right) :
    middleInputLength left ≤ middleInputLength right := by
  unfold middleInputLength
  exact Nat.add_le_add h (outerCertificateLength_mono h)

theorem middleCertificateLength_mono {left right : Nat}
    (h : left ≤ right) :
    middleCertificateLength left ≤ middleCertificateLength right := by
  exact certificateLength_mono_input (middleInputLength_mono h)

theorem innerInputLength_mono {left right : Nat}
    (h : left ≤ right) :
    innerInputLength left ≤ innerInputLength right := by
  unfold innerInputLength
  exact Nat.add_le_add (middleInputLength_mono h)
    (middleCertificateLength_mono h)

theorem innerCertificateLength_mono {left right : Nat}
    (h : left ≤ right) :
    innerCertificateLength left ≤ innerCertificateLength right := by
  exact certificateLength_mono_input (innerInputLength_mono h)

/-- The total-length schedule is strictly increasing because its first
summand already contains the strictly increasing base length. -/
theorem fullInputLength_strictMono : StrictMono fullInputLength := by
  intro left right hlt
  have hle : left ≤ right := Nat.le_of_lt hlt
  have houter : outerCertificateLength left ≤
      outerCertificateLength right := outerCertificateLength_mono hle
  have hmiddleStrict : middleInputLength left < middleInputLength right := by
    unfold middleInputLength
    omega
  have hmiddleCert : middleCertificateLength left ≤
      middleCertificateLength right := middleCertificateLength_mono hle
  have hinnerStrict : innerInputLength left < innerInputLength right := by
    unfold innerInputLength
    omega
  have hcert : innerCertificateLength left ≤
      innerCertificateLength right := innerCertificateLength_mono hle
  unfold fullInputLength
  omega

theorem fullInputLength_injective : Function.Injective fullInputLength :=
  fullInputLength_strictMono.injective

theorem baseLength_le_fullInputLength (baseLength : Nat) :
    baseLength ≤ fullInputLength baseLength := by
  unfold fullInputLength innerInputLength middleInputLength
  omega

/-! ## Executable bounded recovery of the base length -/

def baseLengthMatches (totalLength : Nat)
    (candidate : Fin (totalLength + 1)) : Bool :=
  decide (fullInputLength candidate.val = totalLength)

/-- Search all possible base lengths bounded by the total input length. -/
def recoverBaseLength? (totalLength : Nat) : Option Nat :=
  (Fin.find? (baseLengthMatches totalLength)).map Fin.val

theorem recoverBaseLength_sound {totalLength baseLength : Nat}
    (hrecover : recoverBaseLength? totalLength = some baseLength) :
    fullInputLength baseLength = totalLength := by
  unfold recoverBaseLength? at hrecover
  rcases Option.map_eq_some_iff.mp hrecover with
    ⟨candidate, hfind, hvalue⟩
  subst baseLength
  have hmatch := Fin.eq_true_of_find?_eq_some hfind
  simpa [baseLengthMatches] using hmatch

/-- Recovery is exact on every length produced by the successive-certificate
schedule. -/
@[simp] theorem recoverBaseLength_fullInputLength (baseLength : Nat) :
    recoverBaseLength? (fullInputLength baseLength) = some baseLength := by
  let candidate : Fin (fullInputLength baseLength + 1) :=
    ⟨baseLength, by
      have hle := baseLength_le_fullInputLength baseLength
      omega⟩
  have hexists :
      (Fin.find? (baseLengthMatches (fullInputLength baseLength))).isSome =
        true := by
    rw [Fin.find?_isSome_iff]
    refine ⟨candidate, ?_⟩
    simp only [baseLengthMatches, decide_eq_true_eq]
    rfl
  unfold recoverBaseLength?
  cases hfind : Fin.find?
      (baseLengthMatches (fullInputLength baseLength)) with
  | none =>
      simp [hfind] at hexists
  | some found =>
      have hmatch : fullInputLength found.val =
          fullInputLength baseLength := by
        have htrue := Fin.eq_true_of_find?_eq_some hfind
        simpa [baseLengthMatches] using htrue
      have hvalue : found.val = baseLength :=
        fullInputLength_injective hmatch
      simp [hvalue]

/-! ## Executable splitting of the concatenated matrix input -/

def leftBits {leftLength rightLength : Nat}
    (bits : Bitstring (leftLength + rightLength)) :
    Bitstring leftLength :=
  fun index => bits (Fin.castAdd rightLength index)

def rightBits {leftLength rightLength : Nat}
    (bits : Bitstring (leftLength + rightLength)) :
    Bitstring rightLength :=
  fun index => bits (Fin.natAdd leftLength index)

@[simp] theorem leftBits_concat {leftLength rightLength : Nat}
    (left : Bitstring leftLength) (right : Bitstring rightLength) :
    leftBits (concatBitstring left right) = left := by
  funext index
  simp [leftBits]

@[simp] theorem rightBits_concat {leftLength rightLength : Nat}
    (left : Bitstring leftLength) (right : Bitstring rightLength) :
    rightBits (concatBitstring left right) = right := by
  funext index
  simp [rightBits]

/-- Four fields recovered from one full matrix input at a known base length. -/
structure RowParts (baseLength : Nat) where
  request : Bitstring baseLength
  choice : PaddedChoiceWire baseLength
  query : PaddedQueryWire baseLength
  inner : PaddedInnerWire baseLength

/-- Canonical concatenation in the exact order used by `EAEProject`. -/
def packRowInput {baseLength : Nat} (request : Bitstring baseLength)
    (choice : PaddedChoiceWire baseLength)
    (query : PaddedQueryWire baseLength)
    (inner : PaddedInnerWire baseLength) :
    Bitstring (fullInputLength baseLength) :=
  concatBitstring
    (concatBitstring (concatBitstring request choice) query) inner

/-- Transport an arbitrary total-length carrier to the recovered canonical
total length. -/
def castFullInput {totalLength : Nat} (baseLength : Nat)
    (hfull : fullInputLength baseLength = totalLength)
    (bits : Bitstring totalLength) : Bitstring (fullInputLength baseLength) :=
  fun index => bits (Fin.cast hfull index)

@[simp] theorem castFullInput_rfl (baseLength : Nat)
    (bits : Bitstring (fullInputLength baseLength)) :
    castFullInput baseLength rfl bits = bits := by
  funext index
  rfl

/-- Split a full input by peeling the three appended suffixes from right to
left. -/
def unpackRowInput {totalLength : Nat} (baseLength : Nat)
    (hfull : fullInputLength baseLength = totalLength)
    (bits : Bitstring totalLength) : RowParts baseLength :=
  let full := castFullInput baseLength hfull bits
  let beforeInner := leftBits full
  let inner := rightBits full
  let beforeQuery := leftBits beforeInner
  let query := rightBits beforeInner
  let request := leftBits beforeQuery
  let choice := rightBits beforeQuery
  ⟨request, choice, query, inner⟩

@[simp] theorem unpackRowInput_packRowInput
    {baseLength : Nat} (request : Bitstring baseLength)
    (choice : PaddedChoiceWire baseLength)
    (query : PaddedQueryWire baseLength)
    (inner : PaddedInnerWire baseLength) :
    unpackRowInput baseLength rfl
        (packRowInput request choice query inner) =
      ⟨request, choice, query, inner⟩ := by
  simp [unpackRowInput, packRowInput]

@[simp] theorem unpackRowInput_packRowInput_of_proof
    {baseLength : Nat}
    (hfull : fullInputLength baseLength = fullInputLength baseLength)
    (request : Bitstring baseLength)
    (choice : PaddedChoiceWire baseLength)
    (query : PaddedQueryWire baseLength)
    (inner : PaddedInnerWire baseLength) :
    unpackRowInput baseLength hfull
        (packRowInput request choice query inner) =
      ⟨request, choice, query, inner⟩ := by
  have hproof : hfull = rfl := Subsingleton.elim _ _
  rw [hproof]
  exact unpackRowInput_packRowInput request choice query inner

/-! ## One global padded row language -/

/-- Evaluate the padded matrix after the base length has been recovered and
the four fields have been split. -/
def evaluateRowParts {baseLength : Nat} (parts : RowParts baseLength) : Bool :=
  match parseRequest parts.request with
  | none => false
  | some request =>
      decide
        (PaddedOutputBitMatrix request.n_le_ambient request.s_le_ambient
          request.1.prior request.1.blockList request.1.windowWellFormed
          request.1.position parts.choice parts.query parts.inner)

theorem evaluateRowParts_rejects_parse_failure
    {baseLength : Nat} {parts : RowParts baseLength}
    (hparse : parseRequest parts.request = none) :
    evaluateRowParts parts = false := by
  simp [evaluateRowParts, hparse]

theorem evaluateRowParts_eq_true_iff_of_parse
    {baseLength : Nat} {parts : RowParts baseLength}
    {request : ParsedRequest baseLength}
    (hparse : parseRequest parts.request = some request) :
    evaluateRowParts parts = true ↔
      PaddedOutputBitMatrix request.n_le_ambient request.s_le_ambient
        request.1.prior request.1.blockList request.1.windowWellFormed
        request.1.position parts.choice parts.query parts.inner := by
  simp [evaluateRowParts, hparse]

/--
One executable global row.  Total lengths outside the successive-certificate
schedule, failed proof rechecks, and malformed request prefixes all map to
`false`.
-/
def GlobalPaddedRowLanguage : Language :=
  fun totalLength input =>
    match recoverBaseLength? totalLength with
    | none => false
    | some baseLength =>
        if hfull : fullInputLength baseLength = totalLength then
          evaluateRowParts (unpackRowInput baseLength hfull input)
        else
          false

theorem globalPaddedRowLanguage_rejects_unrecoverable_length
    {totalLength : Nat} {input : Bitstring totalLength}
    (hrecover : recoverBaseLength? totalLength = none) :
    GlobalPaddedRowLanguage totalLength input = false := by
  simp [GlobalPaddedRowLanguage, hrecover]

/-- On a canonical concatenation the global row is exactly the padded fixed
row, with no additional semantic condition. -/
theorem globalPaddedRowLanguage_pack_eq_true_iff_of_parse
    {baseLength : Nat} {requestBits : Bitstring baseLength}
    {request : ParsedRequest baseLength}
    (hparse : parseRequest requestBits = some request)
    (choice : PaddedChoiceWire baseLength)
    (query : PaddedQueryWire baseLength)
    (inner : PaddedInnerWire baseLength) :
    GlobalPaddedRowLanguage (fullInputLength baseLength)
        (packRowInput requestBits choice query inner) = true ↔
      PaddedOutputBitMatrix request.n_le_ambient request.s_le_ambient
        request.1.prior request.1.blockList request.1.windowWellFormed
        request.1.position choice query inner := by
  simp [GlobalPaddedRowLanguage, evaluateRowParts, hparse]

theorem globalPaddedRowLanguage_pack_rejects_parse_failure
    {baseLength : Nat} {requestBits : Bitstring baseLength}
    (hparse : parseRequest requestBits = none)
    (choice : PaddedChoiceWire baseLength)
    (query : PaddedQueryWire baseLength)
    (inner : PaddedInnerWire baseLength) :
    GlobalPaddedRowLanguage (fullInputLength baseLength)
        (packRowInput requestBits choice query inner) = false := by
  simp [GlobalPaddedRowLanguage, evaluateRowParts, hparse]

/-! ## Exact finite EAE projection -/

/-- Unfolding the three generic projections produces exactly the three padded
carriers and the canonical four-field concatenation. -/
theorem eaeProject_eq_true_iff_packed_rows
    (baseLength : Nat) (requestBits : Bitstring baseLength) :
    FinitePHClosure.EAEProject 64 64 64 GlobalPaddedRowLanguage
        baseLength requestBits = true ↔
      Exists fun choice : PaddedChoiceWire baseLength =>
        forall query : PaddedQueryWire baseLength,
          Exists fun inner : PaddedInnerWire baseLength =>
            GlobalPaddedRowLanguage (fullInputLength baseLength)
              (packRowInput requestBits choice query inner) = true := by
  unfold FinitePHClosure.EAEProject
  simp only [FinitePHClosure.existsProject_eq_true_iff,
    FinitePHClosure.forallProject_eq_true_iff]
  rfl

/-- The projected global row is exactly the request codec's deterministic
global padded shell, including malformed-input rejection. -/
theorem eaeProject_eq_true_iff_globalPaddedEAEShell
    (baseLength : Nat) (requestBits : Bitstring baseLength) :
    FinitePHClosure.EAEProject 64 64 64 GlobalPaddedRowLanguage
        baseLength requestBits = true ↔
      GlobalPaddedEAEShell baseLength requestBits := by
  rw [eaeProject_eq_true_iff_packed_rows]
  cases hparse : parseRequest requestBits with
  | none =>
      simp [GlobalPaddedEAEShell, hparse,
        globalPaddedRowLanguage_pack_rejects_parse_failure hparse]
  | some request =>
      simp only [GlobalPaddedEAEShell, hparse]
      unfold PaddedCertificateEAEShell
      simp_rw [globalPaddedRowLanguage_pack_eq_true_iff_of_parse hparse]

/-- Pointwise semantic bridge from the actual output-bit language to one
generic repaired-model EAE projection over the global row. -/
theorem outputBitLanguage_eq_true_iff_eaeProject
    (baseLength : Nat) (requestBits : Bitstring baseLength) :
    OutputBitLanguage baseLength requestBits = true ↔
      FinitePHClosure.EAEProject 64 64 64 GlobalPaddedRowLanguage
        baseLength requestBits = true := by
  exact
    (outputBitLanguage_eq_true_iff_globalPaddedEAEShell
      baseLength requestBits).trans
      (eaeProject_eq_true_iff_globalPaddedEAEShell
        baseLength requestBits).symm

/-- Language equality, not merely a fixed-slice equivalence. -/
theorem outputBitLanguage_eq_eaeProject :
    OutputBitLanguage =
      FinitePHClosure.EAEProject 64 64 64 GlobalPaddedRowLanguage := by
  funext baseLength requestBits
  apply Bool.eq_iff_iff.mpr
  exact outputBitLanguage_eq_true_iff_eaeProject baseLength requestBits

/-! ## Explicit conditional operational closure -/

/-- If the one real global row has an operational uniform decider, equality of
the repaired deterministic and nondeterministic predicates collapses its EAE
projection back to `UniformP`.  Both still-open premises remain explicit. -/
theorem outputBitLanguage_in_uniformP_of_row_and_class_eq
    (hrow : OperationalUniformity.UniformP GlobalPaddedRowLanguage)
    (hclasses : OperationalUniformity.UniformP =
      OperationalUniformity.UniformNP) :
    OperationalUniformity.UniformP OutputBitLanguage := by
  rw [outputBitLanguage_eq_eaeProject]
  exact FinitePHClosure.uniformP_eaeProject_of_class_eq hclasses hrow

/-- Canonically numbered row machines give the same conditional conclusion
through the proved canonical-to-operational bridge. -/
theorem outputBitLanguage_in_uniformP_of_canonicalRow_and_class_eq
    (hrow : OperationalUniformity.CanonicalUniformP GlobalPaddedRowLanguage)
    (hclasses : OperationalUniformity.UniformP =
      OperationalUniformity.UniformNP) :
    OperationalUniformity.UniformP OutputBitLanguage :=
  outputBitLanguage_in_uniformP_of_row_and_class_eq
    (OperationalUniformity.canonicalUniformP_subset_uniformP hrow) hclasses

end StreamMergeGlobalPHBridge
end StreamingMagnification
end Frontier
end Pnp4
