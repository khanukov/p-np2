import Pnp4.Frontier.ContractExpansion.ContentVirtualZeroTailReaderCore
import Pnp4.Frontier.ContractExpansion.ContentCappedSizes
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixExplicitCap

/-!
# Bounded content parser and acceptance-preserving semantic checker (Part A G0-B2c)

This module assembles the G0-B2a source-indexed virtual-zero-tail parser and the
G0-B2b exact capped content sizes into one closed bounded content parser, and
proves that the resulting Boolean checker agrees exactly with the authoritative
`contentSemanticAccepts`.

The public parser computes its cap from the physical source length only:
`boundedContentCap k N = N ^ contentCapExponent k + contentCapExponent k`.  It
first decodes the exact physical-length content header through the virtual
reader, and only then runs `computeContentSizesCapped` at that cap.  A
successful size computation supplies an exact logical length `sizes.M`; the
source-indexed virtual strict parser is invoked at that `sizes.M`, never at the
physical length and never at the cap.  Its result is transported, in proof
only, to the authoritative dependent Sigma index using the `M_eq` field of
`ContentSizes.Exact`.

The parser is intentionally not claimed equal to `contentInput?` on every
input: a word can parse above the accepting-window cap and subsequently fail a
semantic check.  Instead, `boundedContentInput?_eq_some_iff` says exactly that
the bounded parser is the cap-filtered authoritative parser.  The copied
Boolean post-check is nevertheless equal to the authoritative semantic result,
because `contentSemanticAccepts_header_target_explicit` rules out precisely
that overflow branch whenever the authoritative result is `true`.

Imports: the reader core and the capped sizes supply the executable pieces; the
explicit-cap module supplies `contentCapExponent`, `contentSemanticAccepts`
(transitively) and the accepting-window cap theorem used for the Boolean
equality.

**Scope.**  This is semantic glue between source-level executables.  The
executable checker may call the authoritative `contentWitness`,
`prefixAgreesBool` and `verifiesBool`; no fixed `UniformTM`, no tape layout and
no runtime bound is constructed or claimed here.  There is no caller-supplied
cap, advice or content provider.

**Progress classification:** Infrastructure.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- The concrete codec used throughout this slice. -/
abbrev boundedContentCodec (k : Nat) :
    TreeCircuitWitnessCodec (thresholdPoly k) :=
  treeCircuitWitnessCodec (thresholdPoly k)

/-- Exactly the dependent result type returned by authoritative `contentInput?`. -/
abbrev BoundedContentInputResult (k : Nat) :=
  Σ n' : Nat,
    PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (boundedContentCodec k)))
      (treeMCSPPrefixM (boundedContentCodec k) n')

/-- The closed accepting-window cap; there is no caller-supplied advice. -/
def boundedContentCap (k N : Nat) : Nat :=
  N ^ contentCapExponent k + contentCapExponent k

theorem boundedContentCap_pos (k N : Nat) : 0 < boundedContentCap k N := by
  unfold boundedContentCap contentCapExponent
  omega

/-!
## The internal parser

The transport along the exact-length equation is isolated in a proof-only cast,
so the executable parser body contains exactly one call of the virtual parser,
at the value-level target `T := sizes.M`.
-/

/-- Proof-only transport of a parsed input along an equality of logical lengths. -/
private def transportPrefixInput
    {problem : SearchMCSPCompressionProblem} {T T' : Nat}
    (h : T = T') (input : PrefixInput problem T) : PrefixInput problem T' :=
  h ▸ input

/--
Run the source-indexed virtual strict parser at logical length `T` and
transport the result into the authoritative Sigma index.  `T` is the only
value-level target; `hT` is erased.
-/
private def boundedContentTransportParse (k : Nat) {N : Nat}
    (z : PrefixBitVec N) (nHeader T : Nat)
    (hT : T = treeMCSPPrefixM (boundedContentCodec k) nHeader) :
    Option (BoundedContentInputResult k) :=
  match VirtualZeroTailReader.parseTreeMCSPPrefixInput
      (thresholdPoly k) (boundedContentCodec k) z T with
  | none => none
  | some input => some ⟨nHeader, transportPrefixInput hT input⟩

/-- The transported virtual parse is the frozen parse on `padWord z T`. -/
private theorem boundedContentTransportParse_eq (k : Nat) {N : Nat}
    (z : PrefixBitVec N) (nHeader T : Nat)
    (hT : T = treeMCSPPrefixM (boundedContentCodec k) nHeader) :
    boundedContentTransportParse k z nHeader T hT =
      (parseTreeMCSPPrefixInput (thresholdPoly k) (boundedContentCodec k)
        (padWord z (treeMCSPPrefixM (boundedContentCodec k) nHeader))).map
        (fun input => ⟨nHeader, input⟩) := by
  subst hT
  unfold boundedContentTransportParse
  rw [VirtualZeroTailReader.parseTreeMCSPPrefixInput_eq_padWord]
  cases parseTreeMCSPPrefixInput (thresholdPoly k) (boundedContentCodec k)
      (padWord z (treeMCSPPrefixM (boundedContentCodec k) nHeader)) with
  | none => rfl
  | some input => rfl

/--
Internal parser after a successful physical header.  Its cap is supplied only
by the closed public wrapper below.  The certified capped size computation
either overflows (strictly above `B` at the authoritative convention length)
or returns the exact record; the virtual parser is then run at `sizes.M`.
-/
private def boundedContentInputAfterHeaderWithCap? (k B : Nat) {N : Nat}
    (z : PrefixBitVec N) (nHeader : Nat) :
    Option (BoundedContentInputResult k) :=
  match hsizes : computeContentSizesCapped k B nHeader with
  | none => none
  | some sizes =>
      boundedContentTransportParse k z nHeader sizes.M
        ((computeContentSizesCapped_eq_some_iff k B nHeader sizes).mp hsizes).1.M_eq

/-- Strict overflow of the cap at the header target rejects before any strict read. -/
private theorem boundedContentInputAfterHeaderWithCap?_eq_none_of_lt
    (k B : Nat) {N : Nat} (z : PrefixBitVec N) (nHeader : Nat)
    (hover : B < treeMCSPPrefixM (boundedContentCodec k) nHeader) :
    boundedContentInputAfterHeaderWithCap? k B z nHeader = none := by
  have hsizes : computeContentSizesCapped k B nHeader = none :=
    (computeContentSizesCapped_eq_none_iff k B nHeader).2 hover
  unfold boundedContentInputAfterHeaderWithCap?
  split
  · rfl
  · rename_i sizes hsome
    rw [hsizes] at hsome
    exact Option.noConfusion hsome

/-- Under the cap, the internal parser is the frozen parse at the exact header target. -/
private theorem boundedContentInputAfterHeaderWithCap?_eq_of_le
    (k B : Nat) {N : Nat} (z : PrefixBitVec N) (nHeader : Nat)
    (htarget : treeMCSPPrefixM (boundedContentCodec k) nHeader ≤ B) :
    boundedContentInputAfterHeaderWithCap? k B z nHeader =
      (parseTreeMCSPPrefixInput (thresholdPoly k) (boundedContentCodec k)
        (padWord z (treeMCSPPrefixM (boundedContentCodec k) nHeader))).map
        (fun input => ⟨nHeader, input⟩) := by
  unfold boundedContentInputAfterHeaderWithCap?
  split
  · rename_i hnone
    have hover := (computeContentSizesCapped_eq_none_iff k B nHeader).1 hnone
    exact absurd htarget (Nat.not_le_of_lt hover)
  · rename_i sizes hsome
    exact boundedContentTransportParse_eq k z nHeader sizes.M _

/--
Closed public bounded content parser.  The header is decoded by the
source-indexed virtual reader at the exact physical-length window `2 * N + 1`;
the match forces that header before the cap expression is demanded, so a
malformed header does not first compute `N ^ contentCapExponent k`.
-/
def boundedContentInput? (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    Option (BoundedContentInputResult k) :=
  match VirtualZeroTailReader.contentHeader? z with
  | none => none
  | some (nHeader, _consumed) =>
      boundedContentInputAfterHeaderWithCap?
        k (boundedContentCap k N) z nHeader

/-!
## Exact cap-filter characterization

This lower-level theorem exposes the whole semantic difference between the two
parsers.  It is also the transport proof: the virtual parser theorem identifies
the source-indexed parse at exact `sizes.M` with the frozen parse on
`padWord z (treeMCSPPrefixM codec nHeader)`.
-/

theorem boundedContentInput?_eq_filter
    (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    boundedContentInput? k z =
      match contentInput? (boundedContentCodec k) z with
      | none => none
      | some pr =>
          if treeMCSPPrefixM (boundedContentCodec k) pr.1 ≤
              boundedContentCap k N then
            some pr
          else
            none := by
  unfold boundedContentInput? contentInput?
  rw [VirtualZeroTailReader.contentHeader?_eq]
  cases hheader : contentHeader? z with
  | none => rfl
  | some header =>
      rcases header with ⟨nHeader, consumed⟩
      dsimp only
      by_cases htarget :
          treeMCSPPrefixM (boundedContentCodec k) nHeader ≤
            boundedContentCap k N
      · rw [boundedContentInputAfterHeaderWithCap?_eq_of_le
          k (boundedContentCap k N) z nHeader htarget]
        cases hparse :
            parseTreeMCSPPrefixInput (thresholdPoly k) (boundedContentCodec k)
              (padWord z (treeMCSPPrefixM (boundedContentCodec k) nHeader)) with
        | none => rfl
        | some input => simp [htarget]
      · have hover :
            boundedContentCap k N <
              treeMCSPPrefixM (boundedContentCodec k) nHeader :=
          Nat.lt_of_not_le htarget
        rw [boundedContentInputAfterHeaderWithCap?_eq_none_of_lt
          k (boundedContentCap k N) z nHeader hover]
        cases hparse :
            parseTreeMCSPPrefixInput (thresholdPoly k) (boundedContentCodec k)
              (padWord z (treeMCSPPrefixM (boundedContentCodec k) nHeader)) with
        | none => rfl
        | some input => simp [htarget]

/-- Strongest true parser interface: soundness and cap completeness in one statement. -/
theorem boundedContentInput?_eq_some_iff
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (pr : BoundedContentInputResult k) :
    boundedContentInput? k z = some pr ↔
      contentInput? (boundedContentCodec k) z = some pr ∧
      treeMCSPPrefixM (boundedContentCodec k) pr.1 ≤
        boundedContentCap k N := by
  rw [boundedContentInput?_eq_filter]
  cases hinput : contentInput? (boundedContentCodec k) z with
  | none => simp
  | some parsed =>
      dsimp only
      by_cases hcap :
          treeMCSPPrefixM (boundedContentCodec k) parsed.1 ≤
            boundedContentCap k N
      · rw [if_pos hcap]
        constructor
        · intro h
          refine ⟨h, ?_⟩
          cases h
          exact hcap
        · intro h
          exact h.1
      · rw [if_neg hcap]
        constructor
        · intro h
          cases h
        · rintro ⟨h, hle⟩
          cases h
          exact absurd hle hcap

/-- Every bounded-parser success is an identical authoritative-parser success. -/
theorem boundedContentInput?_sound
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : BoundedContentInputResult k}
    (h : boundedContentInput? k z = some pr) :
    contentInput? (boundedContentCodec k) z = some pr :=
  ((boundedContentInput?_eq_some_iff k z pr).mp h).1

/-- Every bounded-parser success carries the exact closed target bound. -/
theorem boundedContentInput?_target_le
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : BoundedContentInputResult k}
    (h : boundedContentInput? k z = some pr) :
    treeMCSPPrefixM (boundedContentCodec k) pr.1 ≤
      boundedContentCap k N :=
  ((boundedContentInput?_eq_some_iff k z pr).mp h).2

/-- Authoritative parsing is reproduced whenever its outer target lies under the cap. -/
theorem boundedContentInput?_complete_of_target_le
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : BoundedContentInputResult k}
    (hinput : contentInput? (boundedContentCodec k) z = some pr)
    (htarget : treeMCSPPrefixM (boundedContentCodec k) pr.1 ≤
      boundedContentCap k N) :
    boundedContentInput? k z = some pr :=
  (boundedContentInput?_eq_some_iff k z pr).2 ⟨hinput, htarget⟩

/-- Every bounded-parser success has a successful exact capped size computation
at its outer index, returning the canonical record. -/
theorem boundedContentInput?_computeContentSizesCapped_eq_some
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : BoundedContentInputResult k}
    (h : boundedContentInput? k z = some pr) :
    computeContentSizesCapped k (boundedContentCap k N) pr.1 =
      some (exactContentSizes k pr.1) :=
  (computeContentSizesCapped_eq_some_iff
    k (boundedContentCap k N) pr.1 (exactContentSizes k pr.1)).2
    ⟨exactContentSizes_exact k pr.1, boundedContentInput?_target_le k z h⟩

/-- An explicit header-target overflow makes the bounded parser reject before strict parsing. -/
theorem boundedContentInput?_eq_none_of_boundedContentCap_lt
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (nHeader consumed : Nat)
    (hheader : contentHeader? z = some (nHeader, consumed))
    (hoverflow : boundedContentCap k N <
      treeMCSPPrefixM (boundedContentCodec k) nHeader) :
    boundedContentInput? k z = none := by
  unfold boundedContentInput?
  rw [VirtualZeroTailReader.contentHeader?_eq, hheader]
  exact boundedContentInputAfterHeaderWithCap?_eq_none_of_lt
    k (boundedContentCap k N) z nHeader hoverflow

/-- Equality under the exact physical header and its accepting-window bound. -/
theorem boundedContentInput?_eq_contentInput_of_header_target_le
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (nHeader consumed : Nat)
    (hheader : contentHeader? z = some (nHeader, consumed))
    (htarget : treeMCSPPrefixM (boundedContentCodec k) nHeader ≤
      boundedContentCap k N) :
    boundedContentInput? k z = contentInput? (boundedContentCodec k) z := by
  rw [boundedContentInput?_eq_filter]
  unfold contentInput?
  rw [hheader]
  cases hparse :
      parseTreeMCSPPrefixInput (thresholdPoly k) (boundedContentCodec k)
        (padWord z (treeMCSPPrefixM (boundedContentCodec k) nHeader)) with
  | none => simp [hparse]
  | some input => simp [hparse, htarget]

/-!
## The acceptance-preserving Boolean interface
-/

/--
Executable bounded semantic checker.  The post-parse expression is copied
literally from `contentSemanticAccepts`; that authoritative executable is not
called here.
-/
def boundedContentSemanticAccepts (k : Nat) {N : Nat}
    (z : PrefixBitVec N) : Bool :=
  match boundedContentInput? k z with
  | none => false
  | some pr =>
      let w := contentWitness (boundedContentCodec k) z pr.2.n
      prefixAgreesBool pr.2 w &&
        verifiesBool (boundedContentCodec k) pr.2.n pr.2.x w

/--
The cap theorem for the physical header, specialized to the outer Sigma index
of one authoritative success.  This avoids conflating `pr.1` with the parsed
field `pr.2.n`.
-/
theorem contentSemanticAccepts_successful_outer_target_explicit
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : BoundedContentInputResult k}
    (hinput : contentInput? (boundedContentCodec k) z = some pr)
    (hsemantic : contentSemanticAccepts (boundedContentCodec k) z = true) :
    treeMCSPPrefixM (boundedContentCodec k) pr.1 ≤
      boundedContentCap k N := by
  cases hheader : contentHeader? z with
  | none =>
      unfold contentInput? at hinput
      rw [hheader] at hinput
      simp at hinput
  | some header =>
      rcases header with ⟨nHeader, consumed⟩
      have hbound :=
        contentSemanticAccepts_header_target_explicit
          k z nHeader consumed hheader hsemantic
      unfold contentInput? at hinput
      rw [hheader] at hinput
      cases hparse :
          parseTreeMCSPPrefixInput (thresholdPoly k) (boundedContentCodec k)
            (padWord z (treeMCSPPrefixM (boundedContentCodec k) nHeader)) with
      | none => simp [hparse] at hinput
      | some input =>
          simp only [hparse, Option.map_some] at hinput
          cases hinput
          simpa [boundedContentCap] using hbound

/--
An explicit header-target overflow forces authoritative semantic rejection.
The contradiction uses only the merged accepting-window cap theorem; it does
not assert that authoritative parsing itself failed.
-/
theorem contentSemanticAccepts_eq_false_of_boundedContentCap_lt
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (nHeader consumed : Nat)
    (hheader : contentHeader? z = some (nHeader, consumed))
    (hoverflow : boundedContentCap k N <
      treeMCSPPrefixM (boundedContentCodec k) nHeader) :
    contentSemanticAccepts (boundedContentCodec k) z = false := by
  cases hsemantic : contentSemanticAccepts (boundedContentCodec k) z with
  | false => rfl
  | true =>
      have hbound :
          treeMCSPPrefixM (boundedContentCodec k) nHeader ≤
            N ^ contentCapExponent k + contentCapExponent k :=
        contentSemanticAccepts_header_target_explicit
          k z nHeader consumed hheader hsemantic
      unfold boundedContentCap at hoverflow
      omega

/-- The bounded checker rejects the same explicit overflow before strict parsing. -/
theorem boundedContentSemanticAccepts_eq_false_of_boundedContentCap_lt
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (nHeader consumed : Nat)
    (hheader : contentHeader? z = some (nHeader, consumed))
    (hoverflow : boundedContentCap k N <
      treeMCSPPrefixM (boundedContentCodec k) nHeader) :
    boundedContentSemanticAccepts k z = false := by
  have hinput : boundedContentInput? k z = none :=
    boundedContentInput?_eq_none_of_boundedContentCap_lt
      k z nHeader consumed hheader hoverflow
  simp [boundedContentSemanticAccepts, hinput]

/--
The bounded and authoritative Boolean checkers have identical accepting
branches.  In the right-to-left direction, the only exclusion of cap overflow
is the explicit accepting-window theorem above.
-/
theorem boundedContentSemanticAccepts_eq_true_iff
    (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    boundedContentSemanticAccepts k z = true ↔
      contentSemanticAccepts (boundedContentCodec k) z = true := by
  constructor
  · intro hbounded
    cases hparse : boundedContentInput? k z with
    | none => simp [boundedContentSemanticAccepts, hparse] at hbounded
    | some pr =>
        have hauthoritative := boundedContentInput?_sound k z hparse
        simpa [boundedContentSemanticAccepts, hparse,
          contentSemanticAccepts, hauthoritative] using hbounded
  · intro hauthoritative
    cases hinput : contentInput? (boundedContentCodec k) z with
    | none => simp [contentSemanticAccepts, hinput] at hauthoritative
    | some pr =>
        have htarget :=
          contentSemanticAccepts_successful_outer_target_explicit
            k z hinput hauthoritative
        have hboundedInput : boundedContentInput? k z = some pr :=
          boundedContentInput?_complete_of_target_le
            k z hinput htarget
        simpa [boundedContentSemanticAccepts, hboundedInput,
          contentSemanticAccepts, hinput] using hauthoritative

/-- Boolean equality, derived from equality of both accepting branches. -/
theorem boundedContentSemanticAccepts_eq
    (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    boundedContentSemanticAccepts k z =
      contentSemanticAccepts (boundedContentCodec k) z := by
  apply Bool.eq_iff_iff.mpr
  exact boundedContentSemanticAccepts_eq_true_iff k z

/-- Explicit rejecting-branch preservation. -/
theorem boundedContentSemanticAccepts_eq_false_iff
    (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    boundedContentSemanticAccepts k z = false ↔
      contentSemanticAccepts (boundedContentCodec k) z = false := by
  rw [boundedContentSemanticAccepts_eq]

/-- On semantic acceptance, the requested parser equality is valid. -/
theorem boundedContentInput?_eq_contentInput_of_semantic_true
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (hsemantic : contentSemanticAccepts (boundedContentCodec k) z = true) :
    boundedContentInput? k z = contentInput? (boundedContentCodec k) z := by
  cases hinput : contentInput? (boundedContentCodec k) z with
  | none => simp [contentSemanticAccepts, hinput] at hsemantic
  | some pr =>
      have htarget :=
        contentSemanticAccepts_successful_outer_target_explicit
          k z hinput hsemantic
      rw [boundedContentInput?_eq_filter, hinput]
      simp [htarget]

/-- The bounded executable still decides the exact frozen content predicate. -/
theorem boundedContentSemanticAccepts_eq_true_iff_contentAccepts
    (k : Nat) {N : Nat} (z : PrefixBitVec N) :
    boundedContentSemanticAccepts k z = true ↔
      ContentAccepts (boundedContentCodec k) z := by
  rw [boundedContentSemanticAccepts_eq_true_iff]
  exact contentSemanticAccepts_eq_true_iff (boundedContentCodec k) z

end ContractExpansion
end Frontier
end Pnp4
