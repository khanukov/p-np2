import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier

/-!
# Semantic verifier for the content-truthful prefix-extension language

This module supplies the computable, `Bool`-valued semantic checker for a complete word used by
`ContentAccepts`.  It is the content-side counterpart of `treePrefixSemanticAccepts`: the parser and
witness offsets are computed from the padded contents of one complete word rather than from a
separate query and certificate.

The checker is a plain computable definition.  Its two proposition checks reuse the local,
constructive decision procedures behind `prefixAgreesBool` and `verifiesBool`; it does not use
`Classical.propDecidable`.  The correctness theorems have the standard axiom footprint inherited
from codec verification and the existing classical language wrapper, or a subset of it.

**Progress classification:** Infrastructure.  This constructs no Turing machine or runtime bound,
does not establish non-vacuity of `ContentAccepts`, and does not reduce either P-vs-NP source
obligation.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- The content-computed `Bool` verifier on a complete word: content-parse, read the content
witness window, check prefix agreement and codec verification. -/
def contentSemanticAccepts {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) : Bool :=
  match contentInput? codec z with
  | none => false
  | some pr =>
      let w := contentWitness codec z pr.2.n
      prefixAgreesBool pr.2 w && verifiesBool codec pr.2.n pr.2.x w

/-- **The Boolean verifier decides the frozen content-acceptance predicate.** -/
theorem contentSemanticAccepts_eq_true_iff {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) :
    contentSemanticAccepts codec z = true ↔ ContentAccepts codec z := by
  cases hinput : contentInput? codec z with
  | none =>
      simp [contentSemanticAccepts, ContentAccepts, hinput]
  | some pr =>
      simp only [contentSemanticAccepts, hinput, Bool.and_eq_true]
      rw [prefixAgreesBool_eq_true_iff, verifiesBool_eq_true_iff]
      unfold ContentAccepts
      constructor
      · rintro ⟨hprefix, hverifies⟩
        refine ⟨pr, hinput, hprefix, ?_⟩
        exact hverifies
      · rintro ⟨pr', hpr', hprefix, hverifies⟩
        have hpr : pr' = pr := by
          simpa [hinput] using hpr'.symm
        subst pr'
        exact ⟨hprefix, hverifies⟩

/-- A failed content parse makes the semantic verifier reject. -/
theorem contentSemanticAccepts_eq_false_of_contentInput_none {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    (h : contentInput? codec z = none) :
    contentSemanticAccepts codec z = false := by
  simp [contentSemanticAccepts, h]

/-- Blank-padding a complete word does not change the Boolean verifier result. -/
theorem contentSemanticAccepts_padWord_of_le {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) :
    contentSemanticAccepts codec (padWord z T) = contentSemanticAccepts codec z := by
  apply Bool.eq_iff_iff.mpr
  rw [contentSemanticAccepts_eq_true_iff, contentSemanticAccepts_eq_true_iff]
  exact ContentAccepts_padWord_of_le codec z hNT

/-- **Language correctness.**  The content-truthful language accepts exactly when some certificate
makes the content-side semantic verifier accept the concatenated complete word. -/
theorem contentSemanticAccepts_correct {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {m : Nat} (y : PrefixBitVec m) :
    ContentPrefixExtensionLanguage codec m y = true
      ↔ ∃ w : Pnp3.ComplexityInterfaces.Bitstring
                (Pnp3.ComplexityInterfaces.certificateLength m 1),
          contentSemanticAccepts codec
            (Pnp3.ComplexityInterfaces.concatBitstring y w) = true := by
  rw [ContentPrefixExtensionLanguage_accepts_iff]
  unfold ContentPrefixExtendable
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (contentSemanticAccepts_eq_true_iff codec _).mpr hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (contentSemanticAccepts_eq_true_iff codec _).mp hw⟩

end ContractExpansion
end Frontier
end Pnp4
