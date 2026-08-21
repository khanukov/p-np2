import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding

/-!
# Classical conditional transport from prefix extendability to padded content acceptance

This module isolates the only padding-related public theorem whose statement necessarily inherits
`Classical.choice`: `ContentAccepts_padWord_of_prefixExtendable` mentions the pre-existing
noncomputable `Pnp3.ComplexityInterfaces.concatBitstring`.  Keeping it here leaves
`ContentPrefixExtensionPadding.lean` axiom-light.

The proof derives `ContentPrefixExtendable` directly from the proposition-level coincidence theorem
`ContentPrefixExtendable_iff_of_parse`; it does not route through either noncomputable Boolean
language wrapper.  Thus the measured `Classical.choice` dependency comes from `concatBitstring`,
not from `ContentPrefixExtensionLanguage` or `PrefixExtensionLanguage`.

This is a **conditional existential**, available only under `hparse`, `hn`, `hext`, and `hT`.
It is not the unconditional satisfiability or non-emptiness result; GATE-0 supplies concrete
`ContentAccepts` non-vacuity separately in `ContentPrefixExtensionNonVacuity.lean`.

**Progress classification (AGENTS.md): Infrastructure** — dependency isolation only; no source
obligation is reduced and no separation is proved.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

noncomputable section

variable {threshold : Nat → Nat}

/-- **Conditional acceptance transport.**  *If* a query at its convention length parses and is
prefix-extendable, *then* some certificate makes the concatenation content-accepted, and — by padding
stability — it stays accepted at every larger physical length.  The statement carries **four**
explicit hypotheses: `hparse`, `hn : input.n = n`, `hext`, and the padding bound `hT`; none of the
first three is discharged here. -/
theorem ContentAccepts_padWord_of_prefixExtendable
    (codec : TreeCircuitWitnessCodec threshold)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input)
    (hn : input.n = n)
    (hext : PrefixExtendable (treeMCSPConcretePrefixParser threshold codec) y)
    {T : Nat}
    (hT : treeMCSPPrefixM codec n
        + Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1 ≤ T) :
    ∃ cert : Pnp3.ComplexityInterfaces.Bitstring
        (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1),
      ContentAccepts codec
        (padWord (Pnp3.ComplexityInterfaces.concatBitstring y cert) T) := by
  have hcontent : ContentPrefixExtendable codec y :=
    (ContentPrefixExtendable_iff_of_parse codec y input hparse hn).mpr hext
  obtain ⟨cert, hacc⟩ := hcontent
  exact ⟨cert, (ContentAccepts_padWord_of_le codec _ hT).mpr hacc⟩

end
end ContractExpansion
end Frontier
end Pnp4
