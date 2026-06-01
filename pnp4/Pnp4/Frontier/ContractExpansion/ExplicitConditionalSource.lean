import Pnp4.Frontier.ContractExpansion.ConditionalVerifiedSource
import Pnp4.Frontier.ContractExpansion.WitnessGrowthReduction
import Pnp4.Frontier.ContractExpansion.PrefixExtensionNPWitness

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Explicit conditional verified-source surface

The capstone of the downstream decision→search extraction: a single clean
conditional theorem assembling a `VerifiedNPDAGLowerBoundSource` from the **three
explicit interfaces** the earlier bricks isolated, each carrying exactly one of the
genuine open inputs:

* `PolynomialWitnessCodec threshold` — the codec plus the single honest growth
  premise (`PolyBoundedInTable codec.witnessBits`), which (Block 10a) yields the full
  `TreeMCSPExtractionGrowthAssumptions`;
* `NoPolynomialBoundedSearchSolver wcodec.codec` — the open weak lower bound (Block
  9d);
* `PrefixExtensionNPWitness (treeMCSPConcretePrefixParser threshold wcodec.codec)` —
  the verifier-TM obligations that (Block 11a) yield `NP (PrefixExtensionLanguage …)`.

Chaining the three through `verifiedSource_of_noPolynomialBoundedSearchSolver`
(Block 9e) gives the source record, and thence (optionally) the `NP ⊄ PpolyDAG`
separation.

Everything is **strictly conditional**: all three inputs are explicit hypotheses,
**none proved here**.  This is purely a packaging surface — the three honest open
problems remain open.

Scope discipline — conditional packaging only:

* the growth premise, the lower bound, and the NP verifier-TM obligations are all
  **explicit hypotheses** — **none proved here**;
* **no** `SearchMCSPMagnificationContract` change, **no** `P ≠ NP` endpoint theorem,
  **no** unconditional claim.
-/

variable {threshold : Nat → Nat}

/--
**Verified source from the three explicit interfaces.**  Given a
`PolynomialWitnessCodec` (witness-growth premise), the open polynomial weak lower
bound, and a TM-witness for NP-membership of the prefix-extension language, assemble
a `VerifiedNPDAGLowerBoundSource`.

The growth assumptions come from `wcodec.toGrowthAssumptions` (Block 10a) and the
`NP`-membership from `prefixExtensionLanguage_in_NP_of_witness` (Block 11a); both feed
`verifiedSource_of_noPolynomialBoundedSearchSolver` (Block 9e).
-/
noncomputable def verifiedSource_of_explicit_interfaces
    (wcodec : PolynomialWitnessCodec threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver wcodec.codec)
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold wcodec.codec)) :
    VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_noPolynomialBoundedSearchSolver
    wcodec.codec
    wcodec.toGrowthAssumptions
    hNoPoly
    (prefixExtensionLanguage_in_NP_of_witness
      (treeMCSPConcretePrefixParser threshold wcodec.codec) hNPWit)

/--
Convenience wrapper: the same three explicit interfaces yield the conditional
`NP ⊄ PpolyDAG` separation, via the existing
`NP_not_subset_PpolyDAG_of_verified_source` bridge applied to the assembled source.

Still strictly **conditional** on all three inputs; **not** the `P ≠ NP` endpoint and
asserts nothing unconditionally.
-/
theorem NP_not_subset_PpolyDAG_of_explicit_interfaces
    (wcodec : PolynomialWitnessCodec threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver wcodec.codec)
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold wcodec.codec)) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_verified_source
    (verifiedSource_of_explicit_interfaces wcodec hNoPoly hNPWit)

end ContractExpansion
end Frontier
end Pnp4
