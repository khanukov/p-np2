import Pnp4.Frontier.ContractExpansion.ExplicitConditionalSource
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Concrete-codec conditional verified source

Block 12f of the downstream extraction effort — instantiating the capstone
(`ExplicitConditionalSource.lean`, #1515) at the **concrete** tree-circuit codec
`treeCircuitWitnessCodec` (#1522).

The capstone `verifiedSource_of_explicit_interfaces` takes three explicit interfaces
(a `PolynomialWitnessCodec`, the open polynomial lower bound, an NP TM-witness) and
returns a `VerifiedNPDAGLowerBoundSource`.  With the concrete codec now in hand, the
`PolynomialWitnessCodec` input is provided by `treePolynomialWitnessCodec` under the
single growth premise `PolyBoundedInTable threshold` — so the codec/growth leg is no
longer an abstract `codec`, but the concrete `treeCircuitWitnessCodec threshold`.

After this brick the three remaining open inputs are, for the concrete codec:

1. `PolyBoundedInTable threshold` — an arithmetic growth hypothesis on the chosen
   threshold;
2. `NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec threshold)` — the genuine
   weak lower bound (hard, research-level mathematics);
3. `PrefixExtensionNPWitness (treeMCSPConcretePrefixParser threshold …)` — a concrete
   NP verifier TM with runtime/correctness.

Everything stays **strictly conditional**: all three are explicit hypotheses, none
proved here.

Scope discipline — concrete-codec instantiation of the conditional source only:

* the three inputs are **explicit hypotheses** — **none** proved here;
* **no** `SearchMCSPMagnificationContract` change, **no** `P ≠ NP` endpoint, **no**
  unconditional claim.
-/

/--
**Concrete-codec verified source.**  For the concrete tree-circuit codec, the three
explicit interfaces — the threshold growth hypothesis (via `treePolynomialWitnessCodec`),
the open polynomial weak lower bound, and an NP TM-witness — assemble a
`VerifiedNPDAGLowerBoundSource`.
-/
noncomputable def verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver
    (threshold : Nat → Nat)
    (hThresholdPoly : PolyBoundedInTable threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec threshold))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold (treeCircuitWitnessCodec threshold))) :
    VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_explicit_interfaces
    (treePolynomialWitnessCodec threshold hThresholdPoly) hNoPoly hNPWit

/--
Convenience wrapper: the same three concrete-codec inputs yield the conditional
`NP ⊄ PpolyDAG` separation.  Still strictly conditional; **not** the `P ≠ NP`
endpoint.
-/
theorem NP_not_subset_PpolyDAG_of_treeCodec_interfaces
    (threshold : Nat → Nat)
    (hThresholdPoly : PolyBoundedInTable threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec threshold))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold (treeCircuitWitnessCodec threshold))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_explicit_interfaces
    (treePolynomialWitnessCodec threshold hThresholdPoly) hNoPoly hNPWit

end ContractExpansion
end Frontier
end Pnp4
