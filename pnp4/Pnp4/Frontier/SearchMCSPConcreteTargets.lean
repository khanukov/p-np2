import Pnp4.Frontier.SearchMCSPMagnification
import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP

namespace Pnp4
namespace Frontier

open AlgorithmsToLowerBounds

/--
Witness encoding interface for the concrete tree-MCSP search target.

The current repository does not yet commit to a concrete bit encoding of tree
circuits.  This interface isolates exactly what a later encoding proof must
provide: soundness and completeness for the existing proof-level
`treeMCSPPredicate`.
-/
structure TreeMCSPSearchWitnessEncoding
    (threshold : Nat → Nat) where
  witnessBits : Nat → Nat
  verifies :
    ∀ n : Nat,
      TruthTable n →
        AlgorithmsToLowerBounds.BitVec (witnessBits n) →
          Prop
  sound :
    ∀ n : Nat, ∀ tt : TruthTable n,
      ∀ w : AlgorithmsToLowerBounds.BitVec (witnessBits n),
        verifies n tt w →
          treeMCSPPredicate n (threshold n) tt
  complete :
    ∀ n : Nat, ∀ tt : TruthTable n,
      treeMCSPPredicate n (threshold n) tt →
        ∃ w : AlgorithmsToLowerBounds.BitVec (witnessBits n),
          verifies n tt w

/--
Concrete promise-search problem for tree-MCSP.

Instances are truth tables on `n` variables.  The promise says the table has a
tree circuit of size at most `threshold n`; a valid witness is an encoded proof
of that small tree circuit according to `encoding`.
-/
def treeMCSPSearchProblem
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) :
    SearchMCSPCompressionProblem where
  instanceBits := fun n => Pnp3.Models.Partial.tableLen n
  witnessBits := encoding.witnessBits
  promise := fun n tt => treeMCSPPredicate n (threshold n) tt
  relation := encoding.verifies
  totalOnPromise := encoding.complete

/--
Concrete weak lower-bound target for tree-MCSP search.

This is the first falsifiable mainline target shape: no non-uniform family from
`C`, with per-output-bit size bounded by `sizeBound n`, solves the promised
tree-MCSP search problem.
-/
def treeMCSPSearchWeakLowerBoundTarget
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (C : CircuitFamilyClass)
    (sizeBound : Nat → Nat) :
    SearchMCSPWeakCircuitLowerBoundTarget where
  problem := treeMCSPSearchProblem threshold encoding
  circuitClass := C
  sizeBound := sizeBound

/--
Named source package for the concrete tree-MCSP search magnification route.

The weak lower bound and the magnification contract remain separate: proving
the weak search lower bound is not enough unless the selected target is also
known to magnify to a verified `PpolyDAG` lower-bound source.
-/
structure TreeMCSPSearchMagnificationSource where
  threshold : Nat → Nat
  encoding : TreeMCSPSearchWitnessEncoding threshold
  circuitClass : CircuitFamilyClass
  sizeBound : Nat → Nat
  weakLowerBound :
    SearchMCSPWeakCircuitLowerBound
      (treeMCSPSearchWeakLowerBoundTarget threshold encoding circuitClass sizeBound)
  magnification :
    SearchMCSPMagnificationContract
      (treeMCSPSearchWeakLowerBoundTarget threshold encoding circuitClass sizeBound)

/-- The concrete tree-MCSP source packages into the generic weak-circuit route. -/
def TreeMCSPSearchMagnificationSource.asWeakCircuitLowerBound
    (src : TreeMCSPSearchMagnificationSource) :
    SearchMCSPWeakCircuitLowerBound
      (treeMCSPSearchWeakLowerBoundTarget
        src.threshold
        src.encoding
        src.circuitClass
        src.sizeBound) :=
  src.weakLowerBound

/-- A concrete tree-MCSP source yields the verified DAG lower-bound source. -/
def TreeMCSPSearchMagnificationSource.verifiedSource
    (src : TreeMCSPSearchMagnificationSource) :
    VerifiedNPDAGLowerBoundSource :=
  src.weakLowerBound.verifiedSource src.magnification

/-- Concrete tree-MCSP search magnification yields `NP not_subset P/poly`. -/
theorem NP_not_subset_Ppoly_of_treeMCSPSearchMagnificationSource
    (src : TreeMCSPSearchMagnificationSource) :
    NP_not_subset_Ppoly :=
  NP_not_subset_Ppoly_of_weakCircuitLowerBound
    src.weakLowerBound
    src.magnification

/-- Final consequence of a fully discharged concrete tree-MCSP source. -/
theorem P_ne_NP_of_treeMCSPSearchMagnificationSource
    (src : TreeMCSPSearchMagnificationSource) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_weakCircuitLowerBound
    src.weakLowerBound
    src.magnification

/-- Concrete tree-MCSP search magnification is accepted mainline progress. -/
def PvsNPMainlineProgress.of_treeMCSPSearchMagnificationSource
    (src : TreeMCSPSearchMagnificationSource) :
    PvsNPMainlineProgress where
  verifiedSource := src.verifiedSource

end Frontier
end Pnp4
