import Pnp4.Frontier.SearchMCSPConcreteTargets
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
Concrete tree-MCSP target over the repository DAG circuit adapter `C_DAG`.

This alias fixes only the circuit class.  The threshold schedule, witness
encoding, and weak-size schedule remain explicit parameters so the eventual
lower-bound and extraction obligations cannot be hidden.
-/
def TreeMCSP_C_DAG_Target
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat) :
    SearchMCSPWeakCircuitLowerBoundTarget :=
  treeMCSPSearchWeakLowerBoundTarget
    threshold
    encoding
    C_DAG
    sizeBound

/--
Target-specific extracted language placeholder.

At this stage we keep the language explicit as a parameter; the concrete parser
and extraction theorem are recorded as separate obligations below.
-/
abbrev TreeMCSPExtractedLanguage : Type :=
  Pnp3.ComplexityInterfaces.Language

/--
Explicit target-specific packaging theorem.

Given:
- an explicit extracted language `L` in `NP`;
- an explicit extraction theorem sending `PpolyDAG L` to a bounded solver for
  the concrete tree-MCSP target;
- a proved weak lower bound (`noBoundedSolver`) for that concrete target;

we can build `VerifiedNPDAGLowerBoundSource` without using wrapper fields.
-/
theorem verifiedSource_of_treeMCSP_prefix_obligations
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (L : TreeMCSPExtractedLanguage)
    (hNP : Pnp3.ComplexityInterfaces.NP L)
    (hExtract :
      Pnp3.ComplexityInterfaces.PpolyDAG L →
        Nonempty
          (BoundedSearchSolver
            (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem
            (TreeMCSP_C_DAG_Target threshold encoding sizeBound).circuitClass
            (TreeMCSP_C_DAG_Target threshold encoding sizeBound).sizeBound))
    (hNoSolver :
      SearchProblemNoBoundedSolver
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).circuitClass
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).sizeBound) :
    VerifiedNPDAGLowerBoundSource := by
  refine
    { L := L
      inNP := hNP
      notInPpolyDAG := ?_ }
  intro hPpoly
  exact hNoSolver (hExtract hPpoly)

/--
Hard extraction obligation (statement-only): a `PpolyDAG` decider for the
extracted tree-MCSP prefix language should yield a bounded search solver for
`TreeMCSP_C_DAG_Target`.
-/
def TreeMCSPPrefixToSolverObligation
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (L : TreeMCSPExtractedLanguage) : Prop :=
  Pnp3.ComplexityInterfaces.PpolyDAG L →
    Nonempty
      (BoundedSearchSolver
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).circuitClass
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).sizeBound)

/--
Weak lower-bound obligation (statement-only): no bounded solver exists for the
concrete tree-MCSP target.
-/
def TreeMCSPNoBoundedSolverObligation
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat) : Prop :=
  SearchProblemNoBoundedSolver
    (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem
    (TreeMCSP_C_DAG_Target threshold encoding sizeBound).circuitClass
    (TreeMCSP_C_DAG_Target threshold encoding sizeBound).sizeBound

end ContractExpansion
end Frontier
end Pnp4
