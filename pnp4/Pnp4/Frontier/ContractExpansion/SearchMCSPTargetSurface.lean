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
Concrete extracted language for tree-MCSP via the staged prefix parser surface.

This binds the language to `PrefixExtensionLanguage` using parser data supplied
through `TreeMCSPPrefixParserObligations`.  No lower-bound or extraction theorem
is assumed here; this is purely the concrete language definition layer.
-/
noncomputable def TreeMCSPPrefixExtractedLanguage
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding) :
    Pnp3.ComplexityInterfaces.Language :=
  PrefixExtensionLanguage obligations.parser

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

/--
Concrete extraction obligation for the bound prefix language.

This is the target-specific R1-C-style statement: if the concrete extracted
prefix language lands in `PpolyDAG`, then the corresponding bounded solver
exists for `TreeMCSP_C_DAG_Target`.
-/
def TreeMCSPConcretePrefixToSolverObligation
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding) : Prop :=
  Pnp3.ComplexityInterfaces.PpolyDAG
      (TreeMCSPPrefixExtractedLanguage threshold encoding obligations) →
    Nonempty
      (BoundedSearchSolver
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).circuitClass
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).sizeBound)

/--
Concrete NP obligation for the bound prefix language.

This surfaces the missing R1-B obligation in target-specific form, without
claiming it is already proved.
-/
def TreeMCSPConcretePrefixNPObligation
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding) : Prop :=
  Pnp3.ComplexityInterfaces.NP
    (TreeMCSPPrefixExtractedLanguage threshold encoding obligations)

/--
Target-specific packaging theorem over the concrete prefix language alias.

This theorem does not prove `hNP`, `hExtract`, or `hNoSolver`; it only composes
those explicit obligations through the L0 packaging lemma.
-/
theorem verifiedSource_of_treeMCSP_concrete_prefix_obligations
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (hNP : TreeMCSPConcretePrefixNPObligation threshold encoding obligations)
    (hExtract :
      TreeMCSPConcretePrefixToSolverObligation
        threshold encoding sizeBound obligations)
    (hNoSolver :
      TreeMCSPNoBoundedSolverObligation threshold encoding sizeBound) :
    VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_treeMCSP_prefix_obligations
    threshold
    encoding
    sizeBound
    (TreeMCSPPrefixExtractedLanguage threshold encoding obligations)
    hNP
    hExtract
    hNoSolver

end ContractExpansion
end Frontier
end Pnp4
