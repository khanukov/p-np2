import Pnp4.Frontier.ContractExpansion.BoundedSolverFromPpoly

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Exact-schedule no-solver contrapositive

Block 9c of the downstream decision→search extraction — the **contrapositive** of
the forward `PpolyDAG`→solver bridge (Block 9b, #1509), at the *exact extracted size
schedule*.

Block 9b showed: `PpolyDAG (PrefixExtensionLanguage …) → ∃ c, BoundedSearchSolver`
with schedule `extractedSolverSizeBound codec c`.  Contrapositively, if **no** solver
exists at any of those extracted schedules, the prefix-extension language is **not**
in `PpolyDAG`.

This is the cleanest, most faithful contrapositive: it keeps the lower-bound
hypothesis at the *exact* schedule the extraction produces, with no polynomial
reconciliation.  The no-solver hypothesis is, of course, **not proved here** — it is
the open weak lower bound; this file only relates it to a `PpolyDAG` non-membership.

Scope discipline — exact-schedule contrapositive only:

* the no-solver hypothesis `NoExtractedScheduleSolver` is an **explicit hypothesis**;
* **no** `NoPolynomialBoundedSearchSolver`, **no** growth/polynomial-schedule
  reconciliation (`extractedSolverSizeBound ≤ (instanceBits n)^d + d`);
* **no** `SearchMCSPMagnificationContract`, `VerifiedNPDAGLowerBoundSource`,
  NP-membership, endpoint, or `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/-- The exact size schedule produced by the forward extraction (Block 9b) for a
`PpolyDAG` decider of exponent `c`. -/
def extractedSolverSizeBound
    (codec : TreeCircuitWitnessCodec threshold)
    (c : Nat) (n : Nat) : Nat :=
  codec.witnessBits n *
      ((treeMCSPPrefixM codec n) ^ c + c + 2 * treeMCSPPrefixM codec n)
    + 1

/-- The exact-schedule weak lower-bound target: no bounded search solver exists at
any of the extracted schedules `extractedSolverSizeBound codec c`. -/
def NoExtractedScheduleSolver
    (codec : TreeCircuitWitnessCodec threshold) : Prop :=
  ∀ c : Nat,
    ¬ Nonempty
      (BoundedSearchSolver (treeProblem codec) C_DAG (extractedSolverSizeBound codec c))

/--
**Exact-schedule contrapositive.**  If no bounded search solver exists at any
extracted schedule, then the prefix-extension language is not in `PpolyDAG`.

Direct contrapositive of `boundedSearchSolver_of_PpolyDAG_prefixExtension` (Block
9b): a `PpolyDAG` membership would yield a solver at some extracted schedule
`extractedSolverSizeBound codec c`, contradicting the hypothesis at that `c`.
-/
theorem not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver
    (codec : TreeCircuitWitnessCodec threshold)
    (hNo : NoExtractedScheduleSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)) := by
  intro hPpoly
  obtain ⟨c, hSolver⟩ := boundedSearchSolver_of_PpolyDAG_prefixExtension codec hPpoly
  exact hNo c hSolver

end ContractExpansion
end Frontier
end Pnp4
