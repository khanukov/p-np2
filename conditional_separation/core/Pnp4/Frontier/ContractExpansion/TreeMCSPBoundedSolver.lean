import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedySolves
import Pnp4.Frontier.ContractExpansion.TreeMCSPDeciderCorrect

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# `BoundedSearchSolver` assembly from a prefix-extension decider family

Block 9 of the downstream decision→search extraction.

This packages the verified greedy machinery into the `BoundedSearchSolver`
structure that the search-MCSP magnification contract consumes.  Given a *family*
of prefix-extension deciders `dec : ∀ n, C_DAG.Family (treeMCSPPrefixM codec n)`
with two explicit hypotheses —

* **language-correctness**: each `dec n` decides `PrefixExtensionLanguage`
  (`DecidesPrefixExtensionLanguage`, #1506), and
* **size**: `C_DAG.size (dec n) ≤ decSizeBound n` —

we build a `BoundedSearchSolver (treeProblem codec) C_DAG solverSizeBound` whose

* `outputCircuit n` is the true-greedy per-bit output family `greedyTrueOutputCircuit`
  (Block 7′);
* `solves` chains `correctNextBitDecider_of_decidesLanguage` (8b) →
  `greedyTrueOutputCircuit_solves` (8c);
* `size_le` uses the uniform bound `size_greedyTrueOutputCircuit_le` (7′), so
  `solverSizeBound n = witnessBits n · (decSizeBound n + 2·M(n)) + 1`.

This is the first object that lives on the `SearchMCSPMagnification` side, but it is
still **honestly conditional**: it takes the decider family and its correctness/size
as explicit hypotheses.  It does *not* construct such a decider, invoke the
magnification contrapositive, or assert any lower bound.

Scope discipline — solver assembly only:

* the prefix-extension decider family + its language-correctness + size are
  **explicit hypotheses**;
* **no** `PpolyDAG`/`InPpolyDAG` bridge or decider construction;
* **no** `SearchProblemNoBoundedSolver` / contrapositive, endpoint, or
  `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/-- The solver size schedule realized by the true-greedy circuits over a decider
family bounded by `decSizeBound`. -/
def boundedSolverSizeBound
    (codec : TreeCircuitWitnessCodec threshold)
    (decSizeBound : Nat → Nat) (n : Nat) : Nat :=
  codec.witnessBits n * (decSizeBound n + 2 * treeMCSPPrefixM codec n) + 1

/--
**Bounded-solver assembly.**  A prefix-extension decider family that is
language-correct and size-bounded yields a `BoundedSearchSolver` for the tree-MCSP
search problem, with the true-greedy output circuits as its per-bit circuits.
-/
def boundedSearchSolver_of_deciderFamily
    (codec : TreeCircuitWitnessCodec threshold)
    (dec : ∀ n, C_DAG.Family (treeMCSPPrefixM codec n))
    (decSizeBound : Nat → Nat)
    (hlang : ∀ n, DecidesPrefixExtensionLanguage codec n (dec n))
    (hsize : ∀ n, C_DAG.size (dec n) ≤ decSizeBound n) :
    BoundedSearchSolver (treeProblem codec) C_DAG (boundedSolverSizeBound codec decSizeBound) where
  outputCircuit := fun n i => greedyTrueOutputCircuit codec n (dec n) i
  size_le := fun n i => by
    refine le_trans (size_greedyTrueOutputCircuit_le codec n (dec n) i) ?_
    unfold boundedSolverSizeBound
    gcongr
    exact hsize n
  solves := fun n x hpromise =>
    greedyTrueOutputCircuit_solves codec n (dec n) x hpromise
      (correctNextBitDecider_of_decidesLanguage codec n (dec n) x (hlang n))

end ContractExpansion
end Frontier
end Pnp4
