import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyTrueOutputCircuits

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# The full true-greedy prefix is a solving witness

Block 8c of the downstream decision→search extraction.

Block 8a (#1504) proved the greedy prefix stays *extendable* at every length
`i ≤ witnessBits n`.  At the **full** length `i = witnessBits n` the prefix already
occupies every witness coordinate, so "extendable" collapses to "solving": the
witness `w` that the extendability gives must equal the greedy prefix itself (they
agree on all `witnessBits n` coordinates), hence the greedy prefix satisfies the
search relation.

Tying back to the circuit surface (Block 7′), the joint output of the
true-greedy output circuits `greedyTrueOutputCircuit` is exactly that full greedy
prefix (`searchSolverOutput_greedyTrueOutputCircuit`), so it too solves
(`greedyTrueOutputCircuit_solves`).

Scope discipline — pre-solver witness correctness only:

* still under the explicit `CorrectNextBitDecider` hypothesis (and the promise);
* **no** `BoundedSearchSolver` assembly (this proves the output solves, it does not
  package the size bound + correctness into the solver structure);
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint, or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/--
**Full greedy prefix solves.**  On a promise instance, with a correct next-bit
decider, the greedy prefix of the full length `witnessBits n` satisfies the search
relation — it is a valid witness for `x`.
-/
theorem greedyPrefix_solves
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec) :
    (treeProblem codec).relation n x
      (greedyPrefix codec n dec x (codec.witnessBits n) (Nat.le_refl _)) := by
  obtain ⟨w, hagree, hrel⟩ :=
    greedyPrefix_extendable codec n dec x hpromise hdec (codec.witnessBits n) (Nat.le_refl _)
  have hweq : w = greedyPrefix codec n dec x (codec.witnessBits n) (Nat.le_refl _) := by
    funext k
    exact hagree k
  rwa [hweq] at hrel

/-- The joint output of the true-greedy output circuits is the full greedy prefix. -/
theorem searchSolverOutput_greedyTrueOutputCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    searchSolverOutput (problem := treeProblem codec) (greedyTrueOutputCircuit codec n dec) x
      = greedyPrefix codec n dec x (codec.witnessBits n) (Nat.le_refl _) := by
  funext i
  simp only [searchSolverOutput, eval_greedyTrueOutputCircuit, greedyPrefix, fullGreedyTrueBundle]

/--
**True-greedy output circuits solve.**  On a promise instance, with a correct
next-bit decider, the joint output of the per-witness-bit true-greedy circuits
satisfies the search relation.  This is the witness-correctness fact a later
`BoundedSearchSolver` will package together with the size bound (Block 7′).
-/
theorem greedyTrueOutputCircuit_solves
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec) :
    (treeProblem codec).relation n x
      (searchSolverOutput (problem := treeProblem codec) (greedyTrueOutputCircuit codec n dec) x) := by
  rw [searchSolverOutput_greedyTrueOutputCircuit]
  exact greedyPrefix_solves codec n dec x hpromise hdec

end ContractExpansion
end Frontier
end Pnp4
