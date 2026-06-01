import Pnp4.Frontier.ContractExpansion.TreeMCSPBoundedSolver

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# `BoundedSearchSolver` from a `PpolyDAG` prefix-extension decider

Block 9b of the downstream decision→search extraction — the **forward** bridge.

If the prefix-extension language `PrefixExtensionLanguage (treeMCSPConcretePrefixParser
threshold codec)` is in `PpolyDAG`, then there is a `BoundedSearchSolver` for the
tree-MCSP search problem with an explicit *extracted* size schedule.

Proof outline:

* `PpolyDAG_decider_as_C_DAG_decider` extracts a global exponent `c` and, at every
  length `m`, a `C_DAG` circuit deciding the language with `size ≤ m^c + c`;
* instantiate it at `m = treeMCSPPrefixM codec n` to get a decider family
  `dec n : C_DAG.Family (treeMCSPPrefixM codec n)` with language-correctness and the
  size bound `(treeMCSPPrefixM codec n)^c + c`;
* feed it to `boundedSearchSolver_of_deciderFamily` (Block 9, #1508).

This is a purely *forward*, conditional statement: it turns a membership hypothesis
into a solver.  It does **not** prove the contrapositive, define any no-solver
target, or assert a lower bound.

Scope discipline — forward bridge only:

* takes `PpolyDAG (PrefixExtensionLanguage …)` as the hypothesis;
* **no** `SearchProblemNoBoundedSolver` / contrapositive, **no**
  `NoPolynomialBoundedSearchSolver`;
* **no** `SearchMCSPMagnificationContract`, `VerifiedNPDAGLowerBoundSource`,
  NP-membership, endpoint, or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/--
**Forward `PpolyDAG`→solver bridge.**  If the prefix-extension language is in
`PpolyDAG`, then for some exponent `c` there is a `BoundedSearchSolver` for the
tree-MCSP search problem with the extracted size schedule
`witnessBits n · ((M n)^c + c + 2·M n) + 1` (where `M n = treeMCSPPrefixM codec n`).
-/
theorem boundedSearchSolver_of_PpolyDAG_prefixExtension
    (codec : TreeCircuitWitnessCodec threshold)
    (hPpoly : Pnp3.ComplexityInterfaces.PpolyDAG
      (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))) :
    ∃ c : Nat,
      Nonempty
        (BoundedSearchSolver (treeProblem codec) C_DAG
          (fun n =>
            codec.witnessBits n *
                ((treeMCSPPrefixM codec n) ^ c + c + 2 * treeMCSPPrefixM codec n)
              + 1)) := by
  obtain ⟨c, hc⟩ := PpolyDAG_decider_as_C_DAG_decider hPpoly
  have hc' : ∀ n, ∃ C : C_DAG.Family (treeMCSPPrefixM codec n),
      C_DAG.size C ≤ (treeMCSPPrefixM codec n) ^ c + c
        ∧ ∀ x, C_DAG.eval C x
            = PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)
                (treeMCSPPrefixM codec n) x :=
    fun n => hc (treeMCSPPrefixM codec n)
  choose dec hsize hlang using hc'
  exact ⟨c, ⟨boundedSearchSolver_of_deciderFamily codec dec
    (fun n => (treeMCSPPrefixM codec n) ^ c + c) hlang hsize⟩⟩

end ContractExpansion
end Frontier
end Pnp4
