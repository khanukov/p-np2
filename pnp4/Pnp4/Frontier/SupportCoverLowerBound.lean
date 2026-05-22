import Pnp4.Frontier.SearchMCSPMagnification
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter

namespace Pnp4
namespace Frontier

open AlgorithmsToLowerBounds
open ContractExpansion

/--
`C_DAG` support-cover upper bound schema.

The theorem is intentionally stated as a reusable adapter surface: if each
output-bit circuit in a bounded search solver has support at most its DAG size,
then the union support cover used by the full solver is bounded by
`witnessBits n * sizeBound n`.

This is the combinatorial estimate consumed by the hWeak contradiction theorem
below.
-/
theorem C_DAG_support_card_le_size
    {problem : SearchMCSPCompressionProblem}
    {sizeBound : Nat → Nat}
    (solver : BoundedSearchSolver problem C_DAG sizeBound)
    (hSupportLeSize :
      ∀ n : Nat, ∀ i : Fin (problem.witnessBits n),
        (Pnp3.ComplexityInterfaces.DagCircuit.support
          (solver.outputCircuit n i)).card
          ≤ C_DAG.size (solver.outputCircuit n i))
    (n : Nat) :
    ∀ i : Fin (problem.witnessBits n),
      (Pnp3.ComplexityInterfaces.DagCircuit.support
        (solver.outputCircuit n i)).card ≤ sizeBound n := by
  intro i
  exact Nat.le_trans (hSupportLeSize n i) (solver.size_le n i)

/--
Pure hWeak contradiction surface (no magnification contract is used).

If promised instances contain a zero point and all singleton points, and the
relation is functional (uniqueness of witness on promise instances), then any
bounded solver would force a support cover of size at least `instanceBits n`.
Therefore the inequality
`witnessBits n * sizeBound n < instanceBits n`
contradicts existence of a bounded `C_DAG` solver.

The bridge from zero/singleton + functionality to the lower bound on support
cover cardinality is passed as an explicit premise
`hSupportCoverAtLeastInstanceBits`; this keeps this file focused on the final
counting contradiction used by SearchMCSP weak lower-bound sections.
-/
theorem no_bounded_solver_if_support_cover_too_small
    (problem : SearchMCSPCompressionProblem)
    (sizeBound : Nat → Nat)
    (hZeroPromised : ∀ n : Nat,
      problem.promise n (fun _ => false))
    (hSingletonPromised : ∀ n : Nat,
      ∀ j : Fin (problem.instanceBits n),
        problem.promise n (fun k => k = j))
    (hFunctional :
      ∀ n : Nat,
        ∀ x : AlgorithmsToLowerBounds.BitVec (problem.instanceBits n),
          problem.promise n x →
            ∀ w₁ w₂ : AlgorithmsToLowerBounds.BitVec (problem.witnessBits n),
              problem.relation n x w₁ →
              problem.relation n x w₂ →
              w₁ = w₂)
    (hSupportCoverAtLeastInstanceBits :
      ∀ solver : BoundedSearchSolver problem C_DAG sizeBound,
        ∀ n : Nat,
          problem.instanceBits n ≤
            problem.witnessBits n * sizeBound n)
    (hTooSmall : ∀ n : Nat,
      problem.witnessBits n * sizeBound n < problem.instanceBits n) :
    SearchProblemNoBoundedSolver problem C_DAG sizeBound := by
  intro hNonempty
  rcases hNonempty with ⟨solver⟩
  let n0 : Nat := 0
  have hLower :
      problem.instanceBits n0 ≤
        problem.witnessBits n0 * sizeBound n0 :=
    hSupportCoverAtLeastInstanceBits solver n0
  have hUpper :
      problem.witnessBits n0 * sizeBound n0 < problem.instanceBits n0 :=
    hTooSmall n0
  exact (Nat.not_lt_of_ge hLower) hUpper

end Frontier
end Pnp4
