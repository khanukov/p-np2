import Attempt.Codec
import ConditionalSeparation.OpenProblem

namespace Research.SolverToDag.LowerBound
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds

/-- Optional decision lower bound. One k precedes every excluded degree e;
at a hard length, EVERY bounded DAG has its own truth-table counterexample.
N = tableLen n = 2^n. No such exclusion is proved by this interface. -/
def FixedKTreeMCSPDAGExclusion (k : Nat) : Prop :=
  ∀ e : Nat, ∃ n : Nat,
    ∀ c : DagCircuit (Pnp3.Models.Partial.tableLen n),
      size c ≤ Pnp3.Models.Partial.tableLen n ^ e + e →
        ∃ tt : TruthTable n,
          ¬ (eval c tt = true ↔ treeMCSPPredicate n (n ^ k + k) tt)

/-- The fixed threshold is chosen once, outside every circuit degree. -/
def TreeMCSPDAGLowerBound : Prop := ∃ k : Nat, FixedKTreeMCSPDAGExclusion k

theorem fixedK_excludes_solver (k : Nat) (h : FixedKTreeMCSPDAGExclusion k)
    (d : Nat) : ¬ Nonempty (ConcreteSolver k d) := by
  rintro ⟨S⟩
  obtain ⟨e, he⟩ := Codec.solver_to_dag_capstone k d
  obtain ⟨n, hn⟩ := h e
  obtain ⟨tt, hbad⟩ := hn (Codec.recognizer S n) (he S n).2
  exact hbad ((he S n).1 tt)

/-- Conditional implication only: the hypothesis is not discharged. Direct R
and the optional lengthwise interface are unchanged. -/
theorem lowerBound_implies_R (h : TreeMCSPDAGLowerBound) :
    ConditionalSeparation.OpenProblem.R := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  intro d
  exact fixedK_excludes_solver k hk d

end Research.SolverToDag.LowerBound
