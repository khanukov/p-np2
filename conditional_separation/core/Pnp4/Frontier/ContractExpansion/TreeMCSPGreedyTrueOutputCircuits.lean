import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyExtendable

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.ComplexityInterfaces.DagCircuit

/-!
# True-greedy output circuits (correctness-bearing)

Block 7′ of the downstream decision→search extraction.

`#1502` exposed per-witness-bit output circuits from the *state-query* greedy
(`greedyBundleUpTo`).  After the Block 8a semantic-mismatch fix (#1504), the
correctness-bearing greedy is the **true-extension** fold `greedyTrueBundleUpTo`
(its decider queries the encoded `p ++ true`).  This file re-exposes the
output-circuit surface — with the same linear size bound — on *that* fold, so the
later solver construction consumes the correct greedy.

* `fullGreedyTrueBundle` — the full true-greedy bundle of `witnessBits n` bits;
* `greedyTrueOutputCircuit i` — the `i`-th output as a `C_DAG` circuit;
* `eval_greedyTrueOutputCircuit`, `size_greedyTrueOutputCircuit_le` (uniform `≤
  witnessBits n · (size dec + 2·M(n)) + 1`, via the linear fold bound proved here).

The legacy `greedyBundleUpTo` / `greedyOutputCircuit` (state-query, `(i, p)`) remain
in the tree as valid constructions but are **not** solver-bearing; their module
docstrings now say so.

Scope discipline — true-greedy output surface + size bound only:

* **no** `solves` / solver-correctness, **no** `BoundedSearchSolver`;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint, or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/-- Additive size recurrence for the true-greedy fold (prior bundle shared). -/
theorem gates_greedyTrueBundleUpTo_succ
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n) :
    (greedyTrueBundleUpTo codec n dec (i + 1) hi).gates
      = (greedyTrueBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).gates
          + (greedyTrueStepHead codec n i hi dec).gates := by
  rw [greedyTrueBundleUpTo_succ]
  exact snocBundleSubst_gates _ (greedyTrueStepHead codec n i hi dec)

/-- **Linear size bound** for the true-greedy fold: `i` bits cost at most
`i · (size dec + 2·M(n))` gates. -/
theorem gates_greedyTrueBundleUpTo_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    ∀ (i : Nat) (hi : i ≤ codec.witnessBits n),
      (greedyTrueBundleUpTo codec n dec i hi).gates
        ≤ i * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) := by
  intro i
  induction i with
  | zero =>
      intro _
      simp [greedyTrueBundleUpTo, emptyBundle]
  | succ i ih =>
      intro hi
      rw [gates_greedyTrueBundleUpTo_succ, add_mul, one_mul]
      have hhead : (greedyTrueStepHead codec n i hi dec).gates
          ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n := by
        have h1 := size_greedyTrueStepHead_le codec n i hi dec
        have h2 : C_DAG.size (greedyTrueStepHead codec n i hi dec)
            = (greedyTrueStepHead codec n i hi dec).gates + 1 := rfl
        omega
      exact Nat.add_le_add (ih (Nat.le_of_succ_le hi)) hhead

/-- The full true-greedy bundle: all `witnessBits n` greedy bits. -/
def fullGreedyTrueBundle
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    DagBundle (Pnp3.Models.Partial.tableLen n) (codec.witnessBits n) :=
  greedyTrueBundleUpTo codec n dec (codec.witnessBits n) (Nat.le_refl _)

/-- The per-witness-bit output circuit of the correctness-bearing true greedy. -/
def greedyTrueOutputCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  (fullGreedyTrueBundle codec n dec).asCircuit i

/-- The `i`-th output circuit computes the `i`-th true-greedy bit. -/
@[simp] theorem eval_greedyTrueOutputCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    C_DAG.eval (greedyTrueOutputCircuit codec n dec i) x
      = (fullGreedyTrueBundle codec n dec).evalOutput i x :=
  rfl

/-- **Uniform size bound**, independent of `i` (every output circuit shares the one
true-greedy bundle gate list). -/
theorem size_greedyTrueOutputCircuit_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.size (greedyTrueOutputCircuit codec n dec i)
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) + 1 := by
  have hs : C_DAG.size (greedyTrueOutputCircuit codec n dec i)
      = (greedyTrueOutputCircuit codec n dec i).gates + 1 := rfl
  have hg : (greedyTrueOutputCircuit codec n dec i).gates = (fullGreedyTrueBundle codec n dec).gates := rfl
  have hb : (fullGreedyTrueBundle codec n dec).gates
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) :=
    gates_greedyTrueBundleUpTo_le codec n dec (codec.witnessBits n) (Nat.le_refl _)
  rw [hs, hg]
  omega

end ContractExpansion
end Frontier
end Pnp4
