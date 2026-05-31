import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleStep

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.ComplexityInterfaces.DagCircuit

/-!
# Recursive shared-bundle greedy fold

> **Legacy (state-query) surface — not solver-bearing.**  This fold iterates the
> state-query step (`greedyBundleStep`, querying `(i, p)`), which is **not** the
> correctness-bearing greedy.  Use the true-extension fold `greedyTrueBundleUpTo`
> (`TreeMCSPGreedyExtendable.lean`) and its outputs `greedyTrueOutputCircuit`
> (`TreeMCSPGreedyTrueOutputCircuits.lean`) for solver/witness construction.  The
> definitions here remain valid constructions (with the same linear size bound) but
> must not be used for correctness.

Block 6 of the downstream decision→search extraction, in the **Option ①**
architecture (#1498 / #1499 / #1500).

This iterates the one-step extension `greedyBundleStep` (Block 5) from `0` to a
target length `i ≤ codec.witnessBits n`, producing one shared bundle
`greedyBundleUpTo … i : DagBundle (tableLen n) i` holding the first `i` greedy
bits.  Because each step *shares* the prior bundle's gate list, the total gate
count is **linear** in `i`:

```
(greedyBundleUpTo … i).gates ≤ i · (size dec + 2·M(n))
```

(`gates_greedyBundleUpTo_le`).  This is the polynomial-size payoff the
size-feasibility spike (`NaiveGreedySizeSpike`) showed the naive per-bit
re-embedding cannot achieve (it blows up as `seed·2^i`).

The bundle is characterized by a recurrence: old outputs are preserved across the
fold (`evalOutput_greedyBundleUpTo_old`), and the newest output is the decider run
on the prefix-state `(i, p)` query, with `p` the *previous* fold's outputs on `x`
(`evalOutput_greedyBundleUpTo_new`).

Scope discipline — fold/bundle + size & eval recurrence only:

* **no** `BoundedSearchSolver` assembly and **no** solver-correctness theorem;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/--
The shared bundle of the first `i` greedy bits, built by folding `greedyBundleStep`
from the empty bundle.  Requires `i ≤ codec.witnessBits n` (each step is within the
parser's prefix-length contract).
-/
def greedyBundleUpTo
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    (i : Nat) → i ≤ codec.witnessBits n → DagBundle (Pnp3.Models.Partial.tableLen n) i
  | 0, _ => emptyBundle (Pnp3.Models.Partial.tableLen n)
  | i + 1, hi =>
      greedyBundleStep codec n i (Nat.le_of_succ_le hi) dec
        (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi))

@[simp] theorem greedyBundleUpTo_zero
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (h : 0 ≤ codec.witnessBits n) :
    greedyBundleUpTo codec n dec 0 h = emptyBundle (Pnp3.Models.Partial.tableLen n) :=
  rfl

theorem greedyBundleUpTo_succ
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n) :
    greedyBundleUpTo codec n dec (i + 1) hi =
      greedyBundleStep codec n i (Nat.le_of_succ_le hi) dec
        (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)) :=
  rfl

/-- **Old outputs preserved across the fold.**  Extending by one bit leaves the
first `i` greedy bits unchanged. -/
theorem evalOutput_greedyBundleUpTo_old
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (o : Fin i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.castAdd 1 o) x
      = (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).evalOutput o x := by
  rw [greedyBundleUpTo_succ]
  exact evalOutput_greedyBundleStep_old codec n i (Nat.le_of_succ_le hi) dec _ o x

/-- **New output of the fold.**  The newest greedy bit is the decider run on the
prefix-state `(i, p)` query, where `p` is the previous fold's outputs on `x` — the
repeated greedy decision. -/
theorem evalOutput_greedyBundleUpTo_new
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.natAdd i (0 : Fin 1)) x
      = C_DAG.eval dec
          (prefixStateQueryValue codec n i (Nat.le_of_succ_le hi) x
            (fun k => (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).evalOutput k x)) := by
  rw [greedyBundleUpTo_succ]
  exact evalOutput_greedyBundleStep_new codec n i (Nat.le_of_succ_le hi) dec _ x

/-- **Additive size recurrence.**  Each fold step adds only the head circuit's
gates (the prior bundle is shared). -/
theorem gates_greedyBundleUpTo_succ
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n) :
    (greedyBundleUpTo codec n dec (i + 1) hi).gates
      = (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).gates
          + (greedyStepHead codec n i (Nat.le_of_succ_le hi) dec).gates := by
  rw [greedyBundleUpTo_succ]
  exact gates_greedyBundleStep codec n i (Nat.le_of_succ_le hi) dec _

/-- **Linear (polynomial) size bound.**  The fold of `i` greedy bits has at most
`i · (size dec + 2·M(n))` gates — linear in `i`, versus the `seed·2^i` blow-up of
the naive per-bit re-embedding.  This is the size-feasibility payoff of Option ①. -/
theorem gates_greedyBundleUpTo_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    ∀ (i : Nat) (hi : i ≤ codec.witnessBits n),
      (greedyBundleUpTo codec n dec i hi).gates
        ≤ i * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) := by
  intro i
  induction i with
  | zero =>
      intro _
      simp [greedyBundleUpTo, emptyBundle]
  | succ i ih =>
      intro hi
      have hi' : i ≤ codec.witnessBits n := Nat.le_of_succ_le hi
      rw [gates_greedyBundleUpTo_succ, add_mul, one_mul]
      have hhead : (greedyStepHead codec n i hi' dec).gates
          ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n := by
        have h1 := size_greedyStepHead_le codec n i hi' dec
        have h2 : C_DAG.size (greedyStepHead codec n i hi' dec)
            = (greedyStepHead codec n i hi' dec).gates + 1 := rfl
        omega
      exact Nat.add_le_add (ih hi') hhead

end ContractExpansion
end Frontier
end Pnp4
