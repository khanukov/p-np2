import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleFold

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.ComplexityInterfaces.DagCircuit

/-!
# Final greedy bundle outputs as per-witness-bit C_DAG circuits

> **Legacy (state-query) surface — NOT solver-bearing.**  `greedyOutputCircuit` here
> projects the *state-query* bundle `fullGreedyBundle` (which queries `(i, p)`), and
> after the Block 8a semantic-mismatch fix (#1504) that greedy is **not** the one
> whose bits form a valid witness.  For the solver, use the correctness-bearing
> `greedyTrueOutputCircuit` / `fullGreedyTrueBundle`
> (`TreeMCSPGreedyTrueOutputCircuits.lean`), built on the true-extension fold.  These
> output circuits remain valid (same uniform size bound) but must **not** be used as
> solver/witness outputs.

Block 7 of the downstream decision→search extraction, in the **Option ①**
architecture (#1498–#1501).

Block 6 built the full greedy bundle `greedyBundleUpTo … (witnessBits n)` — one
shared gate list with `witnessBits n` output wires, of total size linear in
`witnessBits n`.  This file exposes each witness bit as an ordinary `C_DAG` output
circuit over the instance bits (`tableLen n`), via the bundle's `asCircuit`
projection, and records:

* `eval_greedyOutputCircuit` — the `i`-th output circuit computes the `i`-th bundle
  output (the `i`-th greedy bit), and
* `size_greedyOutputCircuit_le` — a **uniform** size bound `≤ witnessBits n ·
  (size dec + 2·M(n)) + 1`, *independent of `i`*, because every output circuit
  shares the one bundle gate list (`gates_greedyBundleUpTo_le`).

This is the `Fin (witnessBits n) → C_DAG.Family (tableLen n)` output-circuit family a
later `BoundedSearchSolver` will consume — but assembled and size-bounded only.

Scope discipline — output-circuit surface + size bound only:

* **no** `solves` / solver-correctness theorem (the greedy bits are not yet claimed
  to be a valid witness);
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/-- The full greedy bundle: all `witnessBits n` greedy bits over `tableLen n`
inputs, as one shared gate list. -/
def fullGreedyBundle
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    DagBundle (Pnp3.Models.Partial.tableLen n) (codec.witnessBits n) :=
  greedyBundleUpTo codec n dec (codec.witnessBits n) (Nat.le_refl _)

/-- The per-witness-bit output circuit: the `i`-th output of the full greedy bundle
as a single `C_DAG` circuit over the instance bits, sharing the bundle's gate
list. -/
def greedyOutputCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  (fullGreedyBundle codec n dec).asCircuit i

/-- The `i`-th output circuit computes the `i`-th bundle output (the `i`-th greedy
bit).  Definitional, via `DagBundle.evalOutput`. -/
@[simp] theorem eval_greedyOutputCircuit
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    C_DAG.eval (greedyOutputCircuit codec n dec i) x
      = (fullGreedyBundle codec n dec).evalOutput i x :=
  rfl

/-- **Uniform size bound.**  Every output circuit shares the single bundle gate
list, so its size is at most `witnessBits n · (size dec + 2·M(n)) + 1`,
independent of `i`.  Follows from the linear bundle bound
`gates_greedyBundleUpTo_le`. -/
theorem size_greedyOutputCircuit_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.size (greedyOutputCircuit codec n dec i)
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) + 1 := by
  have hs : C_DAG.size (greedyOutputCircuit codec n dec i)
      = (greedyOutputCircuit codec n dec i).gates + 1 := rfl
  have hg : (greedyOutputCircuit codec n dec i).gates = (fullGreedyBundle codec n dec).gates := rfl
  have hb : (fullGreedyBundle codec n dec).gates
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) :=
    gates_greedyBundleUpTo_le codec n dec (codec.witnessBits n) (Nat.le_refl _)
  rw [hs, hg]
  omega

end ContractExpansion
end Frontier
end Pnp4
