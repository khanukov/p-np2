import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixStateQueryCircuits

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.ComplexityInterfaces.DagCircuit

/-!
# One-step shared-bundle greedy extension

Block 5 of the downstream decision→search extraction, in the **Option ①**
architecture (merged in #1498 / #1499).

This assembles a *single* greedy step in the shared-bundle shape, with no
recursion.  Given:

* a bundle `B : DagBundle (tableLen n) i` holding the prior greedy bits `0..i-1`
  as functions of the instance `x` (over the `tableLen n` real inputs), and
* a decider `dec : C_DAG.Family (treeMCSPPrefixM codec n)` over the `M(n)`-bit
  prefix-query string,

we build the head circuit
`H = composeDeciderWithQuery dec (prefixStateQueryBitCircuit codec n i hi)`
over `tableLen n + i` inputs — the decider run on the prefix-state `(i, ·)` query,
whose payload region reads the prior bundle outputs (Block 4) — and apply the
shared-bundle step `DagCircuit.snocBundleSubst B H` (the primitive from #1498).

The result `greedyBundleStep … : DagBundle (tableLen n) (i + 1)`:

* **retains** all prior outputs (`evalOutput_greedyBundleStep_old`), and
* its **new** output is exactly the decider run on the prefix-state query for
  `(i, p)` with `p` the prior bundle outputs on `x`
  (`evalOutput_greedyBundleStep_new`), and
* its gate count is **additive** — `B.gates + H.gates`
  (`gates_greedyBundleStep`) — so `B` is shared, not re-embedded.

Scope discipline — one greedy step only:

* **no** recursion over the witness length (no fold of `greedyBundleStep`);
* **no** `BoundedSearchSolver` assembly;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/--
The head circuit for one greedy step: the decider `dec` composed with the
prefix-state `(i, ·)` query-bit circuits, over `tableLen n + i` inputs (the real
instance bits followed by the `i` prior bundle outputs).
-/
def greedyStepHead
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n + i) :=
  composeDeciderWithQuery dec (prefixStateQueryBitCircuit codec n i hi)

/--
**One-step shared-bundle greedy extension.**  Extend the prior-bits bundle `B` by
the bit decided by `dec` on the prefix-state `(i, ·)` query, sharing `B`'s gate
list via `DagCircuit.snocBundleSubst`.
-/
def greedyBundleStep
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : DagBundle (Pnp3.Models.Partial.tableLen n) i) :
    DagBundle (Pnp3.Models.Partial.tableLen n) (i + 1) :=
  snocBundleSubst B (greedyStepHead codec n i hi dec)

/-- The greedy step is *additive* in gate count: the prior bundle is shared, only
the head circuit's gates are added.  Direct instance of `snocBundleSubst_gates`. -/
theorem gates_greedyBundleStep
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : DagBundle (Pnp3.Models.Partial.tableLen n) i) :
    (greedyBundleStep codec n i hi dec B).gates
      = B.gates + (greedyStepHead codec n i hi dec).gates :=
  snocBundleSubst_gates B (greedyStepHead codec n i hi dec)

/-- The head circuit's size is bounded by the decider plus `2 · M(n)` (each
prefix-state query bit has size `≤ 2`).  So one greedy step adds only this much,
independent of the prior bits — the no-blow-up property. -/
theorem size_greedyStepHead_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.size (greedyStepHead codec n i hi dec)
      ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n := by
  refine le_trans
    (size_composeDeciderWithQuery_le dec (prefixStateQueryBitCircuit codec n i hi)) ?_
  have hbit : ∀ j : Fin (treeMCSPPrefixM codec n),
      C_DAG.size (prefixStateQueryBitCircuit codec n i hi j) ≤ 2 :=
    fun j => size_prefixStateQueryBitCircuit_le codec n i hi j
  have hsum : (∑ j, C_DAG.size (prefixStateQueryBitCircuit codec n i hi j))
      ≤ 2 * treeMCSPPrefixM codec n := by
    calc
      (∑ j, C_DAG.size (prefixStateQueryBitCircuit codec n i hi j))
          ≤ ∑ _j : Fin (treeMCSPPrefixM codec n), 2 := Finset.sum_le_sum (fun j _ => hbit j)
      _ = 2 * treeMCSPPrefixM codec n := by
          simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
  omega

/-- **Old outputs preserved.**  Each prior greedy bit is unchanged by the step. -/
@[simp] theorem evalOutput_greedyBundleStep_old
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : DagBundle (Pnp3.Models.Partial.tableLen n) i)
    (o : Fin i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleStep codec n i hi dec B).evalOutput (Fin.castAdd 1 o) x
      = B.evalOutput o x :=
  evalOutput_snocBundleSubst_old B (greedyStepHead codec n i hi dec) o x

/--
**New output correctness.**  The appended bit is exactly the decider run on the
prefix-state `(i, p)` query string, where the payload `p` is the prior bundle's
outputs on `x`.  This is the one-step greedy decision.
-/
theorem evalOutput_greedyBundleStep_new
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : DagBundle (Pnp3.Models.Partial.tableLen n) i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleStep codec n i hi dec B).evalOutput (Fin.natAdd i (0 : Fin 1)) x
      = C_DAG.eval dec
          (prefixStateQueryValue codec n i hi x (fun k => B.evalOutput k x)) := by
  have hinput :
      (fun j => (passthroughBundle B).evalOutput j x)
        = Fin.append x (fun k => B.evalOutput k x) := by
    funext j
    induction j using Fin.addCases <;> simp
  unfold greedyBundleStep greedyStepHead
  rw [evalOutput_snocBundleSubst_new]
  show C_DAG.eval (composeDeciderWithQuery dec (prefixStateQueryBitCircuit codec n i hi))
      (fun j => (passthroughBundle B).evalOutput j x) = _
  rw [hinput, eval_composeDeciderWithQuery]
  congr 1
  funext j
  exact eval_prefixStateQueryBitCircuit codec n i hi x (fun k => B.evalOutput k x) j

end ContractExpansion
end Frontier
end Pnp4
