import Pnp4.Frontier.ContractExpansion.TreeMCSPTrueExtensionQuery
import Pnp4.Frontier.ContractExpansion.PrefixExtendableSplit

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.ComplexityInterfaces.DagCircuit

/-!
# Greedy extendability invariant (true-extension query)

Block 8a of the downstream decision→search extraction — the first place the circuit
plumbing meets real semantic content (Block 7.5).

**Correction over the first draft.**  The greedy step must ask the decider
*"is `p ++ true` extendable?"*, so it runs `dec` on the **true-extension** query
`prefixTrueExtensionQueryValue` (which encodes the prefix-state `(i+1, p ++ true)`),
*not* on the `(i, p)` query.  This is what makes the `CorrectNextBitDecider`
hypothesis dischargeable from an ordinary `PrefixExtensionLanguage` decider: such a
decider on the encoded `p ++ true` decides extendability of `p ++ true`.

`greedyTrueBundleUpTo` folds the true-extension greedy step (sharing the bundle via
`snocBundleSubst`), `greedyPrefix` reads off its outputs, and `greedyPrefix_extendable`
proves — by induction, using the reject-branch split lemma (#1503) — that the greedy
prefix stays extendable on promise inputs under a correct next-bit decider.

Scope discipline — the extendability invariant only:

* the decider's correctness is an **explicit hypothesis**, not proved here;
* **no** `BoundedSearchSolver` assembly and **no** `solves` conclusion;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint, or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/-- The concrete tree-MCSP search problem attached to a codec. -/
abbrev treeProblem (codec : TreeCircuitWitnessCodec threshold) : SearchMCSPCompressionProblem :=
  treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)

/-- The head circuit for one true-extension greedy step: `dec` composed with the
true-extension query-bit circuits, over `tableLen n + i` inputs. -/
def greedyTrueStepHead
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat) (hi : i + 1 ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n + i) :=
  composeDeciderWithQuery dec (prefixTrueExtensionQueryBitCircuit codec n i hi)

/-- One greedy step adds at most `size dec + 2·M(n)` gates, independent of the prior
bits. -/
theorem size_greedyTrueStepHead_le
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat) (hi : i + 1 ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.size (greedyTrueStepHead codec n i hi dec)
      ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n := by
  refine le_trans
    (size_composeDeciderWithQuery_le dec (prefixTrueExtensionQueryBitCircuit codec n i hi)) ?_
  have hsum : (∑ j, C_DAG.size (prefixTrueExtensionQueryBitCircuit codec n i hi j))
      ≤ 2 * treeMCSPPrefixM codec n := by
    calc
      (∑ j, C_DAG.size (prefixTrueExtensionQueryBitCircuit codec n i hi j))
          ≤ ∑ _j : Fin (treeMCSPPrefixM codec n), 2 :=
            Finset.sum_le_sum (fun j _ => size_prefixTrueExtensionQueryBitCircuit_le codec n i hi j)
      _ = 2 * treeMCSPPrefixM codec n := by
          simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
  omega

/-- The shared bundle of the first `i` greedy bits, folding the true-extension step. -/
def greedyTrueBundleUpTo
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    (i : Nat) → i ≤ codec.witnessBits n → DagBundle (Pnp3.Models.Partial.tableLen n) i
  | 0, _ => emptyBundle (Pnp3.Models.Partial.tableLen n)
  | i + 1, hi =>
      snocBundleSubst (greedyTrueBundleUpTo codec n dec i (Nat.le_of_succ_le hi))
        (greedyTrueStepHead codec n i hi dec)

theorem greedyTrueBundleUpTo_succ
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n) :
    greedyTrueBundleUpTo codec n dec (i + 1) hi =
      snocBundleSubst (greedyTrueBundleUpTo codec n dec i (Nat.le_of_succ_le hi))
        (greedyTrueStepHead codec n i hi dec) :=
  rfl

/-- The greedy prefix of length `i`: the first `i` greedy bits on `x`. -/
def greedyPrefix
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (i : Nat) (hi : i ≤ codec.witnessBits n) :
    PrefixBitVec i :=
  fun k => (greedyTrueBundleUpTo codec n dec i hi).evalOutput k x

/-- Old greedy bits are preserved across a fold step. -/
theorem evalOutput_greedyTrueBundleUpTo_old
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (o : Fin i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyTrueBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.castAdd 1 o) x
      = (greedyTrueBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).evalOutput o x := by
  rw [greedyTrueBundleUpTo_succ]
  exact evalOutput_snocBundleSubst_old _ (greedyTrueStepHead codec n i hi dec) o x

/-- The newest greedy bit is `dec`'s verdict on the true-extension query for the
previous prefix — i.e. on the prefix-state `(i+1, p ++ true)` query. -/
theorem evalOutput_greedyTrueBundleUpTo_new
    (codec : TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyTrueBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.natAdd i (0 : Fin 1)) x
      = C_DAG.eval dec
          (prefixStateQueryValue codec n (i + 1) hi x
            (Fin.snoc (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi)) true)) := by
  have hinput :
      (fun j => (passthroughBundle (greedyTrueBundleUpTo codec n dec i (Nat.le_of_succ_le hi))).evalOutput j x)
        = Fin.append x (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi)) := by
    funext j
    induction j using Fin.addCases <;> simp [greedyPrefix]
  rw [greedyTrueBundleUpTo_succ, evalOutput_snocBundleSubst_new]
  show C_DAG.eval (composeDeciderWithQuery dec (prefixTrueExtensionQueryBitCircuit codec n i hi))
      (fun j => (passthroughBundle (greedyTrueBundleUpTo codec n dec i (Nat.le_of_succ_le hi))).evalOutput j x)
      = _
  rw [hinput, eval_composeDeciderWithQuery]
  have hbits : (fun j => C_DAG.eval (prefixTrueExtensionQueryBitCircuit codec n i hi j)
          (Fin.append x (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi))))
        = prefixStateQueryValue codec n (i + 1) hi x
            (Fin.snoc (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi)) true) := by
    funext j
    rw [eval_prefixTrueExtensionQueryBitCircuit, prefixTrueExtensionQueryValue]
  rw [hbits]

/-- The greedy prefix grows by one bit per step: the next bit is `dec`'s verdict on
the true-extension query for the current prefix. -/
theorem greedyPrefix_succ
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (i : Nat) (hi' : i + 1 ≤ codec.witnessBits n) :
    greedyPrefix codec n dec x (i + 1) hi'
      = Fin.snoc (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi'))
          (C_DAG.eval dec
            (prefixStateQueryValue codec n (i + 1) hi' x
              (Fin.snoc (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi')) true))) := by
  funext k
  induction k using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last]
      exact evalOutput_greedyTrueBundleUpTo_new codec n i dec hi' x
  | cast j =>
      simp only [Fin.snoc_castSucc]
      exact evalOutput_greedyTrueBundleUpTo_old codec n i dec hi' j x

/--
**Correct next-bit decider** (explicit hypothesis).  `dec`, run on the *encoded
`p ++ true`* query (the prefix-state `(i+1, p ++ true)` query string), answers
exactly whether `p ++ true` is extendable.  This is dischargeable from an ordinary
`PrefixExtensionLanguage` decider, which on that query decides extendability of the
encoded prefix `p ++ true`.
-/
def CorrectNextBitDecider
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) : Prop :=
  ∀ (i : Nat) (hi : i + 1 ≤ codec.witnessBits n) (p : PrefixBitVec i),
    C_DAG.eval dec (prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)) = true
      ↔ WitnessPrefixExtendable (problem := treeProblem codec) n x hi (Fin.snoc p true)

/--
**Greedy extendability invariant.**  On a promise (yes-)instance `x`, with a correct
next-bit decider, the greedy prefix of every length `i ≤ witnessBits n` is extendable
to a full valid witness.

Base: the empty prefix is extendable via `totalOnPromise`.  Step: the new bit is
`dec`'s verdict on the encoded `p ++ true` query; accept gives extendability of
`p ++ true` directly, reject uses `witnessPrefixExtendable_snoc_false_of_not_true`.
-/
theorem greedyPrefix_extendable
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec) :
    ∀ (i : Nat) (hi : i ≤ codec.witnessBits n),
      WitnessPrefixExtendable (problem := treeProblem codec) n x hi
        (greedyPrefix codec n dec x i hi) := by
  intro i
  induction i with
  | zero =>
      intro _
      obtain ⟨w, hw⟩ := (treeProblem codec).totalOnPromise n x hpromise
      exact ⟨w, fun k => k.elim0, hw⟩
  | succ i ih =>
      intro hi'
      have hi : i ≤ codec.witnessBits n := Nat.le_of_succ_le hi'
      rw [greedyPrefix_succ]
      by_cases hb : C_DAG.eval dec
          (prefixStateQueryValue codec n (i + 1) hi' x
            (Fin.snoc (greedyPrefix codec n dec x i hi) true)) = true
      · rw [hb]
        exact (hdec i hi' (greedyPrefix codec n dec x i hi)).mp hb
      · rw [Bool.not_eq_true] at hb
        rw [hb]
        refine witnessPrefixExtendable_snoc_false_of_not_true (problem := treeProblem codec) n x hi'
          (greedyPrefix codec n dec x i hi) (ih hi) ?_
        intro hext
        have hT := (hdec i hi' (greedyPrefix codec n dec x i hi)).mpr hext
        rw [hT] at hb
        exact absurd hb (by decide)

end ContractExpansion
end Frontier
end Pnp4
