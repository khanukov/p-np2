import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleFold
import Pnp4.Frontier.ContractExpansion.PrefixExtendableSplit

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.ComplexityInterfaces.DagCircuit

/-!
# Greedy extendability invariant

Block 8a of the downstream decision→search extraction.  This is the first place
the circuit plumbing (Blocks 4–7) meets real semantic content (Block 7.5): under an
explicit **correct-decider** hypothesis, the greedy bundle's outputs form a prefix
that stays *extendable* on promise inputs.

Concretely, let `dec` be the prefix-extension decider and
`greedyBundleUpTo … i` the shared greedy bundle (Block 6).  The *greedy prefix*
`greedyPrefix … i` is the length-`i` bit vector of that bundle's outputs on `x`.
We prove, by induction on `i`:

```
WitnessPrefixExtendable (treeProblem codec) n x hi (greedyPrefix codec n dec x i hi)
```

i.e. the greedy prefix can always be completed to a valid witness — given
(1) the promise that `x` is a yes-instance, and (2) `dec` correctly answering the
next-bit extendability question (`CorrectNextBitDecider`).  The step uses the
reject-branch split lemmas from #1503.

This is **not** solver correctness: it does not yet conclude that the *full* greedy
prefix is itself a valid witness, nor assemble a `BoundedSearchSolver`.

Scope discipline — the extendability invariant only:

* the decider's correctness is an **explicit hypothesis**, not proved here;
* **no** `BoundedSearchSolver` assembly and **no** `solves` conclusion;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint wrapper, or
  `P ≠ NP` / `NP ⊄ P/poly` consequence.
-/

variable {threshold : Nat → Nat}

/-- The concrete tree-MCSP search problem attached to a codec. -/
abbrev treeProblem (codec : TreeCircuitWitnessCodec threshold) : SearchMCSPCompressionProblem :=
  treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)

/-- The greedy prefix of length `i`: the first `i` greedy bits (the bundle's
outputs on `x`), as a witness prefix. -/
def greedyPrefix
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (i : Nat) (hi : i ≤ codec.witnessBits n) :
    PrefixBitVec i :=
  fun k => (greedyBundleUpTo codec n dec i hi).evalOutput k x

/--
**Correct next-bit decider** (explicit hypothesis).  `dec`, run on the prefix-state
`(i, p)` query for instance `x`, answers exactly whether the one-bit extension
`p ++ true` is extendable.  This is the next-bit extendability oracle the greedy
construction relies on.
-/
def CorrectNextBitDecider
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) : Prop :=
  ∀ (i : Nat) (hi : i + 1 ≤ codec.witnessBits n) (p : PrefixBitVec i),
    C_DAG.eval dec (prefixStateQueryValue codec n i (Nat.le_of_succ_le hi) x p) = true
      ↔ WitnessPrefixExtendable (problem := treeProblem codec) n x hi (Fin.snoc p true)

/-- The greedy prefix grows by one bit per step: the next bit is the decider's
verdict on the current prefix-state query. -/
theorem greedyPrefix_succ
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (i : Nat) (hi' : i + 1 ≤ codec.witnessBits n) :
    greedyPrefix codec n dec x (i + 1) hi'
      = Fin.snoc (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi'))
          (C_DAG.eval dec
            (prefixStateQueryValue codec n i (Nat.le_of_succ_le hi') x
              (greedyPrefix codec n dec x i (Nat.le_of_succ_le hi')))) := by
  funext k
  induction k using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last]
      exact evalOutput_greedyBundleUpTo_new codec n i dec hi' x
  | cast j =>
      simp only [Fin.snoc_castSucc]
      exact evalOutput_greedyBundleUpTo_old codec n i dec hi' j x

/--
**Greedy extendability invariant.**  On a promise (yes-)instance `x`, with a correct
next-bit decider, the greedy prefix of every length `i ≤ witnessBits n` is
extendable to a full valid witness.

Base case: the empty prefix is extendable because the promise instance has a
witness (`totalOnPromise`).  Step: the new bit is `dec`'s verdict; if it accepts,
`CorrectNextBitDecider` gives extendability of `p ++ true`; if it rejects, the
reject-branch lemma (`witnessPrefixExtendable_snoc_false_of_not_true`) gives
extendability of `p ++ false`.
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
          (prefixStateQueryValue codec n i hi x (greedyPrefix codec n dec x i hi)) = true
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
