# Shrinkage ⇒ Switching-Atlas for AC⁰: Implementation Roadmap

This document distills the mathematical plan outlined in the latest research sync
and translates it into a Lean 4 to-do list. The goal is to remove every remaining
axiom from the shrinkage lemmas used in the Switching-Atlas pipeline.

## Target theorem (SAL-AC⁰)

For a finite family `F` of Boolean functions on `n` variables, each computed by an
`AC⁰` circuit of size `M` and depth `d`, we want a *common* partial decision tree
(`ℓ`-PDT) of depth

```
t = (log M) ^ O(d) + O(log (1/ε))
```

such that for every `f ∈ F` there is a subcollection of the leaves whose union
approximates `f` up to error `ε`. The leaf dictionary has cardinality at most
`2^t`, hence a quasi-polynomial bound in `M` and polynomial in `1/ε`.

The Lean proof should output:

* a structure `PartialDT` containing the trunk PDT together with tail decision
  trees of depth `≤ ℓ` per leaf;
* a predicate `IsCommonPartial ℓ F Q` capturing that *all* functions in `F`
  become depth-`≤ ℓ` decision trees on every leaf of `Q`;
* a lemma converting such a certificate into a bona fide atlas.

## External theorems to import

The proof leans on two results from the literature (Håstad, Impagliazzo–Matthews–Paturi,
Servedio–Tan):

1. **Switching lemma**: a `k`-CNF or `k`-DNF collapses to a decision tree of
   depth `t` with probability at least `1 - (C·p·k)^t` under a `p`-random
   restriction.
2. **Multi-switching lemma**: for a family of `S` formulas the probability that
   the restricted family fails to admit a common `ℓ`-PDT of depth `t` is bounded
   by `S^{⌈t/ℓ⌉} (C·p·k)^t`.

`ThirdPartyFacts/HastadMSL.lean` will host clean statement-level imports of both
lemmas, exposing only the combinatorial interface we need. No new axioms should
be introduced; instead, we commit to porting the proof scripts verbatim from the
references (or reuse an existing verified formalization if available).

## Inductive depth reduction strategy

1. **Depth 2 (DNF/CNF)**
   * Aggregate all bottom-level clauses across the family into a single set.
   * Apply the multi-switching lemma with parameters `p = Θ(1/k)` and
     `ℓ = Θ(log M)` to obtain a common partial tree of depth
     `t₁ = O(log (M·|F|/δ)) + O(log (1/ε))`.
   * Prune the depth-`ℓ` tails into leaf selections, accounting for the allowed
     error budget.

2. **Inductive step (`d ≥ 3`)**
   * Expose the bottom layer (a `k`-DNF/CNF) and apply multi-switching to obtain
     an `ℓ`-partial PDT whose leaves restrict the circuits to depth `d-1` and
     size `M' = M^{O(1)}`.
   * For each leaf, recursively invoke the depth-`d-1` version of the theorem.
   * Stitch the partial trees with a `splice` constructor, bounding the total
     depth by `t = t₁ + t₂`.

3. **Leaf budget**
   * Use `PDT.leaves_length_le_pow_depth` to bound the global dictionary by
     `2^t`.
   * Optionally refine individual `R_f` sizes to `O(t log (1/ε))` once the main
     proof is complete.

## Lean modules to implement

| Module | Purpose | Status |
| --- | --- | --- |
| `Core/PDTPartial.lean` | Definition of partial decision trees and depth accounting lemmas. | ✅ |
| `Core/ShrinkageWitness.lean` | Bridge from partial certificates to the existing `Shrinkage` interface. | ✅ |
| `ThirdPartyFacts/HastadMSL.lean` | Formal statements of the (multi-)switching lemma with parameter bookkeeping. | **new** |
| `Core/ShrinkageAC0.lean` | Inductive depth reduction proof producing a `PartialDT` certificate. | **new** |
| `Core/SAL_AC0.lean` | Wrapper invoking `partial_to_atlas` to obtain the final atlas. | refactor of existing `SAL_Core` |

Each module should come with extensive comments explaining the parameter chase,
mirroring Servedio–Tan, Corollary 3.5.

## Testing checklist

* `lake exe cache get` (if needed for third-party imports).
* `lake build` to ensure all new modules compile.
* `lake test` as the project’s umbrella regression command.
* Optional: targeted doc-tests for helper lemmas via `#eval` / `#check` in
  dedicated `Tests` files.

## Next actions

1. Implement `Core/PDTPartial.lean`, including supporting utilities for
   manipulating leaves (`LeafIndex`, `splice`, depth estimates`).
2. Extract statement-only versions of the switching lemmas into
   `ThirdPartyFacts/HastadMSL.lean`.
3. Formalize the depth-2 shrinkage lemma as the base case for the induction.
4. Generalize to arbitrary depth using recursive shrinkage.
5. Connect the shrinkage certificate to the existing `SAL_Core` pipeline and run
   `lake test`.

Progress should be recorded in the project changelog with references to the
relevant lemmas once each milestone is completed.

## Outstanding items after the latest refactor

Even though the Lean scaffolding for partial certificates and the SAL bridge is
now in place, the current development still relies on external axioms for the
core combinatorial bounds.  Concretely:

* `partial_shrinkage_for_AC0` in
  `ThirdPartyFacts/Facts_Switching.lean` remains an axiom.  We still have to
  supply a bona fide Lean proof by porting the depth-2 switching lemma and the
  multi-switching lemma, then running the inductive depth reduction described in
  Sections “Depth 2” and “Inductive step”.
* `shrinkage_for_localCircuit` is also axiomatic.  After finishing the AC⁰ case
  we must adapt the same machinery to the `LocalCircuitParameters` interface and
  re-establish the locality-specific depth bound.
* The roadmap steps 2–5 above are only partially implemented: modules such as
  `ThirdPartyFacts/HastadMSL.lean` and `Core/ShrinkageAC0.lean` currently expose
  wrappers around axioms rather than proved theorems.  The remaining work is to
  replace these wrappers with actual proofs and eliminate every `axiom` keyword
  from the shrinkage pipeline.

Removing these axioms and validating the resulting proofs with `lake test` will
fully complete Step A and unlock the seamless connection with Step B without any
unproved assumptions.
