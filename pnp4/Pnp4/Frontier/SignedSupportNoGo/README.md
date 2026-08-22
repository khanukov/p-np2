# Generic signed-support no-go

Classification: **infrastructure / no-go hardening**. This directory is not
P-vs-NP mainline progress and proves no complexity-class separation.

The three-module dependency chain is deliberately small:

1. `FiniteSignedSupport.lean` defines exact finite rational uniform and
   weighted Boolean averages. It proves that arbitrary signed, unnormalized
   reverse-one-sided weights exist exactly when the generator support hits
   every tested bounded-DAG predicate above the stated mass.
2. `FiniteSetDAG.lean` builds a computable list-based current-model `DagCircuit` accepting the
   complement of a list of `N`-bit strings, then supplies an order-insensitive `Finset` wrapper whose
   only noncomputability is the absence of a canonical `Finset.toList` order. Both forms have exact
   evaluation and the size bound `|S| * (2*N + 2) + 3`.
3. `DenseEasyBarrier.lean` introduces `FiniteEasyCover` and applies that
   avoider to dense/easy and signed-fooling premises.

The production imports terminate at `Complexity.DagCompose`; there is no
`OneTapeMagnification` or `StreamingMagnification` dependency.

## Honest theorem boundary

The direct no-go theorems require both inequalities explicitly:

- cover sparsity: `2^cover.codeBits * 2 < 2^N`;
- outer fit: `2^cover.codeBits * (2*N + 2) + 3 <= maxSize`.

They also require an actual `FiniteEasyCover`; no codec or enumeration theorem
is inferred from an abstract easy predicate. The signed endpoint additionally
requires every generator image to be easy and `epsilon < 1/2`. It permits
arbitrary negative and unnormalized rational weights.

The eventual-linear endpoint is restricted to truth-table geometry
`N = 2^n`. It says an eventually `O(n)` cover-bit family cannot coexist with
the stated all-exponent dense/easy witnesses. Each such witness still carries
the explicit sparsity premise. The theorem does not refute superlinear cover
bits, construct sparse covers, establish an MCSP lower bound, or imply
`P != NP`.
