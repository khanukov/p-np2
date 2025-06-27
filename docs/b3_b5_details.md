# Details for Lemma B Subtasks B-3 and B-5

This note expands upon the roadmap items **B‑3** and **B‑5** from
`docs/E1_roadmap.md`.  The goal is to clarify what remains to be proven
in the structural compression lemma ("Lemma B") and how these pieces fit
together.

## B‑3. Bounding the capacity

*Statement.*  For each split parameter `k` (the number of left input
bits) the number of canonical circuit descriptions that depend only on
those `k` bits should be bounded by `2^{(1-α)k}` for some
`α > 0`.  Intuitively, most small circuits cannot encode many distinct
left halves of a truth table.

*Current status.*  The file `canonical_circuit.lean` defines a
canonicalisation procedure together with the helper `codeLen` and the lemma
`canonical_desc_length`, stating that size‑`n^c` circuits admit
descriptions of length `O(n^c log n)`.  This implies an upper bound of
`2^{O(n^{c+1})}` on the number of distinct canonical circuits.  Partial
experiments with `lemma_b_search.py` confirm the predicted drop in
counts but the full asymptotic proof is still missing.

*Next steps.*

1. Formalise the canonical description scheme in Lean and prove
   injectivity.
2. Express the set of left table prefixes as a function of the
description bits; derive a counting bound for each fixed `k`.
3. Check the bound experimentally for small `n` to guide the choice of
   `α`.

Recent discussions suggest a more explicit counting argument.
By ordering gates topologically and lexicographically we eliminate
redundant subcircuits, obtaining a canonical description for every
size‑`m` circuit.  The proof of `canonical_desc_length` then yields at
most `2^{O(m \log n)}` canonical circuits, which for `m = n^c` becomes
`2^{O(n^{c+1})}`.  Fixing the first `k` bits of a truth table pins down
`2^k` evaluations.  Treating these answers as constants reduces the
number of relevant variables to `n - k`, so at most
`2^{O(n^c (n - k))}` canonical circuits remain compatible with the
prefix.  Choosing `k` about `C n^{c+1}` (for large enough `C`) forces
this quantity to be `\le 2^{(1-\alpha)k}` for some `\alpha > 0`.  In
other words, long prefixes drastically shrink the space of small
circuits and establish the desired capacity bound.

A corresponding Lemma `count_canonical_bounded` is stated in
`canonical_circuit.lean`.  Together with the helper function
`encodeCanon`, which turns canonical circuits into explicit bitstrings,
it packages the code-length estimate into an explicit counting bound.
Proving this lemma will complete the “canonical” block (B‑1/B‑3).

## B‑5. Constructing the cover

*Statement.*  Show that all functions computed by circuits of size at
most `n^c` admit a rectangular cover of the whole truth table with at
most `2^{N - N^δ}` rectangles (`N = 2^n`).  Each rectangle should be
enumerable in time `2^{(1-α)k}` on the left and `2^{(1-α)ℓ}` on the
right (`k + ℓ = n`).

*Current status.*  Low-sensitivity functions can already be compressed via
the Impagliazzo–Moshkovitz–Oliveira method.  The updated `cover.lean` module
records uncovered inputs explicitly and splits on them, but the sunflower
extraction and entropy steps are still placeholders.  Adapting the
 collision‑entropy technique to entire families remains an open task.
  An auxiliary lemma `exists_restrict_half` in `entropy.lean` shows that
  some input bit restricts a family to at most half its size.  Its
  real-valued sibling `exists_restrict_half_real` eases analytic bounds.
  The strengthened `exists_coord_entropy_drop` lemma then guarantees a
  one‑bit decrease of collision entropy, setting the stage for a cleaner
  argument.

*Next steps.*

1. Tune the numeric constants and integrate the canonical description bound
   from B‑3.
2. Optimise the enumeration procedures and clean up the formal proofs of the
   entropy bounds.

---
### Entropy branch

When no sunflower is found the set $\mathcal{F}$ of functions becomes highly diverse. We view a random variable $F$ uniformly distributed over $\mathcal{F}$ and split each table into a left part $A$ of length $k$ and a right part $B$ of length $\ell=N-k$.  If $H(A) \approx k$ and $H(B) \approx \ell$ continued to hold, the family would contain essentially all $2^N$ functions, which is impossible.  Hence one of the entropies drops by $\Omega(N^\delta)$.  Suppose $H(A)=k-\Delta$.

Then there are at most $2^{k-\Delta}$ distinct left halves among the functions of $\mathcal{F}$ while the conditional entropy $H(B\mid A)$ remains almost maximal.  Choosing $k$ at the point where the drop occurs yields a rectangle $A_i \times B_i$ with $A_i$ equal to the set of realised left halves and $B_i$ consisting of all right halves.  This rectangle covers nearly all of $\mathcal{F}$ but may include many extra functions.

An entropy-reduction lemma lets us pick a subset $A'_i \subseteq A_i$ of size $\approx 2^{k-\Delta}$ that contains most of the probability mass of $A$.  The rectangle $A'_i \times B_i$ still covers almost all of $\mathcal{F}$ and has size $2^{N-\Delta}$.  Iterating the argument until $\Delta = N^{\delta}$ produces a covering rectangle of size $2^{N-N^{\delta}}$.  After removing the covered portion we repeat the search for a sunflower or another entropy drop until the family is exhausted.

These clarifications do not yet close **Lemma B**, but they chart a concrete
route for completing the proof and for incorporating the results into
subsequent SAT algorithms.

The helper script `experiments/lemma_b_search.py` now accepts an
`--entropy` flag which reports the Shannon entropies `H(A)` and `H(B)`
for each split.  This numerical exploration illustrates the drop in
entropy predicted by the theory and helps choose a good threshold `k`.
With `--suggest` the script also prints which split achieves the largest
entropy drop, hinting at a promising decomposition point.
