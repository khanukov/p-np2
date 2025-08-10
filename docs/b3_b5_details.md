> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
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
the Impagliazzo–Moshkovitz–Oliveira method.  The updated `cover2.lean` module
records uncovered inputs explicitly and splits on them.  A new lemma
`sunflower_step` extracts a monochromatic subcube whenever a large set of
small-support functions with **distinct supports** remains uncovered,
while the entropy step now splits on a coordinate whose restriction
reduces entropy by one bit.  The cardinal lemma `exists_coord_card_drop`
has been proved, and tests for `sunflower_step` ensure its behaviour.
The lemma `buildCover_pointwiseMono` now provides a full proof that every rectangle
inserted by `buildCover` is monochromatic.  A first version of the counting
lemma `buildCover_card_bound` is now proven via a measure-based
bound, but the detailed induction argument is not yet complete.
  Whenever an uncovered pair is found the family must contain at least
  two functions, so the entropy split is well-defined.  The opposite
  branch of the split also satisfies the same entropy bound because
  restriction never increases `H₂`.  Thus both recursive calls decrease
  the measure on which `buildCover` recurses.
  Every rectangle produced in this way is monochromatic for the whole
  family; this follows by induction on the construction of the cover.
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

### Explicit lemma statements

Two auxiliary lemmas remain missing from the formalisation.  Writing down
their intended form clarifies how the cover construction should proceed.

```lean
/-- If we have a family `F` and at least `m` distinct 1-inputs that are
    common to all `f ∈ F`, and every set of `t` such points has an
    intersection on fewer than `w` coordinates, then some nontrivial subcube
    is monochromatic for many of these points. -/
lemma sunflower_step (F : Family n) (Pts : Finset (Point n)) (m t w : ℕ)
  (Hpts : ∀ f ∈ F, ∀ x ∈ Pts, f x = true)
  (Huge : Pts.card ≥ (t - 1)! * w^t)
  (BoundInt : ∀ P ⊆ Pts, P.card = t → (⋂ x ∈ P, support x).card < w) :
  ∃ (I : Finset (Fin n)) (val : ∀ i ∈ I, Bool),
    I.Nonempty ∧
    (∀ x ∈ Pts, (∀ i ∈ I, x i = val i) →
       ∃ P ⊆ Pts, P.card = t ∧ ∀ y ∈ P, ∀ i ∈ I, y i = val i) ∧
    (∃ b : Bool, ∀ f ∈ F, ∀ x, (∀ i ∈ I, x i = val i) → f x = b)
```

```lean
/-- If every `f ∈ F` has sensitivity at most `s`, then all 1-inputs of the
    family can be covered by `2^{O(s \log n)}` subcubes. -/
lemma low_sensitivity_cover (F : Family n) (s : ℕ)
  (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
  ∃ Rset : Finset (Subcube n),
    Rset.card ≤ 2 ^ (C * s * log n) ∧
      ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R ∧ ∀ y ∈ R, f y = true
```

An auxiliary lemma `low_sensitivity_cover_single` demonstrates the same bound
for a single function using a small decision tree structure.
Here `C` denotes an absolute constant.  The second lemma packages the
decision-tree bound for low-sensitivity functions from Gopalan et al.
In both cases the proofs would reuse the previously established
core-agreement lemmas and the classical sunflower lemma.

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

### Sketch of `buildCover_card_bound`

The remaining numeric bound argues by a well-founded recursion on the measure

\[
  \mu(F,h,R) = 2h + |\mathrm{uncovered}\,F\,R|,
\]

lexicographically ordered by the entropy budget `h` and then by the number of
uncovered pairs.  The proof proceeds as follows.

1. **Base case.**  If `uncovered = ∅` then `buildCover` simply returns the
   existing set `R`.  Its cardinality is unchanged and obviously bounded by
   `mBound`.
2. **Low-sensitivity branch.**  When all functions in the family have small
   sensitivity, the helper lemma `low_sensitivity_cover` yields a collection of
   rectangles covering all remaining `1`‑inputs.  The number of rectangles is at
   most `2^{10h}`, so the union with the current set stays below
   `mBound n h`.
3. **Entropy branch.**  Otherwise a coordinate split decreases the entropy
   budget.  Both restricted families have measure strictly smaller than the
   original one, allowing the induction hypothesis to bound the size of their
   covers by `mBound n (h-1)`.  Doubling this quantity is still dominated by
   `mBound n h`.
4. **Sunflower branch.**  Occasionally a sunflower argument extracts a single
   rectangle that simultaneously covers many functions.  This step reduces the
   uncovered set by at least two elements, again decreasing `μ` and keeping the
   overall number of inserted rectangles below `mBound`.

In each case the measure drops, so after at most `μ(F,h,∅)` iterations it
reaches `2h` and the recursion terminates.  Since `mBound` dominates this
initial measure, the final cover produced by `buildCover` contains at most
`mBound n h` rectangles.  The Lean development implements the required helper
More recently the key inequalities have been rechecked in detail.
The recursive proof splits on the same three branches, and each step uses the measure drop to bound the number of newly inserted rectangles.
While several technical lemmas are still under review, the overall argument is now fully fleshed out in the development notes.
