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

## B‑5. Constructing the cover

*Statement.*  Show that all functions computed by circuits of size at
most `n^c` admit a rectangular cover of the whole truth table with at
most `2^{N - N^δ}` rectangles (`N = 2^n`).  Each rectangle should be
enumerable in time `2^{(1-α)k}` on the left and `2^{(1-α)ℓ}` on the
right (`k + ℓ = n`).

*Current status.*  Low-sensitivity functions can already be compressed via
the Impagliazzo–Moshkovitz–Oliveira method.  The new `cover.lean` module
records uncovered inputs explicitly and splits on them, but the
sunflower and entropy steps are still placeholders.  Collision‑entropy
techniques for biased functions have yet to be adapted to families.

*Next steps.*

1. Adapt the collision‑entropy argument to a distribution over small
   circuits rather than a single function.
2. Combine this with the canonical description bound from B‑3 to produce
   a uniform cover for the family.
3. Provide a Lean formalisation tying the entropy estimate to the final
   rectangle count `M`.

---

These clarifications do not close Lemma B, but they chart a concrete
route for completing the proof and for incorporating the results into
subsequent SAT algorithms.
