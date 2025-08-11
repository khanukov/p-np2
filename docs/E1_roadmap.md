> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
# Task E1 Roadmap

Below is a modified plan for obtaining a subexponential SAT algorithm for `ACC⁰∘MCSP`. The text is based on project discussions and is divided into key directions.

---

## 1. Initial facts and terminology

* Circuit `C ∈ ACC⁰_d` of size `poly(N)` and depth `d = O(1)`.
* `T` is the truth table of a purported “small” circuit. Let `N = 2^n`, and set the complexity threshold `s(n) = n^c`.
* `csize(T)` denotes the complexity of the function `T`.
* Goal: decide satisfiability of `\Phi(T)` in time `2^{N - N^{\delta}}` (for some `\delta > 0`) under the constraint `csize(T) \le s(n)`.

---

## 2. Overall strategy

1. **Polynomial representation.** By the Razborov–Smolensky theorems every `ACC⁰` circuit is equivalent to a polynomial of degree `d' = O(\log^{O(1)} N)` over a suitable field.
2. **Input splitting.** Write `N = k + \ell` and express the sum over admissible `T` as a two-dimensional convolution over the left and right parts of the table.
3. **Structural Lemma B.** Cover the set `\mathcal{S}_n = \{T : csize(T) \le n^c\}` with at most `2^{N - N^{\delta}}` rectangles `A_i \times B_i`, each of which can be enumerated quickly.
4. **Meet-in-the-middle.** For each rectangle compute the partial sums `\Sigma_{a\in A_i} (-1)^{Q_{\rm left}(a)}` and `\Sigma_{b\in B_i} (-1)^{Q_{\rm right}(b)}`, then multiply them. The bound on the number of rectangles and fast enumeration yield subexponential complexity.

---

## 3. Subtasks for proving Lemma B

### B‑1. Canonical circuits
Show that every circuit of size `\le n^c` has a canonical description of length `O(n^c\log n)`.  The file `canonical_circuit.lean` now provides a canonicalisation procedure and defines a helper `codeLen` together with the lemma `canonical_desc_length`, recording this bound on an abstract code length.

### B‑2. Table locality
The file `table_locality.lean` defines a notion of locality and proves
a first version of the lemma showing that every circuit of size
`≤ n^c` depends only on at most `n` bits.  A sharper bound `k = O(log n)`
is planned for future work.

### B‑3. Bounding the capacity
Estimate the number of canonical descriptions depending on the first `k` bits and show a bound `\le 2^{(1-\alpha)k}`.  Since there are at most `2^{O(n^{c+1})}` canonical circuits of size `n^c`, taking `k = \Theta(n^{c+1})` leaves only a `2^{(1-\alpha)k}` fraction of all truth tables with the same prefix.

### B‑4. Fast enumeration
Justify enumeration of `A_i` and `B_i` in time `2^{(1-\alpha)k}` and `2^{(1-\alpha)\ell}` respectively.

### B‑5. Constructing the cover
Build a rectangular cover of `\mathcal{S}_n` of size `M \le 2^{N - N^{\delta}}`.
The file `cover2.lean` keeps track of uncovered inputs and recurses via
`firstUncovered`.  The classical lemma `sunflower_exists` (together with
the `RSpread` notion of scattered families) now provides the sunflower
step whenever enough **distinct supports** remain, producing a
positive-dimensional subcube.  A corrected monotonicity lemma for
`RSpread` states that larger parameters imply smaller ones when the base
is positive, and new helper lemmas reformulate the bounds and cover the
trivial case `R = 1`.  The entropy branch continues to use
`exists_coord_entropy_noninc` to split on a coordinate that does not increase
collision entropy.  The numeric counting argument has now been formalised,
but the previously stubbed `coreAgreement` lemma in `Agreement.lean` has
been formalised in full, removing a major gap in the combinatorial
theory.

---

## 4. Development and further steps

* **Theory block.** Deepen the study of items B‑1–B‑3, including connections to existing results on canonical forms and description bounds.
* **Algorithm block.** Implement meet-in-the-middle and fast enumeration (B‑4) for small values of `n`.
* **Combinatorial block.** Develop the covering method (B‑5) via an “address–data” representation or similar constructions.
  The Lean code now defines `buildCover` in `cover2.lean`, tracking uncovered inputs via `firstUncovered` and applying either `sunflower_step` or `exists_coord_entropy_noninc`.
  The cardinal lemma `exists_coord_card_drop` is proven and tests for `sunflower_step` verify its behaviour.
  The lemma `buildCover_pointwiseMono` has now been proved, establishing monochromaticity of
  the constructed cover.  The companion size estimate `buildCover_card_bound` is now proven using the same measure-based recursion.
* **Entropy block.**  The lemma `exists_coord_entropy_noninc` in `entropy.lean`
  shows that some coordinate always yields a restriction with no increase in
  collision entropy, paving the way for a robust splitting strategy.
  A lemma `low_sensitivity_cover` describes how smooth families can be compressed, and the stub `acc_mcsp_sat.lean` sketches the final SAT reduction.
  A minimal `DecisionTree` API with depth and evaluation utilities now also
  includes path extraction with `subcube_of_path` and the lemmas
  `path_to_leaf_length_le_depth` and `leaf_count_le_pow_depth`
  controlling path lengths and leaf counts.
  Together with `low_sensitivity_cover_single` this outlines a decision-tree
  approach to the cover.
* **Utilities.**  The new files `collentropy.lean` and `family_entropy_cover.lean`
  collect single-function entropy facts and package the cover from
  `cover2.lean` as a reusable record.  A lightweight variant
  `CollentropyBasic.lean` now supplies just the numeric bounds needed by
  the SAT prototype, while `Cover/Compute.lean` and `Algorithms/SatCover.lean`
  provide constructive skeletons for cover enumeration and satisfiability
  search.

---

This plan remains the basis for obtaining a subexponential SAT algorithm and is a key step toward proving `P ≠ NP`.
