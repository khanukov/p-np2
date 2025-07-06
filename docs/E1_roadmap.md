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
The file `cover.lean` keeps track of uncovered inputs and recurses via
`firstUncovered`.  The classical lemma `sunflower_exists` (together with
the `RSpread` notion of scattered families) now provides the sunflower
step whenever enough **distinct supports** remain, producing a
positive-dimensional subcube.  The entropy branch continues to use
`exists_coord_entropy_drop` to split on a coordinate that decreases
collision entropy.  The numeric counting argument is still incomplete,
but the previously stubbed `coreAgreement` lemma in `Agreement.lean` has
been formalised in full, removing a major gap in the combinatorial
theory.

---

## 4. Development and further steps

* **Theory block.** Deepen the study of items B‑1–B‑3, including connections to existing results on canonical forms and description bounds.
* **Algorithm block.** Implement meet-in-the-middle and fast enumeration (B‑4) for small values of `n`.
* **Combinatorial block.** Develop the covering method (B‑5) via an “address–data” representation or similar constructions.
  The Lean code now defines `buildCover` in `cover.lean`, tracking uncovered inputs and applying either `sunflower_step` or `exists_coord_entropy_drop`.  Completeness proofs and precise counts are still pending.
* **Entropy block.**  The new lemma `exists_coord_entropy_drop` in `entropy.lean`
  shows that some coordinate always cuts collision entropy by at least one bit,
  paving the way for a robust splitting strategy.
  A lemma `low_sensitivity_cover` describes how smooth families can be compressed, and the stub `acc_mcsp_sat.lean` sketches the final SAT reduction.

---

This plan remains the basis for obtaining a subexponential SAT algorithm and is a key step toward proving `P ≠ NP`.
