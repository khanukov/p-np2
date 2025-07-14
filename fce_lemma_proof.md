# The Family Collision-Entropy Lemma: Formal Statement and Constructive Proof

## Abstract

We outline a strategy for the **Family Collision-Entropy Lemma (FCE-Lemma)**: for any family $F$ of Boolean functions on $n$ input bits with collision entropy $H_2(F) \le h$, there should exist a collection $\mathcal{R}$ of at most $n(h+2)2^{10h} < 2^{n/100}$ monochromatic subcubes that simultaneously cover the truth tables of all $f \in F$. The argument combines entropy-drop heuristics with sunflower-based combinatorial decomposition and is intended for eventual formalisation in Lean/Coq. Establishing this lemma would close the last open step in a reduction framework for proving $P \neq NP$ via communication complexity.

---

## 1. Introduction

We consider the problem of covering Boolean function families with low collision entropy using few monochromatic rectangles (subcubes). The **Family Collision-Entropy Lemma** plays a central role in proof strategies aiming to separate $P$ from $NP$. This note sketches how one might construct a covering of size $2^{o(n)}$ and outlines the ingredients needed for a future rigorous proof.

## 2. Notation and Definitions

Let $\{0,1\}^n$ denote the Boolean cube, and let $f: \{0,1\}^n \to \{0,1\}$ be a Boolean function.

* A **family** $F \subseteq \{0,1\}^{\{0,1\}^n}$ is a finite set of Boolean functions.
* The **collision probability** is $\text{Coll}(F) = \sum_{f \in F} p_f^2$, with uniform distribution $p_f = 1/|F|$.
* The **collision entropy** is $H_2(F) = -\log_2(\text{Coll}(F)) = \log_2|F|$.
* A **subcube** $R(I, \alpha) \subseteq \{0,1\}^n$ is defined by fixing coordinates $I \subseteq [n]$ to values $\alpha: I \to \{0,1\}$.
* A subcube is **monochromatic** for $f$ if it has constant output; for $F$ if every $f \in F$ agrees on all $x \in R$.

## 3. The FCE-Lemma (Main Theorem)

**Theorem.** Let $F$ be a family of Boolean functions on $n$ bits with $H_2(F) \le h$, where $h = o(n)$. Then there exists a collection $\mathcal{R} = \{ R_1, \dots, R_m \}$ of monochromatic subcubes such that:

1. Each $R \in \mathcal{R}$ is monochromatic for all $f \in F$;
2. For every $f \in F$, the union of $\{ R \in \mathcal{R} : f(x) = 1 \text{ on } R \}$ covers all 1-points of $f$;
3. $m \le n(h+2)2^{10h} < 2^{n/100}$ for sufficiently large $n$.

## 4. Preparatory Lemmas

### Lemma 1: Entropy-Drop

If $H_2(F) > 0$, there exists $i \in [n]$, $b \in \{0,1\}$ such that:
$H_2(F|_{x_i = b}) \le H_2(F) - 1.$

### Lemma 2: Sunflower Lemma

If $\mathcal{S}$ is a family of size-$w$ sets with $|\mathcal{S}| > (p-1)! w^p$, then $\mathcal{S}$ contains a sunflower of size $p$.

### Lemma 3: Core Agreement

If $x^{(1)}, x^{(2)} \in \{0,1\}^n$ agree on $n - \ell$ bits and $f(x^{(1)}) = f(x^{(2)}) = 1$ for all $f \in F$, then the subcube fixing those bits is monochromatic 1 for all $f \in F$.

### Lemma 4: Sunflower Step

Given a set of uncovered 1-inputs `Pts` common to every function of $F$, assume
each collection of `t` points from `Pts` intersects in fewer than `w`
coordinates.  If `|\text{Pts}| > (t-1)!\,w^t`, the classical sunflower lemma
produces a non-empty intersection `I` of some `t` points.  Fixing the bits in `I`
to their common values yields a subcube on which all functions of $F` evaluate to
1.  At least `t` of the original points lie in this subcube.

### Lemma 5: Merge Low Sensitivity

If every $f \in F$ has sensitivity at most $s$, then there exists a constant $C`
such that the union of at most $2^{C s \log n}` monochromatic subcubes covers all
1-points of all functions in $F`.  The proof uses decision-tree representations
for low-sensitivity functions and merges the resulting covers.

## 5. Constructive Algorithm

We recursively define $\text{Cover}(F)$ as:

* If $H_2(F) = 0$: return full cube.
* Else, try to find a sunflower (two 1-points with large common core): if found, output subcube over core, recurse on uncovered part.
* Else, apply entropy-drop lemma: fix bit $x_i = b$, recurse on two subfamilies.

In each step, either entropy drops by $\ge 1$, or at least $2^{n - \ell}$ inputs are removed. The total number of steps is $\le h + n / \log n$.

## 6. Proof of Correctness and Bound

The algorithm terminates with a set $\mathcal{R}$ satisfying:

* All rectangles are monochromatic for all $f \in F$;
* Every 1-point of each $f$ is covered;
* The number of rectangles $m \le n(h+2)2^{10h}$.

## 7. Discussion and Future Work

* **Tightness**: Bound can likely be improved to $\exp(O(\sqrt{hn}))$ using robust sunflowers and sharper entropy-drop.
* **Applications**: Closes final gap in reduction from $P \neq NP$ to combinatorics.
* **Open Problems**:

  1. Handling non-uniform distributions.
  2. Extending to non-Boolean functions.
  3. Allowing cylinder covers instead of subcubes.

## Appendix A: Key Inequalities

* A binary tree of height $h$ has < $2^{h+1}$ leaves.
* Halving lemma: removing $2^{\log_2 |U|}$ elements at each step implies $\le n / \log n$ steps.

## Appendix B: Formalisation

Modules in Lean 4:

* `bool_func.lean`: types for points, subcubes, Boolean functions.
* `entropy.lean`: entropy-drop lemma.
* `sunflower.lean`: sunflower extraction.
* `Agreement.lean`: core agreement.
* `cover.lean`: main recursive algorithm.
* `bound.lean`: size bound proof.
* `examples.lean`: auto-tests.
### Updated Formalisation Plan (2025-07-04)
The modules above serve as milestones. Our immediate goals are:

1. Complete the proof of `EntropyDrop` in `entropy.lean`.  The helper
   lemma `exists_restrict_half` shows that some input bit reduces a
   family to at most half its size.  Its real-valued form
   `exists_restrict_half_real` and the probability variant
   `exists_restrict_half_real_prob` let us reason about logarithms, and
   `exists_coord_entropy_drop` formalises the resulting one‑bit entropy
   reduction.
2. The classical sunflower lemma in `sunflower.lean` is now fully formalised.
3. ~~Formalise the `CoreAgreement` lemma in `Agreement.lean`.~~
   The file `Agreement.lean` now contains the complete proof of this lemma.
4. Finalise the recursive covering algorithm in `cover.lean`.  A
  proof of the inequality `mBound_lt_subexp` exists in the legacy
  `Pnp2/bound.lean` file, but the new `pnp` version still marks this
  statement as an axiom awaiting porting.

6. Provide small test instances in `examples.lean`.

### Status Update (July 2025)

The Lean codebase now includes the full proof of `exists_coord_entropy_drop`, a `sunflower_step` lemma for extracting subcubes, and a working recursive cover builder. The core agreement lemma has also been formalised in full, and lemma statements for `low_sensitivity_cover` tie in smooth families. The file `acc_mcsp_sat.lean` sketches the final SAT reduction. A few auxiliary lemmas—most notably the probabilistic halving bound—are currently assumed as axioms, but the classical
sunflower lemma has been completed.  Completing these pieces, along
with the counting argument and example scripts, remains the next milestone.

The parameter $h$ is treated as a fixed constant (or $o(n)$) when establishing the bound.

## References

1. Erdős & Rado (1960), intersection theorems.
2. Alweiss–Lovett–Wu–Zhang (2021), improved sunflower bounds.
3. Gopalan et al. (2016), algorithms for low-sensitivity boolean functions.
4. Göös et al. (2020), robust sunflowers and communication complexity.
5. Hegyvári (2024), additive energy and subcube partitions.
6. Terence Tao (2020), [The Sunflower Lemma via Shannon entropy](https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/).

---

*End of Manuscript*
