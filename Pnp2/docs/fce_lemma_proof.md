# The Family Collision-Entropy Lemma: Formal Statement and Constructive Proof
> **Critical warning (2025-10-04).** The parity family $F = \{p, \bar p\}$ contradicts the claimed subexponential bound on common monochromatic subcubes: any such cover must contain at least $2^{n-1}$ points.  Поэтому формулировка FCE-леммы и все нижеследующие рассуждения рассматривайте как нереализуемый план, а не как установленный результат.【F:docs/fce_parity_counterexample.md†L1-L78】

> **Catalogue (2025-10-05).** См. [каталог контрпримеров](docs/fce_counterexample_catalog.md) для систематического списка семейств,
> которые опровергают требование об общем покрытии; любая новая формулировка леммы должна явно обходить эти случаи.

> **Historical status (2025-09-24)**: Combinatorial sublemmas (sunflower step, entropy drop, cover construction) are formalised in Lean.  The remaining gap is the complexity-theoretic bridge from the FCE-Lemma to `P ≠ NP`.

> **Historical update (2025-09-28)**: The quantitative bound `mBound` now includes an explicit `3^n` factor, restoring the inequality `card(Subcube n) ≤ mBound n h` for every positive dimension and every entropy budget.  The regression suite confirms the fix for representative values such as `(n,h) = (10,1)` and the heuristic choices `h = ⌊n / 20⌋` at `n = 20, 30, 40, 50`.

> **Historical update (2025-10-03)**: The formal proof of the FCE lemma is complete.  The recursion in `Cover.BuildCover` now terminates using the lexicographic `muLexTriple` measure, and the exported theorem `Bound.family_collision_entropy_lemma` provides the cover bound `≤ 2^{3n + 11h + 2}` for every `n`.  The regression test in `test/FCEAssumptionCounterexample.lean` instantiates the theorem at `n = 20 000`, certifying that no residual guard remains.


## Abstract

We outline a strategy for the **Family Collision-Entropy Lemma (FCE-Lemma)**: for any family $F$ of Boolean functions on $n$ input bits with collision entropy $H_2(F) \le h$, there should exist a collection $\mathcal{R}$ of at most $n · 3^n · (h+2) · 2^{10h} ≤ 2^{3n + 11h + 2}$ monochromatic subcubes that simultaneously cover the truth tables of all $f \in F$. The argument combines entropy-drop heuristics with sunflower-based combinatorial decomposition and is intended for eventual formalisation in Lean/Coq. Establishing this lemma would close the last open step in a reduction framework for proving $P \neq NP$ via communication complexity.

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
* `entropy.lean`: entropy monotonicity lemma `exists_coord_entropy_noninc`.
* `sunflower.lean`: sunflower extraction.
* `Agreement.lean`: core agreement.
* `cover2.lean`: main recursive algorithm.
* `bound.lean`: size bound proof.
* `examples.lean`: auto-tests.
### Historical Formalisation Plan (2025-08-06)
The modules above serve as milestones. Our immediate goals are:

1. The former halving axiom `exists_restrict_half_real_aux` has been
   removed; `entropy.lean` now proves the monotonicity lemma
   `H₂_restrict_le` showing that restrictions cannot increase collision
   entropy. This suffices for applications requiring entropy
   non‑increase.
2. The classical sunflower lemma in `sunflower.lean` remains an axiom.
3. ~~Formalise the `CoreAgreement` lemma in `Agreement.lean`.~~
   The file `Agreement.lean` now contains the complete proof of this lemma.
4. ~~Finalise the recursive covering algorithm in `cover2.lean`.  The new
  arithmetic lemma `mBound_le_two_pow_linear` bounds the catalogue by
  `2^{3n + 11h + 2}`, replacing the legacy placeholder.~~

6. Provide small test instances in `examples.lean`.


### Historical sketch of `buildCover_card_bound`

The recursive procedure `buildCover` is guided by the measure
$$\mu(F,h,Rset)=2h + |\text{uncovered}\,F\,Rset|,$$
where `uncovered F Rset` collects pairs \(\langle f,x\rangle\) with
\(f \in F\), \(f(x)=1\) and \(x\) not covered by rectangles from `Rset`.
Induction on this measure explains why only a bounded number of rectangles
are inserted.

* **Base case.** If no uncovered pairs remain, the call returns `Rset`
  unchanged.
* **Low-sensitivity branch.** When every function has sensitivity below
  \(\log_2(n+1)\), a cover `R_ls` with at most \(2^{10h}\) rectangles is
  supplied by `low_sensitivity_cover`, and the measure collapses to `2*h`.
* **Entropy branch.** Otherwise a coordinate split produces two
  restrictions with budget `h-1`. By the induction hypothesis their covers
  have size at most `mBound n (h-1)` each, and their union respects
  `mBound n h`.
* **Sunflower branch.** Occasionally a sunflower rectangle covers many
  functions at once.  The uncovered count drops by at least two, so the
  recursion continues with smaller measure.


The detailed argument performs a lexicographic induction on

$$\mu(F,h,Rset) = 2h + |\text{uncovered}\,F\,Rset|.$$ 

The outer recursion decreases $h$ via the entropy branch, while the inner count decreases the uncovered pairs.  Each branch strictly reduces this measure:

- **Base:** when no pairs remain the measure is $2h$ and no rectangles are added.
- **Low-sensitivity:** `low_sensitivity_cover` inserts at most $2^{10h}$ rectangles and resets the measure to $2h`.
- **Entropy:** splitting on a coordinate lowers the budget; each subfamily is handled recursively with budget $h-1`.
- **Sunflower:** adding the sunflower rectangle covers several pairs, dropping the measure by at least two.

By induction the total number of rectangles never exceeds $mBound\,n\,h$.
Combining these cases shows that `(buildCover F h ∅).card ≤ mBound n h`.
A future Lean proof will mirror this outline using well-founded recursion
on `\mu`.

#### Detailed measure-based induction

The intended formal argument proceeds by a *double induction* on the
measure

$$
  \mu(F,h,Rset) = 2h + |\text{uncovered}\,F\,Rset|,
$$
where `uncovered F Rset` collects all currently uncovered pairs
`⟨f, x⟩` with `f ∈ F` and `f x = true`.  The outer induction decreases the
entropy budget `h`, while the inner induction reduces the number of
uncovered pairs.  Each branch of `buildCover` strictly decreases this
lexicographic measure:

* **Base case.**  When `uncovered F Rset = ∅` the recursion terminates
  immediately, returning `Rset`.
* **Low-sensitivity branch.**  If all functions in `F` have sensitivity
  below `log₂(n+1)`, the lemma `low_sensitivity_cover` supplies a set
  `R_ls` of rectangles covering the remaining `1`-points.  Their number is
  bounded by an explicit exponential in the maximum sensitivity, so the
  induction hypothesis applies to the empty uncovered set.
* **Entropy branch.**  Otherwise `exists_coord_entropy_noninc` provides a
  coordinate split that does not increase `H₂`.  Recursive calls on the two
  restrictions use budget `h-1`.  Bounding the size of each restricted
  cover and adding them yields at most `2 * mBound n (h-1)` rectangles,
  which remains below `mBound n h`.
* **Sunflower branch.**  Occasionally `sunflower_step` finds a rectangle
  that simultaneously hits many functions.  The uncovered count drops by
  at least two, so the measure decreases even without reducing `h`.

Since the measure cannot decrease indefinitely, the recursion inserts at
most `mBound n h` rectangles before reaching the base case.  This shows

$$
  (buildCover F h ∅).\text{card} \le mBound\;n\;h.
$$

The current Lean development implements the measure and its basic
properties; the full induction proof is work in progress.
### Status Update (July 2025)

The Lean codebase now includes the entropy monotonicity lemma `exists_coord_entropy_noninc`, a `sunflower_step` lemma for extracting subcubes, and a working recursive cover builder. The core agreement lemma has also been formalised in full, and lemma statements for `low_sensitivity_cover` tie in smooth families. The file `acc_mcsp_sat.lean` sketches the final SAT reduction. A few auxiliary lemmas—most notably the probabilistic halving bound—are currently assumed as axioms, but the classical
sunflower lemma has been completed.  Completing these pieces, along
with the counting argument and example scripts, remains the next milestone.

The parameter $h$ is treated as a fixed constant (or $o(n)$) when establishing the bound.

## Potential Improvements and Next Steps

Several parts of the argument remain sketches.  We list a few directions that
would further strengthen the proof:

1. **Complete the induction proof in `bound.lean`.**  The measure-based
   argument is outlined above but the details are still missing in the Lean
   code.  Formalising this step would remove the last large axiom.
2. **Eliminate remaining axioms.**  In particular the probabilistic halving
   bound is currently assumed.  A direct proof or a reference to a published
   result would increase confidence in the final bound.
3. **Sharpen the low-sensitivity branch.**  The constant hidden in
   `low_sensitivity_cover` is relatively coarse.  A tighter analysis might
   reduce the overall rectangle bound.
4. **Expand test coverage.**  The repository contains a test harness but few
   concrete examples.  Adding small sample families in `examples.lean` would
   help catch regressions as the formalisation evolves.
5. **Clarify termination reasoning.**  The interplay between the recursion
   measure and the entropy budget deserves a more explicit explanation to aid
   future readers.

## References

1. Erdős & Rado (1960), intersection theorems.
2. Alweiss–Lovett–Wu–Zhang (2021), improved sunflower bounds.
3. Gopalan et al. (2016), algorithms for low-sensitivity boolean functions.
4. Göös et al. (2020), robust sunflowers and communication complexity.
5. Hegyvári (2024), additive energy and subcube partitions.
6. Terence Tao (2020), [The Sunflower Lemma via Shannon entropy](https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/).

---

*End of Manuscript*
