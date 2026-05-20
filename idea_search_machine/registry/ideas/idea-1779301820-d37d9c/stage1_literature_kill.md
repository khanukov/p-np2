## Q1

**Is this relativizing?**

Conditional kill: Baker-Gill-Solovay, "Relativizations of the P =? NP Question," SIAM J. Comput. 4 (1975), https://epubs.siam.org/doi/10.1137/0204037, applies under the assumption that the proposed argument does not exploit any non-relativizing property of the circuit model.

The proposed mechanism enumerates `C_n` over all `A^{n²}` inputs to count `p_𝒮(n)`. This counting-by-enumeration step uses the circuit only as a black-box decider — exactly the relativizing pattern. The entropy bound `h(𝒮) = lim (1/n²) log p_𝒮(n)` depends only on the *cardinality* of the accepting set, not on the circuit's internal structure. An oracle A computing tiling-extension yields a P^A algorithm whose "circuit family" trivially decides L_𝒮 in polynomial size with oracle gates, and the entropy approximation argument would equally rule it out — yet relative to a suitable oracle, P^A = NP^A. Hence the argument as stated relativizes and is killed.

## Q2

**Is this natural?**

Killed by Razborov–Rudich, "Natural Proofs," JCSS 55 (1997), https://www.sciencedirect.com/science/article/pii/S0022000097914940, because the property "patch-extendability count `p_𝒮(n)` has entropy-rate matching a specified right-r.e. real" is (i) **constructive** — given the truth table, one counts accepting inputs and tests an entropy approximant in time `2^{O(n²)}` (polynomial in truth-table size), (ii) **large** — a random Boolean function on `n²` bits accepts `≈ 2^{n²-1}` inputs, giving entropy ≈ log|A|, which generically *exceeds* any subcritical target entropy, so a constant fraction of functions exhibit the same entropy-rate witness. Under standard cryptographic assumptions (subexponentially hard PRFs in P/poly), such a natural property cannot exist. The dynamical packaging does not remove the underlying combinatorial counting property.

## Q3

**Is this algebrizing?**

Conditional kill: Aaronson–Wigderson, "Algebrization: A New Barrier in Complexity Theory," ACM TOCT 1 (2009), https://dl.acm.org/doi/10.1145/1490270.1490272, applies because the argument additionally has no obvious use of low-degree extension, multilinear structure, or PCP-style algebraic encoding. The circuit-to-counting reduction goes through black-box enumeration, which both relativizes and algebrizes (any algebraic oracle extension preserves the counting argument). Conditional because algebrization is strictly a stronger barrier than relativization and the proposal makes no algebraic claim — but neither does it escape the barrier.

## Q4

**Is this a known hardness-magnification dead end?**

Killed by Chen, Jin, Williams, "Sharp Threshold Results for Computational Complexity," and the locality-barrier line: Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality," JACM 69(4) 2022, https://dl.acm.org/doi/10.1145/3538391, because the proposed lower bound is `n^k` (super-polynomial only in the trivial sense of arbitrary fixed k) against general circuits for an NP-complete language — exactly the regime where magnification frontiers live, but the *mechanism* (entropy approximation from enumeration) is a **local / black-box** argument that the locality barrier shows cannot cross the threshold. Specifically, the counting step `|L_𝒮 ∩ A^{n×n}|` is a local statistic of the circuit (an additive function of indicator outputs), and Chen et al. show such local arguments cannot yield even mildly super-linear lower bounds beyond known ones.

## Q5

**Is this equivalent to a known open lower bound?**

Conditional kill: The statement "NP-complete language L has no `n^k`-size circuit for every k" is literally `NP ⊄ P/poly`, an open problem since Karp–Lipton 1980, https://dl.acm.org/doi/10.1145/800141.804678. So the proposed theorem statement is equivalent to a notoriously open problem (this is by design — that's the thesis). Not killed in the sense of refuted, but it confirms the proposal claims to resolve `NP vs P/poly`, raising the bar to "complete proof, not sketch."

## Q6

**Is this already proved impossible?**

Not killed by direct refutation: no paper proves NP ⊆ P/poly. Not found after search for "Hochman–Meyerovitch entropy circuit lower bound impossibility."

However, the *technique* (enumerating accepting inputs of a circuit to extract entropy) is essentially a `#P`-style oracle: counting accepting inputs of a poly-size circuit is `#P`-complete (Valiant 1979, https://www.sciencedirect.com/science/article/pii/0304397579900446), and the entropy `(1/n²) log p_𝒮(n)` reduces to such counting. So the "fast approximation of h(𝒮)" derived from a poly circuit is no faster than `#P` in general — and there is no known reason `#P` computations cannot approximate right-r.e. reals at exponential accuracy if the right-r.e. real happens to be in `#P/poly`. The proposed contradiction does not follow.

## Q7

**Is this already known to be too weak?**

Not killed: the target `n^k` for every k against general circuits is *above* the magnification threshold (which would be `n^{1+ε}` for MCSP-style problems), so weakness is not the issue. The issue is strength: it is too strong to be achievable by the proposed black-box method (see Q1, Q2, Q4).

## Q8

**Is there a paper that directly says "this type of route does not work"?**

Killed by Hochman, "On the dynamics and recursive properties of multidimensional symbolic systems," Invent. Math. 176 (2009), https://link.springer.com/article/10.1007/s00222-008-0161-7, read against itself: the quantitative factor-map entropy inequality bounds **entropy of the factor ≤ entropy of the cover plus fiber entropy**, but says nothing about lower-bounding the *computational complexity* of deciding patch extendability — only about the *recursion-theoretic* complexity of approximating the entropy. The slow-approximation lower bound in Hochman–Meyerovitch (Annals 2011, https://annals.math.princeton.edu/2011/173-4/p06) is a statement about **right-r.e. reals being non-recursive in general**, i.e., undecidability, not non-poly-time-decidability. Translating "h is not computable" to "patch-extendability is not in P/poly" requires that *every* poly-size circuit family yield a poly-time-computable approximant of h — but this conflates uniform recursion-theoretic computability with non-uniform circuit complexity. The Aubrun–Sablik / Durand–Romashchenko–Shen simulation theorems (https://arxiv.org/abs/1204.4988, https://arxiv.org/abs/1011.6580) are explicitly *recursion-theoretic*: they produce **Turing-degree** preservation, not circuit-size preservation. There is no quantitative version controlling non-uniform circuit size, and the proposal does not supply one.

Additionally, Allender et al., "Power from Random Strings," SIAM J. Comput. 35 (2006), https://epubs.siam.org/doi/10.1137/050628994, and the broader resource-bounded Kolmogorov complexity literature, show that recursion-theoretic uncomputability arguments systematically fail to transfer to circuit lower bounds without an additional, currently-missing ingredient.

## Final verdict

The proposal is killed on multiple independent grounds: (Q1) it relativizes — the circuit is used as a black box for counting; (Q2) the entropy-rate property is constructive and large, so it is a natural property in the Razborov–Rudich sense; (Q4) the local/enumerative mechanism falls inside the locality barrier for magnification; (Q8) the dynamical theorems cited are recursion-theoretic and do not have the quantitative non-uniform-circuit versions the argument needs — this is the fatal gap. The "factor-map entropy inequality" controls entropy of dynamical factors, not circuit sizes; the proposal silently identifies "computable approximation of h" with "poly-size-circuit-computable approximation of h," which is exactly the relativization/naturalization barrier in disguise.

LIT_RED

```
VERDICT: LIT_RED
```