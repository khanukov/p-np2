## Q1

Not killed by Baker-Gill-Solovay 1975 (https://epubs.siam.org/doi/10.1137/0204037), because the proposed invariant `κ(G_f)` is defined on a consistency graph built from `f`'s actual gate structure / combinatorial encoding, not via oracle queries. The construction does not commute with oracle insertion in an obvious way, so the relativization barrier doesn't trivially apply. **However**, the upper-bound argument ("small circuits induce gate-by-gate Wasserstein contraction") is suspicious: any argument that works by "propagate through the circuit" for an *arbitrary* function in P/poly typically does relativize, because the same propagation works with oracle gates. The author's barrier-evasion claim here is asserted, not demonstrated. Conditional kill possible but not definitive.

## Q2

**Killed by Razborov-Rudich (JCSS 1997)** (https://www.sciencedirect.com/science/article/pii/S0022000097914940), because the claimed "largeness evasion" is incorrect as stated. The natural proofs barrier requires (a) constructivity (computable in P given the truth table), (b) largeness (a non-negligible fraction of functions satisfy the property), and (c) usefulness (excludes small circuits). The invariant `κ(G_f)` is fully determined by `f`'s truth table (since `G_f` is defined from `f|_α not identically 0`, i.e., from the truth table), so it IS a property of the truth table — the author's claim that it "is not a property of the truth table's measure" is a category error: being a function of the truth table is what matters, not being a "measure" on it. If `κ` is computable in time poly(2^n) (which Ollivier curvature on a 3^n-vertex graph is) and large (curvature concentration on random functions is plausible by Erbar-Maas-style concentration), this is a natural property. Razborov-Rudich would then yield: if pseudorandom generators exist in P/poly, no such `κ` can separate.

The Erbar-Maas / Ollivier curvature of a *random* reversible chain on a high-dimensional discrete cube typically concentrates (see e.g. Veysseire 2012, Eldan-Lee-Lehec), suggesting largeness holds for the random-function chain. Hard kill.

## Q3

Conditional kill: Aaronson-Wigderson 2009 (https://www.scottaaronson.com/papers/alg.pdf), applies under the assumption that the Wasserstein-contraction-through-gates argument can be carried out with an oracle gate replaced by an algebraic extension oracle Ã. The transport-geometry inequalities cited (Erbar-Maas) are purely combinatorial/metric and do not break under algebraic oracle insertion, so the upper-bound side likely algebrizes. The author's denial ("uses combinatorial structure, not algebraic extensions") is unsupported — Wasserstein contraction is oblivious to whether a gate is Boolean or algebraic.

## Q4

Not killed by Chen-Jin-Williams JACM 2022 (locality barrier) (https://dl.acm.org/doi/10.1145/3486750) directly, because the proposal isn't claiming a magnification chain from a weak lower bound. However, **the structure of the upper bound is locally-defined** (gate-by-gate contraction → a "local" property of the circuit), and the locality barrier of Chen et al. shows that local lower-bound techniques cannot prove the magnification-style separations being targeted. The MCSP-adjacent framing puts this squarely in the territory addressed by Oliveira-Pich-Santhanam CCC 2019 (https://eccc.weizmann.ac.il/report/2019/075/) and Chen et al. Conditional kill: applies because the gate-by-gate Wasserstein propagation is exactly a "local, gate-wise" argument that the locality barrier forbids.

## Q5

The "circuit-monotone real-valued invariant separating P/poly from NP" is essentially what Mulmuley's GCT program (https://arxiv.org/abs/1110.1351) and any number of previous attempts (formal complexity measures à la Khrapchenko, Karchmer-Wigderson) try to be. No direct equivalence proof, but it occupies the same logical slot: "find a real-valued monotone-under-circuit-composition quantity, large on a small class, small on an NP function." Not a clean equivalence kill.

## Q6

Not found after search. Searches: "Ollivier Ricci curvature circuit complexity", "Ricci curvature Boolean function lower bound", "Wasserstein contraction circuit lower bound", "entropic curvature complexity class". No direct prior attempt found, so no direct refutation.

## Q7

**Killed by combined Razborov-Rudich + the magnification literature**: The invariant produces an `Ω(1/poly(n))` vs `-Ω(1)` gap, which is a *quantitative* gap of polynomial order. The upper bound `κ ≥ 1/s(n)^c` is vacuous unless `s(n)` is small — but for `s(n) = n^{ω(1)}` (super-polynomial), the bound is `1/n^{ω(1)}`, which the lower bound `-Ω(1)` would still beat. So technically the gap argument scales. However, the *real* weakness: the upper bound as stated, `κ ≥ Ω(1/s(n)^c)`, gives nothing for `s(n) = 2^n` (trivial circuits), meaning any function has `κ ≥ 2^{-O(n)}` — but the claimed lower bound is `≤ -Ω(1)`, a constant. So one must check whether ANY function (including those in P) can have `κ ≤ -Ω(1)`. If yes (which is highly plausible — negative Ollivier curvature is generic for tree-like or expander-like graphs, and tons of P-computable functions have expander-like consistency graphs), then the lower-bound side is wrong. **Hard kill on consistency**: explicit easy functions (e.g., parity, majority) likely have negative-curvature consistency graphs too, contradicting the claimed upper bound.

## Q8

Not found after search for "no-go Ricci curvature complexity" / "transport geometry circuit lower bound impossibility". No paper directly says "this route fails." But the meta-paper Aaronson-Wigderson (Q3) and Razborov-Rudich (Q2) together explicitly target exactly this kind of "find an invariant" approach.

## Final verdict

The proposal has at least one hard kill (Q2: natural proofs — the invariant *is* a function of the truth table, the author's denial is a misreading of Razborov-Rudich; largeness plausibly holds by curvature concentration results) and a second hard kill (Q7: explicit easy functions like parity have expander-like consistency graphs and almost certainly fail the claimed positive-curvature upper bound). Q3 and Q4 provide additional conditional kills.

`LIT_RED`

VERDICT: LIT_RED