## Q1

Not killed by Baker-Gill-Solovay 1975, because the proposed approach uses topological entropy of explicitly constructed SFTs — a non-relativizing invariant that depends on the specific tile rules, not on oracle access. The SFT construction via Hochman–Meyerovitch is intrinsically non-relativizing (it depends on concrete TM-to-tile encodings). https://www.ams.org/journals/proc/1975-26-04/

## Q2

Conditional kill: Razborov-Rudich, *Natural Proofs*, JCSS 1997, applies under the assumption that `top_entropy_modulus` is (a) constructive (computable in time 2^O(n) given the truth table) and (b) "large" (holds for a constant fraction of languages). The proposal claims it is "not a natural property," but no argument is given for why the entropy-modulus invariant fails *largeness* or *constructivity*. In fact, the SFT construction is uniform and polynomial-time-checkable on local rules, which makes the *constructivity* condition plausibly satisfied. Without an explicit demonstration that either largeness or constructivity fails, the natural-proofs barrier applies. https://www.sciencedirect.com/science/article/pii/S0022000097914940

## Q3

Not killed by Aaronson-Wigderson 2009, because algebrization concerns oracle access to low-degree extensions, and this proposal does not use oracles or arithmetization. https://www.scottaaronson.com/papers/alg.pdf

## Q4

Conditional kill: Chen-Jin-Williams-Wu, *Hardness magnification and locality barriers*, and OPS19 (Oliveira-Pich-Santhanam, CCC 2019), apply under the assumption that the modulus-of-entropy invariant is "local" in the sense of depending on bounded-window behavior of the SFT. Aubrun–Sablik simulations are inherently local (finite-window tile rules), and the entropy is defined as a limit of finite-window pattern counts — this is structurally the kind of local invariant that locality barriers target. The proposal's claim of "not a circuit-counting argument" does not address whether the underlying argument reduces to local pattern counting, which it almost certainly does (entropy = lim (1/n²) log N(n)). https://eccc.weizmann.ac.il/report/2019/048/

## Q5

Conditional kill: The entropy approximation rate of an SFT encoding a language L is equivalent to the time-bounded Kolmogorov complexity / pattern-counting complexity of L (#P-style counting of valid n×n tile configurations). Separating P from NP via approximation rates of #P-style counting functions is equivalent to known open problems about #P vs FP approximation (Stockmeyer's theorem and consequences). This makes the entropy-modulus separation equivalent to, not easier than, existing open lower-bound questions. Reference: Stockmeyer, *The complexity of approximate counting*, STOC 1983.

## Q6

Not found after search. No direct refutation of "entropy modulus of SFT encoding ⇒ P vs NP" exists in the literature, because the idea is too specific/novel to have been explicitly refuted. Searches: Google Scholar "SFT entropy P NP separation", "topological entropy complexity class separation", "Hochman-Meyerovitch complexity lower bound".

## Q7

Killed by the general principle established in Hochman, *On the dynamics and recursive properties of multidimensional symbolic systems*, Inventiones 176 (2009): the entropies realizable by SFTs are exactly the Π₀₁ (right-r.e.) reals, which is a *recursion-theoretic* classification at the level of the arithmetic hierarchy — far coarser than the P/NP distinction. The Hochman–Meyerovitch construction has no known refinement that distinguishes between polynomial-time and NP-time within the Π₀₁ class; the construction's "quantitative control" is at the level of computability, not feasibility. The proposal's claim that the modulus "directly inherits the time complexity of deciding L" is not actually established by Hochman–Meyerovitch — their theorem is about computability, not complexity. https://link.springer.com/article/10.1007/s00222-008-0161-7

This is a hard kill on the load-bearing step: the cited theorems do not provide polynomial-vs-superpolynomial modulus distinctions, only computable-vs-uncomputable.

## Q8

Killed by Jeandel-Vanier, *Turing degrees of multidimensional SFTs*, TCS 505 (2013): they show the Turing degrees realizable by SFT-invariants are exactly the Π₀₁ degrees, and explicitly note that *finer* (sub-recursive, complexity-theoretic) distinctions are not achievable by these simulation techniques. The "uniform construction" route is shown to top out at the computability level. The paper's framework directly indicates that the polynomial-vs-superpolynomial modulus refinement the proposal needs is not in the reach of the simulation method. https://www.sciencedirect.com/science/article/pii/S0304397513006853

Additionally, Pavlov-Schraudner and follow-up work on computable entropy approximation rates show that the rate of approximation can be made arbitrarily slow within the Π₀₁ class but is not naturally tied to a feasible-computation hierarchy — the constructions are too coarse.

## Final verdict

The load-bearing step (Q7) is a hard kill: Hochman–Meyerovitch and Aubrun–Sablik give *computability*-level control on entropy, not *complexity*-level control. The claim that "f_L(k) = O(1/poly(k)) with constants depending on t" for L ∈ TIME(t(n)) is not in either paper and is not extractable from their constructions — their constructions have exponential/tower blowups in tile alphabet size relative to TM simulation depth, which destroys any polynomial modulus claim. Jeandel-Vanier (Q8) confirms that the simulation framework operates at the Turing-degree level, not the complexity-class level. Natural proofs (Q2) and locality barriers (Q4) provide additional conditional kills.

LIT_RED

VERDICT: LIT_RED