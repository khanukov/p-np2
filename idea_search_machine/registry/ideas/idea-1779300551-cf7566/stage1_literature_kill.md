## Q1

Not killed by Baker-Gill-Solovay 1975, because the proposed route explicitly uses bounded-arithmetic unprovability anchored to a specific combinatorial design and a non-black-box Goldreich-Levin reduction. The witnessing-theorem machinery in `VNC¹ + dWPHP(PV)` is not known to relativize uniformly (Cook-Nguyen 2010 formalizations operate on bit-graph encodings, not oracle gates). However, the proposal does not explicitly construct a relativizing barrier breaker; it merely asserts non-relativization. So BGS (https://epubs.siam.org/doi/10.1137/0204037) does not directly kill, but it is not affirmatively defeated either.

## Q2

**Conditional kill: Razborov-Rudich, "Natural Proofs", JCSS 1997 (https://www.sciencedirect.com/science/article/pii/S0022000097914940), applies under** the assumption that the witnessing-theorem extraction from `dWPHP(PV)` yields a `P/poly`-constructive property. The proposal claims measure-zero (defeating largeness) and Σ²-hardness of membership (defeating constructivity). But Rudich-Razborov's barrier is about properties of the *truth table* — and Pich-Santhanam 2019 (https://ieeexplore.ieee.org/document/8948687) explicitly note that bounded-arithmetic-based lower bounds, when they extract circuits, tend to yield *natural-like* properties unless one carefully blocks constructivity. The Σ²-hardness claim for membership is unsupported in the proposal — Atserias-Müller 2020 (https://dl.acm.org/doi/10.1145/3409472) shows automating Resolution is NP-hard but this does not transfer to Σ²-hardness of the relevant proof-search instance. **Conditional kill** pending a genuine non-constructivity proof.

## Q3

**Killed by Aaronson-Wigderson, "Algebrization", TOCT 2009 (https://dl.acm.org/doi/10.1145/1490270.1490272), because** the inner-product `⟨r, f(x|S_i)⟩` of Goldreich-Levin is precisely the canonical example handled by algebrization: it extends naturally to a low-degree polynomial over GF(2) (the inner product IS a degree-2 polynomial). The proposal's parenthetical hand-wave ("Aaronson-Wigderson's algebraic oracle framework treats ⟨·,·⟩ as inner-product which their separation explicitly handles only over restricted query patterns") is false — A-W Section 5 explicitly shows GL-style hardcore arguments algebrize, and the NP vs P/poly question algebrizes only with both ~A and A oracles, which the proposed reduction provides since GL is a black-box reduction with algebraic structure. The claim of non-algebrization is unsupported and contradicted by A-W's treatment of inner-product oracles.

## Q4

**Conditional kill: Chen-Jin-Williams-Wu et al., "Beyond Natural Proofs: Hardness Magnification and Locality" JACM 2022 (https://dl.acm.org/doi/10.1145/3538391) and Oliveira-Pich-Santhanam CCC 2019 (https://drops.dagstuhl.de/opus/volltexte/2019/10849/), apply under** the interpretation that NW-EVAL is a "structured / sparse" NP problem whose hard instances have a specific combinatorial template. The locality barrier shows that lower bounds proved via local reductions against structured NP languages cannot exceed the magnification threshold. The witnessing-theorem extraction is local in the bounded-arithmetic sense (Σ^B_1 definability ≈ AC⁰-Frege-like locality). Conditional kill pending verification that the NW-design evaluator falls in the OPS19 sparse-language regime.

## Q5

The proposed lower bound `NW-EVAL ∉ P/poly` is equivalent to `NP ⊄ P/poly` modulo polynomial padding (NW-EVAL is in NP, and the proposal asserts it has no poly circuits — this *is* NP vs P/poly). Karp-Lipton (https://dl.acm.org/doi/10.1145/800141.804678) shows this collapses PH. Not killed in the sense that it's not a refutation, but the proposal has reduced one open problem to itself. **Effective kill** under the equivalence-to-open-problem criterion: the proposal does not produce a *new* attack; it restates `NP ⊄ P/poly` as `NW-EVAL ∉ P/poly`.

## Q6

**Killed by Pich-Santhanam, "Why are Proof Complexity Lower Bounds Hard?", FOCS 2019 (https://ieeexplore.ieee.org/document/8948687), because** they show that proving super-polynomial lower bounds for explicit NP languages via unprovability in theories at least as strong as `VNC¹ + dWPHP(PV)` *itself* requires lower bounds against the theory's own propositional proof system (quasi-polynomial Frege / `G_i`). The proposal invokes the very theorem that demonstrates its own circularity: to get the unprovability certificate, one needs lower bounds against Jeřábek's `WF` / `G*_1` proof systems, which are exactly as hard as the original circuit lower bound. Section 4 of Pich-Santhanam formalizes this as a "feasible incompleteness barrier."

## Q7

**Killed by Krajíček-Pudlák, "Some Consequences of Cryptographical Conjectures for S^1_2 and EF" Information and Computation 1998 (https://www.sciencedirect.com/science/article/pii/S0890540198927307) and Cook-Krajíček JSL 2007 (https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/consequences-of-the-provability-of-np-pposy/),** because the proposal's witnessing-transfer step only yields a *feasibly-constructible* circuit family contradiction, which Cook-Krajíček show requires the theory to prove `NP ⊆ P/poly` in a uniform Σ^B_1 sense. The dWPHP(PV) witnessing gives PLS-style search problems, but the resulting lower bounds are known to apply only to *bounded-depth* or *restricted-Frege* circuits, not full P/poly. This is below the magnification threshold of OPS19.

## Q8

**Killed by Razborov, "Pseudorandom generators hard for k-DNF resolution and polynomial calculus resolution", Annals of Math 2015 (https://annals.math.princeton.edu/2015/181-2/p01) and Krajíček's "Forcing with Random Variables" 2011 (Cambridge LMS 382),** which together establish that NW-generator-based hardness arguments inside bounded arithmetic recover only restricted-proof-system lower bounds, not P/poly. More directly, **Pich, "Logical strength of complexity theory and a formalization of the PCP theorem in bounded arithmetic", LMCS 2015 (https://lmcs.episciences.org/1620)** and **Müller-Pich, "Feasibly constructive proofs of succinct weak circuit lower bounds", APAL 2020 (https://www.sciencedirect.com/science/article/pii/S0168007220300658)** explicitly state that the "unprovability-to-circuit-lower-bound" route via VNC¹/VPV-style theories with dWPHP cannot exceed weak/succinct regimes — they prove super-polynomial lower bounds *only* against models like sub-exponential circuits for E^NP, not for NP. This is a direct negative result for the proposed route's strength.

## Final verdict

Multiple hard kills: Q3 (algebrization of inner-product GL hardcore is well-documented), Q5 (the lower bound is equivalent to the open problem itself, not a new attack), Q6 (Pich-Santhanam's feasible incompleteness barrier is invoked by the proposal's own machinery), and Q8 (Müller-Pich and Pich explicitly bound the strength of this exact route below P/poly for NP). The proposal's non-algebrization claim is factually incorrect, and its proof-theoretic machinery is precisely the machinery whose limits have been mapped.

`LIT_RED`

```
VERDICT: LIT_RED
```