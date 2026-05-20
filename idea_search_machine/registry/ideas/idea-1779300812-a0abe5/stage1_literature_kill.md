## Q1

Not killed by Baker-Gill-Solovay 1975 (https://epubs.siam.org/doi/10.1137/0204037), because the proposed mechanism explicitly invokes the algebraic structure of Goldreich's `P5` predicate over GF(2), and Cook-style propositional translations of bounded-arithmetic proofs are known to be non-relativizing (cf. Arora-Impagliazzo-Vazirani 1992 critique of relativization, and the fact that natural-proofs-style barriers and cryptographic hardness reductions go through non-relativizing techniques). The argument routes through specific Σ^b_1 witnessing inside `VNP_2`, which is not preserved by oracle extensions.

## Q2

Conditional kill: Razborov-Rudich JCSS 1997 (https://www.sciencedirect.com/science/article/pii/S0022000097914940), applies under the assumption that the hardness property used is "natural" in the R-R sense. The proposal explicitly claims to evade naturalness by (a) using a non-constructive property (deciding consistency of a fragment of bounded arithmetic relative to a crypto assumption is not in P/poly) and (b) being non-large (singling out `MCSP*`-deciders). On its face this evades naturalness — *however*, this same evasion strategy has been attempted many times (Razborov 1995 "Unprovability of lower bounds in weak theories", Rudich 1997) and the bounded-arithmetic-internalized version was already considered. Not a direct kill, but the burden of demonstrating non-naturalness rigorously is high.

## Q3

Not killed by Aaronson-Wigderson 2009 (https://www.scottaaronson.com/papers/alg.pdf), because the route uses propositional proof complexity and specific algebraic structure of `P5` (degree-5 over GF(2)) rather than low-degree algebraic extensions of oracles. Algebrization concerns arithmetization of Boolean formulas; the bounded-arithmetic witnessing argument does not arithmetize circuits in the AW sense. However, Aaronson-Wigderson Section 6 shows that even with arithmetization, NP ⊄ P/poly requires non-algebrizing techniques — so the proposal must show its techniques are non-algebrizing, which is plausible but not demonstrated.

## Q4

**Killed by Chen-Jin-Williams "Sharp threshold results for computational complexity" STOC 2020 / Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam "Beyond natural proofs: hardness magnification and locality" JACM 2022** (https://dl.acm.org/doi/10.1145/3538391 ; ECCC TR19-118), because the proposal relies on transferring a circuit lower bound for `MCSP*` (a padded self-reducible MCSP variant) to NP-completeness via Hirahara-style non-black-box reductions, which is *exactly* the hardness-magnification regime. The CHOPRS "locality barrier" shows that *any* lower bound proved via current local/natural techniques against MCSP-like problems at the magnification threshold cannot be extended past the threshold without overcoming the locality barrier. The proposal's "TransferLemma via Hirahara's reduction" inherits this barrier: the EF-witnessing argument produces lower bounds, but the magnification step is precisely where locality bites, and nothing in the proof-complexity machinery addresses it. **This is a hard kill on stage 3 of the transfer chain.**

## Q5

Conditional kill: The proposal is essentially equivalent to proving super-polynomial EF lower bounds for τ_{P5,n} (Krajicek's NW-generator tautologies), which is a *major open problem* — see Krajicek, *Proof Complexity* (Cambridge UP, 2019), Chapter 19, and Razborov "Pseudorandom generators hard for k-DNF resolution and polynomial calculus" 2003 (https://people.cs.uchicago.edu/~razborov/files/misha.pdf). EF lower bounds for NW-generators against EF are explicitly listed as open. So the proposal reduces P vs NP to an *equally hard* open problem in proof complexity. Conditional kill on tractability grounds.

## Q6

Not killed (no direct refutation found that bounded-arithmetic witnessing + cryptographic hardness *cannot* yield circuit lower bounds; this is in fact a program advocated by Krajicek and Pich).

## Q7

**Killed by Oliveira-Pich-Santhanam "Hardness magnification near state-of-the-art lower bounds" CCC 2019** (https://drops.dagstuhl.de/opus/volltexte/2019/10849/), because the magnification thresholds for MCSP and its variants (including padded/self-reducible variants like `MCSP*`) require lower bounds that are *just barely* beyond what current techniques achieve, and OPS19's "threshold gap" / "fine-grained" results show that the bounds obtainable from proof-complexity arguments of the Krajicek-Pich type fall on the wrong side of the threshold for the magnification to fire into NP-completeness. Specifically, EF witnessing arguments give quasi-polynomial bounds; the Hirahara reduction needs n^{1+ε} circuit lower bounds at a specific input length, and the proof-theoretic route does not pin down the constant.

## Q8

**Killed by Pich-Santhanam "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly" STOC 2021** (https://dl.acm.org/doi/10.1145/3406325.3451117 ; ECCC TR20-150), because they show that under standard cryptographic assumptions (which the proposal itself relies on for `P5`-PRG security), strong circuit lower bounds for NP *cannot* be proved within bounded-arithmetic theories like `VPV` and arguably `VNP_2`-adjacent theories. This directly attacks the proposal's stage 2: if `VNP_2` could carry out the witnessing argument to conclude an NP lower bound, then by Pich-Santhanam under crypto assumptions there is a meta-mathematical obstruction. Additionally, **Krajicek-Pich "Witnessing functions in bounded arithmetic and search problems" JSL 1998** (the very paper cited as a tool) does *not* establish that EF lower bounds for NW-tautologies are obtainable in `VNP_2` — the witnessing direction goes the wrong way for the proposal's purposes without additional unproved assumptions about the strength of `VNP_2`.

## Final verdict

Two hard kills: Q4 (locality barrier of Chen et al. JACM 2022 applied to the Hirahara magnification step) and Q8 (Pich-Santhanam STOC 2021 obstruction to feasibly provable NP lower bounds). Q5 and Q7 are strong conditional kills reducing the proposal to known major open problems. The three-stage chain breaks at stage 3 (locality barrier) and is meta-mathematically obstructed at stage 2 (Pich-Santhanam).

`LIT_RED`

VERDICT: LIT_RED