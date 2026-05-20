## Q1

**Is this relativizing?**

The proposed proof attempts to encode circuit computation into a Z²-SFT and extract entropy bounds. The encoding is via Cook-Levin-style local simulation, which is fundamentally a relativizing technique: an oracle gate can be incorporated as a local rule in the SFT just as easily as an AND/OR gate. The Aubrun-Sablik simulation theorem (the load-bearing tool) embeds arbitrary effective subshifts, including those defined by oracle Turing machines, into Z²-SFTs with uniform local rules. The entropy of such a relativized SFT would still be right-r.e. relative to the oracle, and the Hochman-Meyerovitch classification relativizes cleanly to oracle computation.

Killed by Baker-Gill-Solovay, "Relativizations of the P =? NP question," SIAM J. Comput. 4 (1975), 431-442, https://doi.org/10.1137/0204037, because the proposed construction `C ↦ X_C` is a local simulation that treats gates as black-box symbols — adding an oracle gate to the alphabet and a corresponding local rule produces an SFT `X_C^A` with all the same entropy-approximation properties relative to A. Hence the argument, if it worked, would prove `SAT^A ∉ P^A/poly` for every oracle A, contradicting BGS.

## Q2

**Is this natural?**

The "polynomial circuit ⟹ polynomial entropy-defect decay" lemma defines a property of circuits (or their truth tables) via a window-approximation rate in the encoded SFT. This property would be:
- **Constructive**: the entropy-defect at window size n is computable in time polynomial in the SFT alphabet (and hence in circuit size) via standard transfer-matrix / pattern-counting algorithms (Friedland; Pavlov-Schraudner give explicit algorithms).
- **Large**: a random function should have entropy-defect decay matching that of a generic / maximum-entropy SFT, putting most functions in the "hard" class.

Killed by Razborov & Rudich, "Natural Proofs," JCSS 55 (1997), 24-35, https://doi.org/10.1006/jcss.1997.1494, because the entropy-defect property as defined is (i) computable in time poly in the truth-table from local rules (constructivity), and (ii) the diagonalization in Step 3 against polynomial-rate r.e. reals selects a property that includes a large fraction of functions (largeness). Under standard cryptographic assumptions (existence of pseudorandom function generators in P/poly), no such property can separate P/poly from random functions. The author makes no attempt to evade this barrier; the entropy-defect is *defined to be* a tame combinatorial quantity.

## Q3

**Is this algebrizing?**

The simulation of circuits by SFTs is a local, gate-by-gate encoding. Aaronson-Wigderson algebrization extends relativization to low-degree extensions of oracles. The SFT encoding can be extended to algebraic oracle gates by extending the alphabet to encode field elements (truncated to finite precision) — the Hochman-Meyerovitch framework was extended by Hochman to effective dynamical systems on more general computable spaces.

Conditional kill: Aaronson & Wigderson, "Algebrization: A New Barrier in Complexity Theory," ACM TOCT 1 (2009), Article 2, https://doi.org/10.1145/1490270.1490272, applies under the assumption (essentially trivial here) that the SFT encoding extends to algebraic gates symbol-by-symbol. Since the encoding is purely local and uniform-radius (Aubrun-Sablik), it commutes with low-degree extensions, so the argument algebrizes and is killed for the same reason as Q1.

## Q4

**Is this a known hardness-magnification dead end?**

The argument is not framed as magnification (small lower bound ⟹ big one), so the locality barrier of Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam does not directly apply. However, the route does have a "locality" flavor: the entropy-defect lemma is supposed to hold *because of* a local circuit-to-tiling simulation, and the proof of the lower bound proceeds by a diagonal/counting argument over local rules.

Not killed by Chen et al., "Beyond Natural Proofs: Hardness Magnification and Locality," JACM 69 (2022), 25:1-25:49, https://doi.org/10.1145/3538391, because the proposed argument does not invoke magnification per se. However, the locality barrier suggests that any proof going through "local simulation + counting" should be viewed with extreme suspicion. Not a direct kill, but a strong warning.

## Q5

**Is this equivalent to a known open lower bound?**

The target is `NP ⊄ P/poly`, which is the standard NP vs P/poly question; the route is novel but the target is the canonical open problem. The intermediate claim — that polynomial-size circuits force polynomial entropy-defect decay — if proved, would be a new theorem connecting circuit complexity to SFT entropy, but it is not known to be equivalent to any other open problem.

Not killed: this question does not produce a kill. The route's target is the canonical separation, so "equivalence to a known open problem" is trivially the same problem.

## Q6

**Is this already proved impossible?**

The combination of Q1 (relativization) and Q2 (natural proofs) gives standard impossibility arguments against the *route as described*. No paper specifically refutes "use SFT entropies to separate P from NP" because no one has proposed it; but the general form (local simulation + entropy/counting bound) is killed by the union of standard barriers.

Killed by Razborov-Rudich (https://doi.org/10.1006/jcss.1997.1494) combined with Baker-Gill-Solovay (https://doi.org/10.1137/0204037), because the proposed argument is both relativizing and natural, and these two barriers jointly forbid it modulo standard cryptographic assumptions.

## Q7

**Is this already known to be too weak?**

The Hochman-Meyerovitch entropy characterization gives only that the entropy is right-r.e.; the quantitative approximation rates from Pavlov-Schraudner apply under block-gluing/mixing conditions that are unlikely to hold for a computation-trace SFT (which is highly non-mixing — the simulation traces are essentially deterministic given input).

Conditional kill: Pavlov & Schraudner, "Entropies realizable by block gluing Z^d shifts of finite type," J. Anal. Math. 126 (2015), 113-174, https://doi.org/10.1007/s11854-015-0014-4, applies under the assumption that the computation-trace SFT is block-gluing. It is not: simulation SFTs in the Aubrun-Sablik / Hochman framework are notoriously non-mixing (cf. Hochman 2009, where the constructions deliberately exploit lack of mixing to encode arbitrary recursive structure). So the quantitative tool Step 2 needs **does not apply** to the SFT Step 1 constructs. This is a hard internal inconsistency in the prerequisites.

## Q8

**Is there a paper that directly says "this type of route does not work"?**

The general meta-result is that any "uniform local encoding" route is killed by relativization. More specifically, Hochman's own 2009 Inventiones paper observes that the recursive-theoretic structure of effective dynamical systems is *too flexible* to make fine-grained complexity distinctions — every right-r.e. real is an SFT entropy, so SFT entropies cannot distinguish polynomial-time from exponential-time computations at the level of the entropy value itself; one needs the rate of convergence, and the rate is governed by Kolmogorov complexity (uniform), not circuit complexity (non-uniform).

Killed by Hochman, "On the dynamics and recursive properties of multidimensional symbolic systems," Invent. Math. 176 (2009), 131-167, https://doi.org/10.1007/s00222-008-0161-7, because Hochman's framework characterizes effective subshifts up to *computable* (uniform) equivalence; there is no known mechanism in this framework to distinguish circuit size n^k from n^{k+1} in the non-uniform setting. The "right-r.e. real with sub-poly approximation rate" produced by Solovay-style diagonalization is a diagonalization against *uniform* poly-time machines, not against non-uniform circuits — so encoding it into SAT does not contradict SAT ∈ P/poly, only SAT ∈ P. The argument at best (if everything else worked) re-derives the time hierarchy theorem.

This is the fatal internal flaw: Step 3 diagonalizes against uniform polynomial-time approximation, but the target is non-uniform P/poly. The "diagonal SFT" cannot diagonalize against non-uniform circuits because there is no recursive enumeration of polynomial-size circuit families — exactly the gap that Razborov-Rudich crystallizes.

## Final verdict

Multiple hard kills:
- **Q1**: relativizes (BGS).
- **Q2**: natural in the Razborov-Rudich sense.
- **Q7**: the quantitative entropy-approximation tools (Pavlov-Schraudner) require block-gluing, which computation-trace SFTs do not have.
- **Q8**: the diagonalization in Step 3 is against *uniform* poly-time, not against non-uniform P/poly — fatal target mismatch.

The most decisive is Q8: even granting all dynamical machinery, the diagonal SFT cannot separate against non-uniform circuits, only against uniform polynomial time.

LIT_RED

VERDICT: LIT_RED