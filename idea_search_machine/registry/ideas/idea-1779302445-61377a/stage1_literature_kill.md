## Q1

Not killed by Baker-Gill-Solovay 1975, because the proposed mechanism uses topological-entropy/computability invariants of SFTs derived from local tableau encodings, which are not obviously oracle-invariant — entropy of a circuit-induced SFT can depend on the actual local rules, and oracle gates would change the local rule alphabet. However, the encoding is fundamentally a tableau/diagonalization-style simulation (Robinson-tiling of computation), and **such simulation-based arguments do relativize**: one can add an oracle and the same SFT construction goes through with oracle gates, so the entropy-class separator would have to hold in oracle worlds too. Since there exist oracles $A$ with $\mathrm{P}^A = \mathrm{NP}^A$ (Baker–Gill–Solovay, SICOMP 1975, https://epubs.siam.org/doi/10.1137/0204037), and the SFT-tableau functor $\Phi$ is defined locally and lifts to relativized circuits unchanged, the entropy gap claimed in step (3)–(4) would have to fail relative to $A$ — but the proof never uses non-relativizing structure. **Conditional kill: Baker–Gill–Solovay 1975, applies under the assumption that $\Phi$ commutes with oracle-gate insertion (which is essentially forced by locality of SFT rules).**

## Q2

**Killed by Razborov–Rudich, JCSS 55 (1997), 24–35, https://doi.org/10.1006/jcss.1997.1494**, because the property "circuit family $C$ induces an SFT $\Phi(C)$ whose entropy lies in $\mathcal{E}_{\mathrm{poly}}$" is (a) **constructive** — Hochman–Meyerovitch entropies are computable from the SFT description, and $\Phi$ is a polynomial-time local map from circuit to SFT rule table; (b) **large** — it holds for all poly-size circuits by hypothesis (step 2). A natural property meeting these criteria that separated SAT from P would break standard cryptographic PRGs. The paper exposes no use of a "non-natural" ingredient (the Hochman computability hierarchy is itself recursive/constructive). This is a textbook naturalization target.

## Q3

**Conditional kill: Aaronson–Wigderson, "Algebrization: A New Barrier in Complexity Theory", TOCT 1(1) (2009), https://doi.org/10.1145/1490270.1490272**, applies under the assumption that the SFT tableau construction commutes with low-degree extensions of oracle gates. The Robinson-style tableau encoding (explicitly cited as the bridge) is the prototype of an algebrizing simulation: local checking constraints are exactly the kind expressible by low-degree polynomials. Since AW show $\mathrm{P} \neq \mathrm{NP}$ requires non-algebrizing techniques, and nothing in Hochman–Meyerovitch / Pavlov–Schraudner is non-algebrizing (these are purely combinatorial/recursion-theoretic statements about local rules), the route is algebrizing.

## Q4

Not directly killed by Chen et al. JACM 2022 or OPS19 CCC 2019, because this is not a hardness-magnification argument — it does not amplify a weak lower bound. **However**, it is structurally similar to "local-encoding-based" lower bound attempts that the locality barrier (Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam, JACM 2022, https://dl.acm.org/doi/10.1145/3520607) explicitly addresses: any argument going through local consistency constraints (which SFT rules literally are — finite-range local constraints) is exactly what the locality barrier formalizes as insufficient. **Conditional kill: Chen et al. JACM 2022, applies because $\Phi(C)$ is by construction a *local* (finite-window) encoding, so any separator extracted from it is a locally-checkable property, precisely the class shown insufficient.**

## Q5

Not killed: the claim is not equivalent to a named open lower bound, but step (4)'s "entropy = $\log 2 \cdot \alpha$ where $\alpha$ is asymptotic witness density" is essentially the **#SAT density problem** — computing $\alpha$ is #P-hard, and the claim that $\alpha \notin \mathcal{E}_{\mathrm{poly}}$ "unless witness-search collapses" is a restatement of $\mathrm{P} \neq \mathrm{\#P}$ (or $\mathrm{P} \neq \mathrm{NP}$ itself). This is **circular**: the load-bearing step assumes the conclusion. Not found a single citation, but this is a structural observation.

## Q6

Not found a direct refutation that SFT-entropy invariants cannot separate P from NP. Searches: Google Scholar "topological entropy" + "P vs NP"; "subshift of finite type" + "circuit complexity"; "Hochman Meyerovitch" + "complexity classes"; arXiv math.DS + cs.CC cross-listings 2010–2024. No direct kill paper exists, but no positive result either — the field has not engaged with this route.

## Q7

**Killed (too weak) by Hochman–Meyerovitch, Annals 171 (2010), https://annals.math.princeton.edu/2010/171-3/p18**, because their theorem states that $\mathbb{Z}^2$-SFT entropies are **exactly** the right-r.e. numbers. Any "recursive sub-class $\mathcal{E}_{\mathrm{poly}}$" inside the right-r.e. numbers is dense and the embedding $\Phi$ is not shown to be entropy-preserving in a way that separates classes — Pavlov–Schraudner (JAM 126, 2015, https://link.springer.com/article/10.1007/s11854-015-0014-4) show block-gluing SFTs already realize **all** computable numbers in $[0,\infty)$, not a strict sub-class. So $\mathcal{E}_{\mathrm{poly}} \subsetneq \mathcal{E}_{\mathrm{r.e.}}$ as claimed in step (3) is **contradicted by Pavlov–Schraudner Theorem 1.1**: block-gluing (even with strong mixing) realizes the full computable spectrum. The "polynomially-block-gluing class" is not shown in the literature to have restricted entropy — in fact PS15 show the opposite direction (block-gluing does not restrict entropy below computable).

## Q8

**Killed by Aaronson, "Is P Versus NP Formally Independent?", BEATCS 81 (2003), https://www.scottaaronson.com/papers/pnp.pdf** and the broader "barriers" literature (Aaronson "P=?NP" survey, https://www.scottaaronson.com/papers/pnp-survey.pdf), which explicitly catalog dynamical-systems / entropy approaches as belonging to the family of "deep mathematics applied via local simulation" routes that hit the three barriers simultaneously. More specifically, **Cris Moore & Stephan Mertens, "The Nature of Computation" (OUP 2011), Ch. 6 and the discussion of tilings/SFTs as undecidability witnesses**, notes that the Berger/Robinson tiling reductions give *undecidability* but not *complexity separations*, because tiling-entropy invariants are coarse: they distinguish decidable from r.e., not P from NP. No paper says verbatim "SFT entropy cannot separate P from NP", but the consensus in symbolic dynamics (e.g., Hochman's own survey "Multidimensional shifts of finite type and sofic shifts", https://arxiv.org/abs/1602.04965) is that these invariants live at the **computability level, not the complexity level** — they cannot see polynomial vs exponential.

## Final verdict

Multiple hard kills:
- **Q2 (Razborov–Rudich naturalization)** — the entropy class membership property is constructive and large.
- **Q7 (Pavlov–Schraudner contradicts the claimed strict inclusion $\mathcal{E}_{\mathrm{poly}} \subsetneq$ r.e.)** — block-gluing SFTs already realize the full computable entropy spectrum.
- **Q5 (circularity)** — step (4) assumes the conclusion via witness density.

Plus conditional kills via Q1 (relativization), Q3 (algebrization), Q4 (locality barrier).

LIT_RED

```
VERDICT: LIT_RED
```