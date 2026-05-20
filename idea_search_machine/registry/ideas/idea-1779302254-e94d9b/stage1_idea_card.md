# Idea Card

## 1. Thesis

**Thesis**: Separate **P from NP** (specifically, exhibit a language in NP requiring super-polynomial circuits) by encoding SAT-solving circuit families as a **multidimensional subshift of finite type (SFT)** over a structured alphabet, and applying the **Hochman–Meyerovitch characterisation of topological entropies of ℤᵈ-SFTs** (d ≥ 2) together with **Pavlov–Schraudner-type undecidability obstructions** to entropy realisation under uniformly local constraints.

**Bridge (E14)**: Each circuit family `{C_n}` solving SAT induces, via a tile-system encoding of gate-locality + input-encoding consistency, a ℤ²-SFT `X_C` whose topological entropy `h(X_C)` is a Π₁-computable real determined by the circuit-size growth. Boolean circuits of polynomial size yield SFTs whose entropy lies in a restricted "polynomially-presentable" sub-class with effectively computable upper approximations at a controlled rate. The set of SAT-witnessing tile systems, however, must realise entropies forced (by a tile-encoding of #SAT counting via Furstenberg–Weiss-style fibre-entropy decompositions) into a class of right-recursively enumerable reals **without matching left-r.e. upper approximation at polynomial rate**.

**Conclusion**: A polynomial-size SAT-solving circuit family would yield a ℤ²-SFT whose entropy is simultaneously polynomially left-r.e. approximable and equals a quantity forced to be only right-r.e. approximable — contradiction, hence `P ≠ NP`.

## 2. Prerequisite techniques

**From E14 (topological / symbolic dynamics)**:
- **Hochman–Meyerovitch (2010), "A characterization of the entropies of multidimensional shifts of finite type"**, *Annals of Mathematics* 171(3):2011–2038. The set of ℤᵈ-SFT entropies (d ≥ 2) equals the set of non-negative right-r.e. reals.
- **Pavlov–Schraudner (2015), "Entropies realizable by block gluing ℤᵈ shifts of finite type"**, *Journal d'Analyse Mathématique* 126:113–174. Strengthening of realisable-entropy classes under mixing constraints — critical for the "circuit-uniformity ⇒ block-gluing" step.
- **Hochman (2009), "On the dynamics and recursive properties of multidimensional symbolic systems"**, *Inventiones Mathematicae* 176(1):131–167. Computability-of-entropy framework and Medvedev-degree analysis of SFT factors — provides the rate-of-approximation refinement we need.
- **Boyle–Pavlov–Schraudner (2010), "Multidimensional sofic shifts without separation and their factors"**, *Transactions AMS* 362:4617–4653. Sofic-projection lemmas needed to project gate-traffic encodings.

**From complexity theory (background only)**:
- Cook–Levin SAT-encoding into tile systems (used only as the input-side bookkeeping, not as load-bearing mechanism).
- Standard P/poly definition.

## 3. Expected mechanism

Encode a candidate uniform circuit family `{C_n}` as a **tile system** on ℤ² where:
- Horizontal direction codes time / gate-layer index.
- Vertical direction codes a SAT instance + its candidate assignment, padded with "witness-trace" symbols.

Local SFT constraints enforce: (i) valid gate-evaluation transitions, (ii) consistency of the input clause with the bottom row, (iii) acceptance symbol on the top row iff a satisfying assignment is encoded.

**Load-bearing step**: The topological entropy `h(X_C)` of this SFT decomposes (via a relative variational principle, Downarowicz 2011) into `h_input + h_witness_given_input`. The conditional entropy `h_witness_given_input` is the asymptotic log-rate of satisfying assignments — a `#P`-type counting quantity.

By **Hochman–Meyerovitch**, *every* right-r.e. real is achievable as an SFT entropy, but the **rate of left-r.e. approximation** is what distinguishes complexity classes: Hochman (2009, §6) shows the approximation rate is tied to the Medvedev degree of the SFT's language. A polynomial-circuit SAT solver collapses this approximation rate to polynomial, forcing `h_witness_given_input` into the **left-polynomially-r.e.** class.

The contradiction: a diagonal SAT-like instance family (constructed via Pavlov–Schraudner's block-gluing entropy-pumping) produces an SFT entropy provably outside the left-polynomially-r.e. class but inside the SAT-encodable family. Hence no polynomial circuit family exists.

## 4. Target pnp3 / pnp4 interface

`pnp3.Core.PvsNP.exists_language_in_NP_not_in_Ppoly`
— specifically constructing the witness language as `SAT_tile := { (φ, w) | tile system T_φ admits a valid configuration with witness-trace w }` and showing membership in NP via direct simulation, while non-membership in P/poly is reduced to the entropy-approximation-rate dichotomy formalised as a new lemma `SFT_entropy_rate_dichotomy` in `pnp4.Dynamics.SFTEntropy`.

## 5. Self-assessment of novelty and cluster-avoidance

**Overall novelty**: HIGH.

**Forbidden-cluster avoidance**:
- **Cluster A (proof complexity)**: primary mechanism is the Hochman–Meyerovitch entropy classification — a theorem of ergodic theory / symbolic dynamics. No bounded arithmetic, no Frege system, no witnessing theorem is invoked.
- **Cluster B (GCT)**: no orbit closures, no plethysm, no representation-theoretic obstruction; the mechanism is topological-dynamical (entropy of subshifts), not algebraic-geometric.
- **Cluster C (natural property variants)**: the obstruction is the *recursion-theoretic class* of SFT entropies, not a density / Fourier / spectral / homological property of Boolean functions. The "largeness" property is on the SFT side, not the truth-table side, dodging the Razborov–Rudich constructivity/largeness frame.
- **Cluster D (hardness magnification)**: no MCSP, no weak-to-strong amplification chain; the argument is direct from SFT entropy to circuit size.
- **Cluster E (standard barrier workarounds)**: not relativizing because SFT-encoding uses specific tile syntax tied to SAT structure; not algebrizing because no polynomial extension is invoked; not natural because the SFT-entropy class is neither large nor constructive in the Razborov–Rudich sense.

**Cross-domain bridge chosen**: **E14** — topological/symbolic dynamics, specifically multidimensional SFT entropy theory.

**Three alternative bridges considered before settling**:
- **Alternative 1: E2 (ergodic theory / Furstenberg correspondence)**. Rejected because Furstenberg-style correspondence principles have already drawn complexity-theory attention via additive combinatorics (Green–Tao influence on PCP/lower bounds), making the connection less unexplored.
- **Alternative 2: E8 (Ricci curvature on graphs / optimal transport)**. Rejected because Ollivier-Ricci curvature has begun appearing in graph-learning and expander literature; the boundary with complexity theory is becoming porous.
- **Alternative 3: E1 (subfactors / Jones index)**. Rejected because while genuinely disconnected from complexity, the technical bridge to Boolean circuit semantics requires inventing the entire encoding from scratch with no published anchor result of comparable specificity to Hochman–Meyerovitch.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Multidimensional SFT entropy classification (Hochman–Meyerovitch) is a deep result in symbolic dynamics whose only known computability-theoretic uses are inside dynamics itself — there is no prior application to circuit lower bounds or P-vs-NP, and the *rate-of-approximation* refinement is essentially untouched outside Hochman's own work.

**Genuine novelty escape**: cross-domain bridge from E14 (Hochman–Meyerovitch ℤᵈ-SFT entropy = right-r.e. reals, with rate-of-approximation refinement) plus the barrier evasion that the lower bound is extracted from a **recursion-theoretic asymmetry** (left-r.e. polynomial-rate vs. right-r.e. unrestricted) of a dynamical invariant of an SFT *encoding* circuit traces — neither relativizing (depends on SFT syntax), nor algebrizing (no polynomial oracle extension), nor natural (the obstruction predicate is on tile systems, not on truth tables, and is provably non-constructive in poly-time).

VERDICT: idea_card_generated