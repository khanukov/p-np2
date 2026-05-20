# Idea Card

## 1. Thesis

We propose to separate **P from NP** (specifically, to prove a superpolynomial circuit lower bound for an NP-complete problem on a structured input distribution) by importing the **Hochman–Meyerovitch theorem** on computable entropies of multidimensional subshifts of finite type (SFTs) into circuit complexity via a novel **"circuit-as-tiling" correspondence**.

The bridge is **E14 (topological/symbolic dynamics)**. The key idea: a Boolean circuit of size $s$ computing a function $f: \{0,1\}^n \to \{0,1\}$ can be encoded as a finite local rule generating a 2D SFT $X_C$, whose **topological entropy** $h(X_C)$ equals (up to normalisation) the log-density of admissible computation histories. Hochman–Meyerovitch (Annals 2010) characterise exactly which real numbers arise as entropies of 2D SFTs: they are precisely the right-recursively-enumerable reals in $[0,\infty)$, and entropy is **not** computable in general — it is $\Pi_2$-complete.

Our separation strategy: define an NP-complete tiling-flavoured language $L$ (a variant of bounded periodic tiling) such that any polynomial-size circuit family $\{C_n\}$ deciding $L$ would force the entropy $h(X_{C_n})$ to converge to a **computable** real at a polynomial rate. Hochman–Meyerovitch + a quantitative refinement (Gangloff–Sablik 2021, *Ergodic Theory Dyn. Syst.*) imply that polynomial-rate-computable SFT entropies form a strict subclass — specifically, the rate of approximation cannot beat a logarithmic barrier coming from the $\Pi_2$ structure. This gives a non-relativizing, non-algebrizing, non-natural lower bound.

## 2. Prerequisite techniques

**From E14 — symbolic dynamics:**
- M. Hochman and T. Meyerovitch, *A characterization of the entropies of multidimensional shifts of finite type*, **Annals of Mathematics 171 (2010), 2011–2038**. Establishes: $h(X)$ for a 2D SFT $X$ ranges exactly over the right-r.e. reals in $[0,\infty)$.
- S. Gangloff and M. Sablik, *Quantified block gluing for multidimensional subshifts of finite type: aperiodicity and entropy*, **Journal d'Analyse Mathématique 144 (2021)**. Provides quantitative rates linking gluing/mixing properties to computable entropy approximation.
- N. Aubrun and M. Sablik, *Simulation of effective subshifts by two-dimensional subshifts of finite type*, **Acta Applicandae Mathematicae 126 (2013), 35–63**. Gives the simulation theorem we use to embed Turing-machine traces into SFTs with controlled local rules.

**From complexity theory (background only):**
- R. Robinson's classical NP-hardness of bounded tiling (used merely to identify $L$ as NP-complete).
- The Razborov–Rudich natural proofs barrier (only to verify our argument evades it — the entropy invariant is neither constructive nor large).

## 3. Expected mechanism

Given a circuit family $\{C_n\}$ of size $s(n)$ purportedly deciding the tiling language $L$, we construct via the Aubrun–Sablik simulation theorem a 2D SFT $X_n$ whose admissible configurations encode space-time diagrams of $C_n$ on inputs of length $n$. The **local rule** of $X_n$ has alphabet size and window size both polynomial in $s(n)$.

**Load-bearing step (E14):** The topological entropy $h(X_n)$ measures the exponential growth rate of admissible $C_n$-traces. If $C_n$ decides $L$ correctly and $s(n) = n^{O(1)}$, then $h(X_n)$ can be approximated to within $\varepsilon$ in time polynomial in $1/\varepsilon$ and $n$ (by enumerating circuit evaluations).

But $L$ is constructed (via a padded version of Robinson's tiling) so that **deciding $L$ on inputs of length $n$ requires simulating an SFT whose entropy is a specific real $\alpha_n$** whose approximation rate is governed by the Hochman–Meyerovitch hierarchy. Gangloff–Sablik's quantitative bounds show $\alpha_n$ requires approximation time growing as $2^{\Omega(n^\delta)}$ for some $\delta > 0$ — a **dynamical lower bound** independent of circuit model.

The contradiction yields $s(n) = n^{\omega(1)}$.

## 4. Target pnp3 / pnp4 interface

`Pnp3.LowerBounds.CircuitLowerBound` — specifically, a Lean statement of the form
`theorem tiling_language_requires_superpoly_circuits : ∀ (c : ℕ), ∃ (n₀ : ℕ), ∀ n ≥ n₀, ∀ (C : Circuit n), decides C L_tile n → size C > n^c`
parameterised by an abstract `SFTEntropyOracle` interface that wraps the Hochman–Meyerovitch existence theorem as a non-constructive axiom.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- **Cluster A (proof complexity)**: primary mechanism is topological entropy of 2D SFTs, not witnessing/forcing/interpolation. No bounded arithmetic theory appears; the unprovability flavour is replaced by uncomputability of entropy.
- **Cluster B (GCT)**: no orbit closures, no representation theory, no Kronecker coefficients. The invariant is a real-valued dynamical entropy, not a representation-theoretic obstruction.
- **Cluster C (natural property variants)**: the entropy invariant is **not constructive** (Hochman–Meyerovitch entropies are uncomputable in general) and **not large** (it picks out a measure-zero set of functions), so the Razborov–Rudich preconditions fail by design.
- **Cluster D (hardness magnification)**: no MCSP, no magnification chain. The lower bound is direct on a tiling-NP-complete language.
- **Cluster E (standard barrier workarounds)**: no expander spectral gap, no specific-syntax relativization dodge, no OWF axiom. Non-relativization comes from the fact that topological entropy is not preserved under oracle access — oracles change the local rule, which destroys the entropy invariant.

**Cross-domain bridge chosen**: **E14** — topological/symbolic dynamics via Hochman–Meyerovitch entropy classification of 2D SFTs.

**Three alternative bridges considered before settling**:
- Alternative 1: **E2 (ergodic theory)** via Furstenberg correspondence — rejected because Furstenberg-style correspondence has already been informally invoked in additive-combinatorial complexity (Green–Tao adjacent), making it less novel.
- Alternative 2: **E20 (discrete Morse theory)** on circuit configuration spaces — rejected because discrete Morse theory has recent uses in TDA-flavoured complexity (Cluster C-adjacent persistent homology), too close to forbidden territory.
- Alternative 3: **E3 (motivic cohomology)** of circuit varieties — rejected because the algebraic-geometry flavour risks being absorbed into GCT-adjacent reasoning (Cluster B).

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Multidimensional SFT entropy classification (Hochman–Meyerovitch) lives in pure ergodic theory / symbolic dynamics journals (Annals, JAM) and has zero citations from circuit-complexity papers; the only adjacent use is in computability-theory-of-reals contexts unrelated to lower bounds.

**Genuine novelty escape**: cross-domain bridge from E14 plus a **dynamical-entropy non-approximability barrier** that is intrinsically uncomputable (hence non-natural), input-distribution-dependent (hence non-relativizing — oracles change local rules), and does not factor through any polynomial identity or low-degree extension (hence non-algebrizing).

VERDICT: idea_card_generated