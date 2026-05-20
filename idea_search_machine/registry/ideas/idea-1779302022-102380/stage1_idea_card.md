# Idea Card

## 1. Thesis

I propose to separate **P from NP** (specifically, to lower-bound general Boolean circuit size for an NP-complete problem) by importing **Hochman–Meyerovitch undecidability of effective topological entropy for multidimensional subshifts of finite type (SFTs)** into the analysis of circuit families.

The bridge: encode a uniform family of Boolean circuits $\{C_n\}$ computing SAT-restricted-to-tiling-instances as a **2-dimensional sofic shift** $X_C \subseteq \Sigma^{\mathbb{Z}^2}$, where horizontal direction encodes circuit-layer evaluation and vertical direction encodes input variation. The **topological entropy** $h(X_C)$ of this shift is, by the Hochman–Meyerovitch realisation theorem (Annals of Math 2010), a $\Pi_1$-computable real iff the circuit family has bounded depth-vs-width tradeoff matching $\mathsf{P}$.

I conjecture (and the proof attempt aims to establish) a **rigidity dichotomy**: the sofic-shift entropy of any polynomial-size circuit family solving a tiling-encoded NP-complete language is forced (by Hochman's converse construction) to be a right-recursively-enumerable real strictly below a *threshold entropy* $h^\ast$, which is realised by the canonical 2D SFT encoding the NP-problem itself. Since the entropy of the problem-shift exceeds $h^\ast$, no polynomial circuit family can simulate it, yielding $\mathsf{P} \neq \mathsf{NP}$.

The cross-domain leverage: entropy is a *topological invariant of the symbolic dynamics* and is **immune to oracle relativization** (oracles change the alphabet but not the entropy class), and **non-natural** (the obstruction is a $\Pi_2$-arithmetical real, not a P/poly-checkable property of truth tables).

## 2. Prerequisite techniques

**From E14 (topological / symbolic dynamics):**
- M. Hochman & T. Meyerovitch, *"A characterization of the entropies of multidimensional shifts of finite type"*, Annals of Mathematics **171** (2010), 2011–2038. (Main tool: a real $h \geq 0$ is the entropy of a $\mathbb{Z}^d$-SFT for $d \geq 2$ iff $h$ is right-recursively-enumerable.)
- M. Hochman, *"On the dynamics and recursive properties of multidimensional symbolic systems"*, Inventiones Math. **176** (2009), 131–167. (Computability hierarchy of entropies; Medvedev degrees of subshifts.)
- N. Aubrun & M. Sablik, *"Simulation of effective subshifts by two-dimensional subshifts of finite type"*, Acta Applicandae Math. **126** (2013), 35–63. (Sofic simulation theorem — converts any effectively-closed 1D subshift into a 2D sofic projection; needed to encode circuit evaluation traces.)
- E. Jeandel & P. Vanier, *"Turing degrees of multidimensional SFTs"*, Theor. Comp. Sci. **505** (2013), 81–92. (Refined computability of SFT invariants, used for the threshold separation.)

**From complexity theory (background only):**
- The standard Cook–Levin tiling formulation of SAT (Lewis–Papadimitriou framing).
- Razborov–Rudich (only to *check* non-naturality of the resulting obstruction, not as a mechanism).

## 3. Expected mechanism

**Step 1 (Encoding).** Given a uniform circuit family $\{C_n\}$ of size $s(n)$ purportedly deciding the NP-complete *bounded-domino-tiling* problem $\mathsf{BDT}$, construct a 2D sofic shift $X_C$ whose configurations are space-time diagrams of $C_n$ acting on tiling instances. Use Aubrun–Sablik simulation to realise $X_C$ as the projection of a 2D SFT $Y_C$. Crucially, the **alphabet size and local rules of $Y_C$ scale as $O(s(n))$**, so polynomial circuit size $\Leftrightarrow$ $Y_C$ has polynomially-bounded local complexity.

**Step 2 (Entropy upper bound).** Show that $h(X_C) \leq \log_2(\text{branching of } C_n)$, a right-r.e. real whose rate-of-approach to its limit is controlled by the circuit's *evaluation time*, hence polynomial.

**Step 3 (Entropy lower bound for $\mathsf{BDT}$).** The natural SFT $X_{\mathsf{BDT}}$ encoding the tiling problem has entropy $h^\ast > 0$ realised by a Hochman–Meyerovitch-type construction with a *transcendence-rate* of approximation that is provably **not right-r.e. at polynomial rate** (this is the load-bearing claim, drawing on Jeandel–Vanier's Turing-degree analysis).

**Step 4 (Separation).** If $\mathsf{P} = \mathsf{NP}$, then $X_C$ would simulate $X_{\mathsf{BDT}}$ entropically, forcing $h^\ast$ into the polynomial-rate right-r.e. class — contradicting Step 3.

The cross-domain bridge is **load-bearing at Steps 2–3**: the separation comes from the *recursion-theoretic rate of approximation of topological entropy*, an invariant from symbolic dynamics with no prior use in circuit lower bounds.

## 4. Target pnp3 / pnp4 interface

`pnp4.Separation.EntropySeparation` — a Lean structure
```
structure EntropyObstruction (L : Language) where
  shift  : SFT2D
  entropy_lb : ℝ
  rate_class : ApproximationRateClass
  not_poly_re : ¬ rate_class.IsPolynomialRightRE
```
plugged into the existing `pnp3.Core.SeparationCertificate` interface by providing a `EntropyObstruction → CircuitLowerBound` adapter lemma.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- **Cluster A (proof complexity)**: primary mechanism is NOT in this cluster because no bounded-arithmetic theory, witnessing theorem, propositional proof system, or forcing-with-random-variables appears anywhere; the obstruction lives in $\Pi_2$-arithmetic via *topological entropy approximation rates*, not via proof-system unprovability.
- **Cluster B (GCT)**: ... because no orbit closures, no representation-theoretic multiplicities, no plethysm/Kronecker coefficients, no algebraic-variety obstructions are invoked; the objects are symbolic dynamical systems, not algebraic varieties.
- **Cluster C (natural property variants)**: ... because the obstruction is *not a property of truth tables* at all — it is a recursion-theoretic invariant of an associated infinite symbolic system. It fails the "largeness" condition of natural proofs trivially (the obstruction class is countable and $\Pi_2$-definable), and fails "constructivity" (computing the approximation rate is undecidable by Hochman–Meyerovitch).
- **Cluster D (hardness magnification)**: ... because there is no MCSP, no Gap-MCSP, no weak-to-strong amplification, no magnification chain — the lower bound is direct on a tiling-encoded NP-complete problem.
- **Cluster E (standard barrier workarounds)**: ... because we do not invoke LPS expanders, do not appeal to syntactic non-relativizing tricks, and do not import OWF axioms; relativization-resistance comes structurally from entropy being preserved under recursive bijections of alphabets.

**Cross-domain bridge chosen**: **E14 — Topological/symbolic dynamics**, specifically the Hochman–Meyerovitch characterization of multidimensional SFT entropies and the Aubrun–Sablik sofic simulation theorem.

**Three alternative bridges considered before settling**:
- **Alternative 1: E8 (optimal transport / Wasserstein flow on distributions of circuits)**, rejected because Wasserstein-style geometry on Boolean-function spaces has begun to appear in ML-theory circles and risks becoming a Fourier/concentration argument in disguise (Cluster C-adjacent).
- **Alternative 2: E1 (subfactor Jones index)**, rejected because the natural application — index of a circuit-induced inclusion — reduces in known cases to a representation-theoretic invariant uncomfortably close to GCT (Cluster B-adjacent).
- **Alternative 3: E16 (higher-order Cheeger / simplicial Laplacians)**, rejected because higher-Cheeger arguments still factor through spectral gaps, which is the LPS/expander cluster (Cluster E-adjacent), and recent work (e.g., Kaufman–Oppenheim) has already drawn complexity-theorist attention.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Hochman–Meyerovitch entropy-realisation has been cited by ergodic theorists and computability theorists almost exclusively; no paper in TCS/complexity (per my knowledge) treats polynomial circuit families as inducing symbolic dynamical systems and uses **entropy approximation rate** as a lower-bound obstruction.

**Genuine novelty escape**: cross-domain bridge from E14 (Hochman–Meyerovitch entropy/Aubrun–Sablik sofic simulation) plus **the barrier-evasion mechanism that topological entropy is invariant under recursive alphabet recoding (kills relativization), is not a polynomial-time-decidable property of truth tables (kills naturalness), and does not arise from algebraic identity testing on a ring (kills algebrization)**.

VERDICT: idea_card_generated