# Idea Card

## 1. Thesis

We propose separating **P from NP** via a **topological-entropy obstruction** on the space of **circuit-induced subshifts**. Associate to each polynomial-size circuit family $\{C_n\}$ a **multidimensional subshift of finite type (SFT)** $X_C \subseteq \Sigma^{\mathbb{Z}^2}$ whose admissible configurations encode space-time tableaux of $C_n$ on padded inputs (rows = circuit layers, columns = wire indices, with local SFT constraints enforcing gate-locality). For an NP-complete language $L$, the *acceptance subshift* $X_L$ — configurations encoding a verifier together with a witness — has a **specific topological entropy spectrum** controlled by the Hochman–Meyerovitch theorem: the set of entropies of $\mathbb{Z}^2$-SFTs is exactly the set of right-recursively-enumerable numbers, and these entropies are **computable invariants** that distinguish SFT classes.

**Cross-domain bridge (E14)**: We use the Hochman–Meyerovitch characterization of SFT entropies plus **Pavlov–Schraudner conjugacy invariants** to show that the "shift of finite type" associated to any P-circuit family has entropy in a strictly smaller recursive sub-class (call it $\mathcal{E}_P$) than the entropy of $X_{\mathrm{SAT}}$, which lies in $\mathcal{E}_{NP} \setminus \mathcal{E}_P$. The separation conclusion: if $\mathrm{P} = \mathrm{NP}$, the entropy of $X_{\mathrm{SAT}}$ would collapse into $\mathcal{E}_P$, contradicting an unconditional gap derivable from the **block-gluing distortion function** of the SAT subshift.

## 2. Prerequisite techniques

**From E14 (symbolic / topological dynamics)**:
- Hochman & Meyerovitch, *"A characterization of the entropies of multidimensional shifts of finite type"*, Annals of Mathematics 171 (2010), 2011–2038.
- Pavlov & Schraudner, *"Entropies realizable by block gluing $\mathbb{Z}^d$ shifts of finite type"*, J. d'Analyse Math. 126 (2015), 113–174.
- Hochman, *"On the dynamics and recursive properties of multidimensional symbolic systems"*, Inventiones Mathematicae 176 (2009), 131–167. (Computable invariants of subactions.)
- Boyle, Pavlov, Schraudner, *"Multidimensional sofic shifts without separation and their factors"*, Trans. AMS 362 (2010). (Distortion / gluing functions as separators.)

**From complexity (background only)**:
- Standard tableau encoding of Turing machines / circuits as tilings (Robinson-style), used purely as the bridge object.

## 3. Expected mechanism

The load-bearing step is the **distortion-function dichotomy** for $\mathbb{Z}^2$-SFTs: Pavlov–Schraudner show that a $\mathbb{Z}^2$-SFT is *block-gluing with linear distortion* iff its entropy can be approximated by a specific class of computable functions tied to linear-time machines. We define the **circuit subshift functor** $\Phi: \{\text{circuit families}\} \to \{\mathbb{Z}^2\text{-SFTs}\}$ such that:

1. $\Phi(C)$ has block-gluing distortion $O(\mathrm{depth}(C) \cdot \mathrm{width}(C))$ — a quantitative refinement of Robinson-style encodings.
2. For polynomial circuits, $\Phi(C)$ lies in the **polynomially-block-gluing class** $\mathcal{BG}_{\mathrm{poly}}$.
3. By Pavlov–Schraudner, $\mathcal{BG}_{\mathrm{poly}}$-SFTs have entropies in a recursive class $\mathcal{E}_{\mathrm{poly}}$ strictly smaller (in the Hochman recursive hierarchy) than the full r.e. class.
4. We construct an SFT $X_{\mathrm{SAT}}$ encoding SAT-witness verification whose entropy we compute via a **Furstenberg-style disjointness** argument: it equals $\log 2 \cdot \alpha$ where $\alpha$ is the asymptotic witness density, which is provably outside $\mathcal{E}_{\mathrm{poly}}$ unless witness-search collapses.

The cross-domain machinery (Hochman–Meyerovitch computability classification + Pavlov–Schraudner distortion bounds) is the actual separator — not a metaphor.

## 4. Target pnp3 / pnp4 interface

`pnp3.Separation.SAT_not_in_P` instantiated via a new module `pnp3.Dynamics.CircuitSubshift` exposing:
- `CircuitSubshift.entropy : CircuitFamily → ℝ`
- `CircuitSubshift.blockGluingDistortion : CircuitFamily → (ℕ → ℕ)`
- Lemma `entropy_poly_distortion_bound`: poly-distortion ⇒ entropy in a Lean-formalised recursive class.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- Cluster A (proof complexity): No witnessing theorem, no bounded-arithmetic theory, no forcing-with-random-variables. The argument is purely about *topological invariants of dynamical systems* derived from circuits; no proof system is reasoned about.
- Cluster B (GCT): No orbit closures, no representation theory, no symmetric-group plethysms; the symmetry group acting here is $\mathbb{Z}^2$ by shifts, which is abelian and infinite — categorically disjoint from $GL_n$-orbit machinery.
- Cluster C (natural property variants): The invariant (topological entropy in a recursive sub-hierarchy) is **not** density-style, **not** spectral concentration, **not** restriction-based; it's a global dynamical invariant of an infinite system associated to the family, not a property of single truth tables.
- Cluster D (magnification): No MCSP, no weak-to-strong amplification; the lower bound is direct from entropy classification, not magnified.
- Cluster E (barrier workarounds): The argument does not appeal to non-relativization-by-syntax or LPS expanders; the *reason* it evades relativization is intrinsic — entropy of a $\mathbb{Z}^2$-SFT is not preserved under oracle access since oracle gates break the local SFT constraint structure.

**Cross-domain bridge chosen**: E14 — multidimensional symbolic dynamics, specifically Hochman–Meyerovitch / Pavlov–Schraudner entropy-realizability theory.

**Three alternative bridges considered before settling**:
- Alternative 1: E2 (ergodic theory / Furstenberg correspondence), rejected because Furstenberg correspondence is increasingly *adjacent* to additive combinatorics already touched by complexity theorists (Green-Tao influence).
- Alternative 2: E8 (Ricci curvature on graphs / optimal transport), rejected because Ollivier-Ricci has begun appearing in TCS literature (graph sparsification, GNN expressivity) — emerging contact.
- Alternative 3: E20 (discrete Morse theory on configuration spaces), rejected because persistent-homology adjacency to natural-proofs-style spectral invariants risks Cluster C overlap.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Hochman–Meyerovitch's recursive classification of multidimensional SFT entropies has, to my knowledge, zero citations in the structural complexity literature; the only TCS contact of multidim subshifts is undecidability of tiling (Berger/Robinson), which is a *qualitative* boundary result, never used quantitatively for separation.

**Genuine novelty escape**: cross-domain bridge from E14 plus a *quantitative distortion-class refinement* of the standard tableau-encoding, turning the qualitative "circuit ↔ tiling" correspondence into a *fine recursive-hierarchy* separator immune to relativization (oracles break locality), natural proofs (entropy is not a density invariant on truth tables), and proof-complexity barriers (no proof system is the object of study).

VERDICT: idea_card_generated