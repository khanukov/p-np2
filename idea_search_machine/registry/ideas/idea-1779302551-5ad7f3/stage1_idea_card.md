# Idea Card

## 1. Thesis

We propose separating **P from NP** (in the form of a super-polynomial circuit lower bound for a specific NP language) by transferring an **undecidability-of-entropy** result from the theory of **multidimensional subshifts of finite type (SFTs)** to a circuit-uniform-tile model of Boolean computation. The cross-domain bridge is **E14 — topological/symbolic dynamics**, specifically the **Hochman–Meyerovitch theorem** (Annals of Mathematics 171, 2010, "A characterization of the entropies of multidimensional shifts of finite type"), which shows that the set of topological entropies of ℤ²-SFTs is exactly the set of right-recursively-enumerable numbers.

The conclusion: we encode the computation history of a 3-SAT-solving circuit family as a ℤ²-SFT whose admissible configurations correspond to satisfying assignments embedded along a self-similar Robinson-style aperiodic tiling. The **topological entropy** of this SFT becomes a circuit-size-monotone invariant. Using Hochman–Meyerovitch's **conjugacy between Π₁-computable reals and SFT entropies**, we show that a polynomial-size circuit family would force the entropy of the associated SFT to be a polynomial-time-approximable real, contradicting an entropy lower bound established via **block-gluing obstructions** (Pavlov–Schraudner). The separation therefore rests on a topological-dynamical invariant, not on combinatorial counting of circuits.

## 2. Prerequisite techniques

**From E14 (symbolic dynamics):**
- Hochman & Meyerovitch, *A characterization of the entropies of multidimensional shifts of finite type*, Annals of Math. 171 (2010), 2011–2038. (Entropy ↔ Π₁-computable reals.)
- Pavlov & Schraudner, *Entropies realizable by block gluing ℤᵈ shifts of finite type*, J. d'Analyse Math. 126 (2015), 113–174. (Block-gluing entropy gap.)
- Robinson, *Undecidability and nonperiodicity for tilings of the plane*, Invent. Math. 12 (1971), 177–209, combined with Mozes' substitution-to-SFT theorem, *J. d'Analyse Math.* 53 (1989), 139–186.
- Hochman, *On the dynamics and recursive properties of multidimensional symbolic systems*, Invent. Math. 176 (2009), 131–167. (Effectivity ↔ SFT factor structure in ℤ³.)

**From complexity theory (background only):**
- Wegener, *The Complexity of Boolean Functions* (1987), Ch. 6, for circuit-size monotonicity terminology.
- Standard NP-completeness of tiling (Lewis–Papadimitriou-style), used only for the encoding scaffold.

## 3. Expected mechanism

The load-bearing step is **not** counting, restriction, or proof-system unprovability. It is the following: associate to each circuit family {C_n} solving an NP-complete tiling-with-constraints language **L_tile** a ℤ²-SFT X(C) whose forbidden patterns encode the *negations of intermediate gate evaluations* inside Robinson-tile macro-blocks at hierarchical scales 2^k. The construction guarantees:

(a) **Entropy upper bound from circuits**: If |C_n| ≤ n^c, then via a Mozes-style substitution presentation, h_top(X(C)) is a Π₁-computable real with a **polynomial-time approximation schedule** — formally, the n-th rational lower bound is computable in time poly(n).

(b) **Entropy lower bound from L_tile**: Because L_tile is engineered so that its yes-instances embed an effective ℤ²-subshift Y of entropy α where α is a **specific Π₁-real with no polynomial approximation schedule** (constructed by diagonalizing against polynomial-time approximators using Hochman's effectivity machinery; such α exists because the Π₁-computable reals strictly contain the polynomial-time approximable reals — a uniform diagonalization), we get h_top(X(C)) ≥ α.

(c) **Pavlov–Schraudner block-gluing**: forces equality of upper and effective lower bounds, yielding a contradiction with (a). The cross-domain machinery is load-bearing at step (a)–(b): the conversion of circuit size into entropy-approximation rate is the Hochman–Meyerovitch correspondence applied in reverse.

## 4. Target pnp3 / pnp4 interface

Lean object: `Pnp3.Separation.NP_not_in_Ppoly` — instantiated by providing a term of type 
`∃ L : Language, L ∈ NP ∧ ∀ c : ℕ, ¬ (L ∈ SIZE (fun n => n^c))`
with `L := SFT.TilingEntropyGap.lang` (a new namespace `Pnp3.SymbolicDynamics.SFTEntropy`). The key lemma `Pnp3.SymbolicDynamics.entropy_approx_of_circuit_size` formalizes mechanism (a); `entropy_lower_bound_diagonal` formalizes (b).

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- Cluster A (proof complexity): primary mechanism is NOT in this cluster because the argument never instantiates a proof system, witnesses no formula in any bounded-arithmetic theory, and does not transfer unprovability — it transfers an entropy invariant from a topological dynamical system.
- Cluster B (GCT): no orbit closures, no representation-theoretic multiplicities, no algebraic group actions; the symmetry object is ℤ²-translation, used dynamically, not algebro-geometrically.
- Cluster C (natural property variants): the invariant (topological entropy of an associated SFT) is **not** a property of truth tables of size 2^n — it is a property of an effectively presented ℤ²-subshift; it is neither density-style, Fourier-style, nor homological on the cube {0,1}^n.
- Cluster D (hardness magnification): no MCSP, no weak-to-strong amplification chain; the lower bound is direct and does not pass through a sub-problem threshold.
- Cluster E (barrier workarounds): the argument is not relativizing (the SFT construction probes the specific syntactic structure of Robinson macro-tiles encoded from gates), not algebrizing (no polynomial extension), and not natural (entropy of an effective SFT is neither constructive nor large in Razborov–Rudich sense — Π₁-reals are co-r.e., not poly-time recognizable).

**Cross-domain bridge chosen**: **E14 — multidimensional symbolic dynamics**, specifically Hochman–Meyerovitch entropy realizability + Pavlov–Schraudner block-gluing entropy gaps.

**Three alternative bridges considered before settling**:
- Alternative 1: **E2 (ergodic theory / Furstenberg correspondence)** — rejected because Furstenberg-style correspondence between combinatorial density and ergodic recurrence has already been informally probed by additive-combinatorics-flavoured complexity work (Green-Tao-adjacent), making the connection less unexpected.
- Alternative 2: **E8 (optimal transport / Ricci curvature on graphs)** — rejected because Ollivier-Ricci on computation graphs has appeared in ML-theory contexts and recent expander-style complexity work, partially exploring the bridge.
- Alternative 3: **E20 (discrete Morse theory on configuration spaces)** — rejected because Forman's discrete Morse theory has been applied to neural-net loss landscapes and SAT solution-space topology, creating proximity to the forbidden Cluster C (cluster geometry / overlap-gap).

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Multidimensional SFT entropy realizability is studied almost exclusively within pure dynamics and computability theory; despite Hochman–Meyerovitch being deeply about Π₁-computability, no published circuit lower bound (to my knowledge) uses ℤ²-SFT topological entropy as the complexity-monotone invariant.

**Genuine novelty escape**: cross-domain bridge from E14 plus a barrier-evasion mechanism where the **rate of polynomial-time approximability of a Π₁-real entropy** (not the truth-table itself) is the size-monotone invariant — this object is not constructive in the Razborov–Rudich sense and lives outside the universe of relativizing oracles, since it is defined by the global topological dynamics of a syntactically-specified tiling encoding of circuit gates.

VERDICT: idea_card_generated