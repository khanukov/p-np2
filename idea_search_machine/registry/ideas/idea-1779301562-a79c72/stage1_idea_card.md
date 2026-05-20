# Idea Card

## 1. Thesis

I propose separating **P from NP** (in the form of a superpolynomial circuit lower bound for an NP language) by reformulating circuit computation as a **subshift of finite type (SFT) on a Cayley-like graph**, then invoking **Hochman–Meyerovitch's characterization of computable topological entropies** to show that any polynomial-size family of circuits computing a particular self-referential NP property forces the resulting 2D SFT to have a topological entropy that is **simultaneously** a right-recursively-enumerable real (by Hochman–Meyerovitch) **and** strictly less than a specific transcendental value determined by the language's Kolmogorov-style description complexity. The contradiction yields the separation.

**Cross-domain bridge**: E14 — topological/symbolic dynamics, specifically the Hochman–Meyerovitch theorem on multidimensional SFT entropies.

**Conclusion**: a specific padded NP-complete language (a "tiling-encoded SAT" variant) cannot be decided by polynomial-size circuit families because the entropy of its associated SFT must lie outside the computable entropies admitting polynomial-rate approximation.

The key novelty: circuit *families* (indexed by input length) are encoded as a **multidimensional shift space** where the second dimension is input length. Lower bounds on circuit size translate to lower bounds on the **complexity of approximating** the SFT's topological entropy from below, a quantity controlled by Hochman–Meyerovitch rather than by any combinatorial counting / random-restriction argument.

## 2. Prerequisite techniques

**From E14 (primary domain)**:
- M. Hochman and T. Meyerovitch, *"A characterization of the entropies of multidimensional shifts of finite type,"* Annals of Mathematics 171 (2010), 2011–2038. Establishes that the set of topological entropies of d-dimensional SFTs (d ≥ 2) equals the set of non-negative right-recursively-enumerable reals.
- M. Hochman, *"On the dynamics and recursive properties of multidimensional symbolic systems,"* Inventiones Mathematicae 176 (2009), 131–167. Provides the recursive-theoretic machinery for embedding computations into sofic shifts.
- N. Aubrun and M. Sablik, *"Simulation of effective subshifts by two-dimensional subshifts of finite type,"* Acta Applicandae Mathematicae 126 (2013), 35–63. Gives the explicit substitution-based construction translating effective 1D subshifts into 2D SFTs — the bridge needed to encode circuit families.

**Background from complexity theory (background only)**:
- Standard fact that NP-complete tiling problems exist (Lewis–Papadimitriou style bounded tiling).
- Standard size hierarchy / padding arguments.

## 3. Expected mechanism

Let L be a padded NP-complete tiling language. Define a 2D SFT X_L whose horizontal direction encodes a candidate input x and whose vertical direction encodes a purported polynomial-size circuit computation trace. The local constraint rules enforce: (i) gate-level consistency of a circuit C evaluated on x, (ii) the answer matches the membership predicate for L, (iii) the size of C at horizontal coordinate n is bounded by p(n) for a fixed polynomial p.

By Aubrun–Sablik, this is realizable as a genuine 2D SFT (not merely sofic). Its topological entropy h(X_L) measures the asymptotic count of valid (input, polynomial-circuit-trace) pairs per unit area.

**Load-bearing step (E14)**: Hochman–Meyerovitch's theorem characterizes h(X_L) as a right-r.e. real. Crucially, their proof gives **explicit rate-of-approximation bounds** tying the approximation modulus to the time-complexity of the recursive enumeration. If P = NP, the trace constraints become decidable in polynomial time, forcing h(X_L) into a strictly thinner subclass — those right-r.e. reals admitting **polynomial-time approximation from below**.

The contradiction: by a diagonalization that uses self-reference of L against polynomial-time approximators (Kolmogorov-incompressibility flavor, but operating on entropy values rather than truth tables), h(X_L) provably falls outside this thinner subclass. Hence no polynomial-size circuit family decides L.

## 4. Target pnp3 / pnp4 interface

`Pnp3.Separation.NP_not_subset_Ppoly` — the headline statement that the SAT-flavored padded language is not in P/poly. Concretely, target a theorem of the form `∃ L ∈ NP, ∀ p polynomial, ¬ (L ∈ SIZE(p))` instantiated via the SFT-entropy obstruction, packaged as a Lean structure `SFTEntropyObstruction` parallel to existing obstruction structures in the `pnp3` tree.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- **Cluster A (proof complexity)**: Primary mechanism is the Hochman–Meyerovitch entropy characterization for 2D SFTs; no forcing with random variables, no witnessing in V^1_2, no feasible interpolation, no NW-generator-as-axiom. Bounded arithmetic is not invoked.
- **Cluster B (GCT)**: No orbit closures, no plethysms, no Kronecker coefficients, no symmetric-function representation theory. The objects are symbolic dynamical systems, not algebraic varieties under group action.
- **Cluster C (natural property variants)**: Primary obstruction is a *dynamical-systems entropy* of an SFT, not a property of truth tables. No Fourier concentration, no shrinkage, no Betti numbers of truth tables, no overlap-gap. The obstruction is non-constructive in the natural-proofs sense because computing the entropy approximation itself requires solving the decision problem.
- **Cluster D (hardness magnification)**: No MCSP, no Gap-MCSP, no magnification chain, no weak-to-strong amplification on meta-computational problems. The lower bound is direct on a padded tiling language.
- **Cluster E (standard barrier workarounds)**: No relativization-evasion via "specific syntax", no LPS expanders, no OWF transfer. Barrier evasion comes from the entropy approximation rate being a non-relativizing invariant of the SFT.

**Cross-domain bridge chosen**: E14 — multidimensional symbolic dynamics, specifically Hochman–Meyerovitch's entropy characterization plus Aubrun–Sablik's SFT realization of effective subshifts.

**Three alternative bridges considered before settling**:
- **Alternative 1**: E8 (Ricci curvature on graphs / Wasserstein flows on circuit distributions), rejected because optimal-transport approaches to complexity have been quietly explored in connection with mixing-time / spectral arguments, putting it adjacent to the spectral-concentration sub-cluster (C).
- **Alternative 2**: E1 (subfactors / Jones index applied to circuit semantics), rejected because Jones-index obstructions have recently appeared in quantum complexity contexts (MIP* = RE neighborhood), making the bridge less unexplored than it first appears.
- **Alternative 3**: E11 (automorphic L-functions for hardness), rejected because the only known way to deploy L-functions in complexity is currently LPS-expander-flavored, which is explicitly listed in Cluster E.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: multidimensional SFT entropy characterization has zero footprint in circuit complexity literature; Hochman–Meyerovitch is cited in computability theory and ergodic theory but has never been invoked as a lower-bound mechanism for Boolean circuits.

**Genuine novelty escape**: cross-domain bridge from E14 plus a barrier-evasion mechanism in which the lower bound is extracted from the **rate-of-approximation hierarchy of right-r.e. reals** — an invariant that is neither relativizing (it depends on the specific recursive structure of the SFT's local rules), nor algebrizing (no polynomial extension is involved), nor naturalizable (computing the entropy approximation rate is itself not in P).

VERDICT: idea_card_generated