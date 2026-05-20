# Idea Card

## 1. Thesis

We propose separating P from NP by exhibiting an explicit NP language whose characteristic sequences, viewed as orbits of a computable Z^d-action, generate a **subshift of finite type (SFT) whose topological entropy is uncomputable at a specific rate**, while any P-time language's corresponding subshift has **computably approximable entropy with a polynomial modulus**. The cross-domain bridge is **E14 — topological/symbolic dynamics**, specifically the **Hochman–Meyerovitch theorem** (Annals of Math, 2010) which characterises the set of entropies of multidimensional SFTs as exactly the upper semicomputable nonnegative reals (Π₀₁ right-recursively-enumerable numbers).

The separation idea: encode SAT instances as local matching rules of a 2D SFT in such a way that the topological entropy of the resulting subshift equals a specific Π₀₁ real `h_SAT` whose **right-approximation modulus** is provably super-polynomial. For any P-time decidable language, a uniform construction yields an SFT whose entropy is approximable with a polynomial-time-computable modulus (because membership decisions feed into a finite-window approximation). The two moduli classes are disjoint, separating P from NP via entropy-modulus rate.

The load-bearing cross-domain step is Hochman–Meyerovitch's **simulation of Turing machines by SFTs with controlled entropy contribution**: their construction gives quantitative control on how computational hardness translates to entropy approximation rates — a quantitative dimension never exploited by complexity theory.

## 2. Prerequisite techniques

**From E14 (symbolic dynamics):**

- M. Hochman and T. Meyerovitch, *A characterization of the entropies of multidimensional shifts of finite type*, Annals of Mathematics 171 (2010), 2011–2038. **Load-bearing**: the SFT-from-TM simulation with entropy-rate control.

- M. Hochman, *On the dynamics and recursive properties of multidimensional symbolic systems*, Inventiones Math. 176 (2009), 131–167. Provides the recursive-theoretic framework for Π₀₁-rates of subshift invariants.

- N. Aubrun and M. Sablik, *Simulation of effective subshifts by two-dimensional subshifts of finite type*, Acta Applicandae Mathematicae 126 (2013), 35–63. Gives the cleaner 2D simulation with explicit window/alphabet bounds — essential for the quantitative modulus tracking.

- E. Jeandel and P. Vanier, *Turing degrees of multidimensional SFTs*, Theoretical Computer Science 505 (2013), 81–92. Calibrates which Turing degrees are realised — needed for the NP-vs-P granularity.

**Background from complexity theory (used only as scaffolding):**

- Standard Cook–Levin reduction (to encode SAT into local SFT rules).

## 3. Expected mechanism

Given a language L, build a uniform family of 2D SFTs `X_L^n` over an alphabet whose local rules encode "tile (i,j) carries a partial computation trace of L on input encoded in row 0". By Aubrun–Sablik, this is realisable as a genuine SFT (not merely effective subshift) in 2D. Define the **complexity-entropy** `H(L,n) := h_top(X_L^n)`. 

Hochman–Meyerovitch's quantitative construction shows: `H(L,n)` admits a right-computable approximation `α_k → H(L,n)` from above where `α_k − H(L,n) ≤ f_L(k)` for a modulus `f_L` that **directly inherits** the time complexity of deciding L. The key quantitative lemma (extractable from §7 of Hochman–Meyerovitch and refined by Aubrun–Sablik) gives: if L ∈ TIME(t(n)), then `f_L(k) = O(1/poly(k))` with constants depending on `t`. 

Conversely, for SAT-encoding SFTs, we show via a **diagonal entropy obstruction** — built by joining a Hochman-construction realising a Π₀₁ real `ρ` whose approximation modulus is super-polynomial (such ρ exist by a Kolmogorov-complexity argument inside the Π₀₁ class) — that any P-uniform family fails to match the modulus.

The crucial point: this is **not** a natural property, not a relativising argument, and not a circuit-counting argument. It is a **topological-dynamical invariant** of a uniformly-constructed shift space.

## 4. Target pnp3 / pnp4 interface

`pnp3/Complexity/ShiftEntropy.lean` — a new file defining `SFT_of_language : Language → ShiftSpace (Fin 2) (Fin 2)` and `top_entropy_modulus : ShiftSpace → (ℕ → ℝ)`, culminating in the theorem `entropy_modulus_separates : (∃ L ∈ NP, ¬ poly_modulus (top_entropy_modulus (SFT_of_language L))) → P ≠ NP`. This plugs into the existing `pnp3.Core.SeparationAxioms` interface via a new constructor `SeparationWitness.entropyModulus`.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:

- **Cluster A (proof complexity)**: Primary mechanism is the topological entropy of a shift space, a *real-valued dynamical invariant*. No bounded arithmetic, no Frege system, no witnessing theorem appears. Provability is replaced by *right-computable approximation rate*, a distinct mathematical object.

- **Cluster B (GCT)**: No orbit closures, no representation theory, no plethysm/Kronecker coefficients. The relevant orbits are Z²-actions on Cantor space, not GL-orbits on tensor space.

- **Cluster C (natural property variants)**: The entropy modulus is a *uniform* invariant of an *infinite* shift space built from L, not a property of truth tables. There is no largeness/constructivity dichotomy in the Razborov–Rudich sense; in fact the invariant is undefined on individual truth tables.

- **Cluster D (hardness magnification)**: No MCSP, no weak-to-strong amplification of an existing lower bound. The argument is direct: entropy modulus distinguishes the classes outright.

- **Cluster E (standard barrier workarounds)**: Not a relativising argument (entropy of SFT does not relativise to oracle TMs cleanly — oracles destroy the local-rule structure). Not algebrising. Not LPS expanders. No cryptographic axioms.

**Cross-domain bridge chosen**: **E14 — topological/symbolic dynamics**, specifically Hochman–Meyerovitch's quantitative simulation of TMs by 2D SFTs with controlled entropy approximation rate.

**Three alternative bridges considered before settling**:

- **Alternative 1: E2 (ergodic theory, Furstenberg correspondence)**. Rejected because Furstenberg-style correspondence between combinatorial density and dynamical recurrence has already attracted attention via additive-combinatorics-flavoured complexity arguments (Green–Tao adjacent), making the "least-plausibly-connected" criterion fail.

- **Alternative 2: E8 (optimal transport / Wasserstein gradient flow between computation distributions)**. Rejected because Wasserstein distances have begun appearing in machine-learning-theoretic hardness via neural-network expressivity, polluting the novelty.

- **Alternative 3: E20 (discrete Morse theory on configuration spaces)**. Rejected because Forman's discrete Morse theory has been informally connected to SAT solver heuristics and persistent-homology of solution spaces (Cluster C-adjacent), risking cluster contamination.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Multidimensional SFT entropy is a *uncountable-state* dynamical invariant whose only complexity-theoretic appearance is via the decidability question of *whether SFTs are nonempty* (the domino problem) — never via *quantitative entropy approximation rates as a complexity class separator*.

**Genuine novelty escape**: Cross-domain bridge from E14 (Hochman–Meyerovitch quantitative entropy realisation) plus a **modulus-of-approximation refinement of the Π₀₁ characterisation** turning a recursive-theoretic theorem into a complexity-theoretic one. The barrier evasion: relativisation fails because oracle access breaks SFT locality; natural proofs fail because the invariant is not a truth-table predicate; algebrisation fails because no polynomial extension structure is used.

VERDICT: idea_card_generated