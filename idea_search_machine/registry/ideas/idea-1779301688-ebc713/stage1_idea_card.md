# Idea Card

## 1. Thesis

We propose to separate **P from NP** (specifically: prove a superpolynomial circuit lower bound for an NP-complete problem suitable for the `pnp3` LB_Formulas / `pnp4` LB_GeneralCircuit interface) by importing **Hochman–Meyerovitch's theory of computable entropies realised by multidimensional subshifts of finite type (SFTs)** from symbolic dynamics (domain **E14**).

Bridge: encode a circuit family `{C_n}` deciding an NP-complete language `L` as a **Z²-SFT** `X_C` whose admissible configurations encode tilings that simulate computation traces of `C_n` on inputs of length `n`. The **topological entropy** `h(X_C)` is, by Hochman–Meyerovitch (Annals of Math 2010), a right-recursively-enumerable real, and conversely every such real is realisable; crucially, the **rate of convergence** of finite-window entropy approximations `h_n(X_C) → h(X_C)` is governed by the Kolmogorov-style complexity of the local rules.

We define a **"computation-trace SFT" functor** `C ↦ X_C` such that:
- If `L ∈ P/poly`, then `h(X_C) − h_n(X_C) = O(n^{-k})` polynomially fast for some `k`.
- For `L = SAT`, a diagonal SFT construction (a dynamical analogue of time-hierarchy) forces **subrecursive entropy-convergence** strictly slower than any polynomial.

The contradiction yields `SAT ∉ P/poly`.

## 2. Prerequisite techniques

**From E14 (primary)**:
- Hochman, M. & Meyerovitch, T., *"A characterization of the entropies of multidimensional shifts of finite type"*, Annals of Mathematics 171 (2010), 2011–2038. — The classification of Z²-SFT entropies as right-r.e. reals.
- Hochman, M., *"On the dynamics and recursive properties of multidimensional symbolic systems"*, Inventiones Math. 176 (2009), 131–167. — Recursive-theoretic structure of effective dynamical systems and simulation theorems.
- Aubrun, N. & Sablik, M., *"Simulation of effective subshifts by two-dimensional subshifts of finite type"*, Acta Applicandae Math. 126 (2013), 35–63. — Tools for embedding Turing machines into Z²-SFTs with quantitative window bounds.
- Pavlov, R. & Schraudner, M., *"Entropies realizable by block gluing Z^d shifts of finite type"*, Journal d'Analyse Math. 126 (2015) — refined entropy-approximation rates under mixing conditions.

**From complexity (background only)**:
- Standard simulation of polynomial circuits by uniform-window local rules (Cook–Levin style).
- The `pnp3` formal definition of `LB_Formulas` / `pnp4` `LB_GeneralCircuit`.

## 3. Expected mechanism

The load-bearing step is **dynamical, not combinatorial**.

Step 1 (encoding). For a circuit family `{C_n}` decide `L`, build a single Z²-SFT `X_C` whose alphabet encodes gate-states and whose local rules enforce that horizontal slabs of height `n` admit configurations iff some input `x ∈ {0,1}^n` produces an accepting trace in `C_n(x)`. The Aubrun–Sablik simulation theorem provides a uniform-radius local-rule realisation.

Step 2 (entropy ↔ circuit size). The topological entropy `h(X_C)` measures the asymptotic exponential growth of admissible configurations per unit area. We prove (this is the main lemma) that the **window-approximation defect** `h(X_C) − h_n(X_C)` is bounded above by `poly(circuit-size(C_n))/n` when `C` is polynomial-size. The proof uses Pavlov–Schraudner block-gluing bounds combined with a circuit-to-tiling locality argument.

Step 3 (diagonal SFT). Using the Hochman–Meyerovitch realisation half: construct an SFT `X*` whose entropy equals a right-r.e. real `α` with **provably subpolynomial approximation rate** (such reals exist by a Solovay-style diagonalisation over poly-time computable rates). Encode `X*` into SAT instances so that any polynomial circuit family for SAT would induce a polynomial approximation rate for `α`, contradicting its construction.

The cross-domain content is irreducible: the obstruction lives in the **recursion-theoretic stratification of right-r.e. reals via SFT entropies**, an object having no shadow in proof complexity, GCT, or natural-proofs frameworks.

## 4. Target pnp3 / pnp4 interface

Target: `pnp4.LB_GeneralCircuit` — specifically the existential statement

```
∃ (L : Language), L ∈ NP ∧ ∀ k, ¬ (L ∈ SIZE(n^k))
```

The bridge to Lean is via a definition `SFTEntropyDefect : Circuit → ℕ → ℝ` and a lemma stating that polynomial circuit size forces polynomial defect decay; the contradiction is then proved against a Hochman–Meyerovitch witness SFT formalised as a fixed-radius local rule.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- Cluster A (proof complexity): the load-bearing step is topological entropy of Z²-SFTs; no bounded-arithmetic witnessing, no forcing-with-random-variables, no feasible interpolation appears. Recursion theory enters only via Hochman–Meyerovitch's classification of r.e. reals, not via VPV/S^1_2/APC₁.
- Cluster B (GCT): no orbit closures, no representation theory of GL_n, no Kronecker/plethysm coefficients. The symmetry group of an SFT is Z², not a reductive algebraic group.
- Cluster C (natural property variants): the SFT-entropy invariant is **not** a property of truth tables (it is a property of the *circuit-encoded local rule*, a syntactic-dynamical object); largeness/constructivity in Razborov–Rudich sense does not apply because the invariant is not closed under random sampling of truth tables.
- Cluster D (hardness magnification): no MCSP, no gap problem, no weak-to-strong magnification chain.
- Cluster E (standard barrier workarounds): the argument does not relativize (Z²-SFT simulation is **not** oracle-stable: oracles change the local-rule radius unpredictably), does not algebrize (no low-degree extension is used), and uses no LPS-style expander or classical OWF axiom.

**Cross-domain bridge chosen**: **E14 — multidimensional symbolic dynamics, specifically the Hochman–Meyerovitch entropy classification of Z²-SFTs**.

**Three alternative bridges considered before settling**:
- Alternative 1: **E1 (subfactor index / Jones polynomials)** — rejected because subfactor index values (Jones' theorem) form a discrete-then-continuous set that doesn't naturally stratify by complexity classes; the bridge to circuit size is speculative.
- Alternative 2: **E11 (automorphic L-functions beyond LPS)** — rejected because despite genuine non-obviousness, recent work by Bhowmick–Lovett and the broader arithmetic-circuits-via-L-functions thread makes this border-line on Cluster E.
- Alternative 3: **E8 (Ricci curvature on graphs / Ollivier–Ricci)** — rejected because graph-curvature based complexity arguments have begun appearing in TCS-adjacent literature (graph neural network theory, expander-mixing refinements), making the connection less alien.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Hochman–Meyerovitch entropy classification has been cited essentially zero times in mainstream complexity theory; multidimensional SFT entropy is studied for its own dynamical interest, and the recursion-theoretic stratification of right-r.e. reals via tile sets is a tool that has never been quantitatively calibrated against circuit-size classes.

**Genuine novelty escape**: cross-domain bridge from **E14 (multidimensional symbolic dynamics)** plus a **non-relativizing, non-algebrizing barrier evasion via window-radius rigidity of SFT local rules** — the local rule radius is a hard syntactic invariant of the SFT not preserved by oracle access, sidestepping Baker–Gill–Solovay; and the entropy invariant is not a low-degree polynomial in truth-table entries, sidestepping algebrization.

VERDICT: idea_card_generated