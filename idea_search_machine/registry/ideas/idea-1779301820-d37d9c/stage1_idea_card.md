# Idea Card

## 1. Thesis

I propose to separate **P from NP** (specifically, to lower-bound general Boolean circuits computing a specific NP-hard tiling-derived language) by importing the **undecidability and entropy machinery of multidimensional subshifts of finite type (SFTs)** from symbolic dynamics. The bridge is **E14 — topological/symbolic dynamics**, specifically the Hochman–Meyerovitch theorem characterising the set of topological entropies of ℤ²-SFTs as exactly the right-recursively-enumerable reals, together with Hochman's later work on effective dynamical systems as factors of SFTs.

The core idea: encode a parametrised family of NP instances as **finite patches of a ℤ²-SFT** whose **patch-complexity function** p_n (number of globally extendable n×n patterns) has a growth rate controlled by the topological entropy h. Hochman–Meyerovitch lets us *design* an SFT whose entropy equals a chosen right-r.e. real encoding a hard computation, while the **Desai entropy-density theorem** (and the simulation theorem of Aubrun–Sablik / Durand–Romashchenko–Shen) forces any sub-exponential **circuit** decoding patch-extendability to violate a **factor-map entropy inequality**. The conclusion is a super-polynomial circuit lower bound for the language "is this n×n patch globally extendable in 𝒮", which is NP-complete by Berger-style reduction.

The novelty is that the lower bound is extracted not from a combinatorial / Fourier / algebraic invariant of the function, but from a **dynamical-systems invariant (topological entropy and its factor behaviour) of the language's natural ℤ²-shift presentation**.

## 2. Prerequisite techniques

**From E14 — symbolic / topological dynamics:**

- Hochman, M. & Meyerovitch, T., *"A characterization of the entropies of multidimensional shifts of finite type,"* Annals of Mathematics 171 (2011), 2011–2038. Establishes that the set of topological entropies of ℤ^d SFTs (d≥2) equals the right-recursively-enumerable non-negative reals. This is the load-bearing simulation theorem.
- Aubrun, N. & Sablik, M., *"Simulation of effective subshifts by two-dimensional subshifts of finite type,"* Acta Applicandae Mathematicae 126 (2013), 35–63. Provides the explicit factor-map construction from any Π₁-effective subshift to a ℤ²-SFT, preserving entropy quantitatively.
- Hochman, M., *"On the dynamics and recursive properties of multidimensional symbolic systems,"* Inventiones Mathematicae 176 (2009), 131–167. Gives the effective-dynamics-as-factors framework and the *quantitative* control on patch-complexity needed to translate circuit size bounds into entropy bounds.
- (Supporting) Pavlov, R. & Schraudner, M., *"Entropies realizable by block-gluing ℤ^d shifts of finite type,"* J. d'Analyse Mathématique 126 (2015) — gives mixing-class refinements.

**From complexity theory (background only):**

- Berger's classical tiling undecidability + its finite analogue (bounded domino problem is NP-complete).
- Standard worst-case circuit-size definitions in `pnp3`.

## 3. Expected mechanism

Fix a ℤ²-SFT 𝒮 with alphabet A and forbidden patterns F. Let **L_𝒮 = {w ∈ A^{n×n} : w extends to a configuration in 𝒮}**. By Berger / Robinson, choosing F appropriately makes L_𝒮 NP-complete (bounded tiling).

Suppose, for contradiction, a circuit family {C_n} of size s(n) = n^k decides L_𝒮. Then the *patch-complexity* function p_𝒮(n) = |L_𝒮 ∩ A^{n×n}| is computable by an n^{O(k)}-time enumeration: iterate C_n over A^{n²}.

Now invoke Hochman–Meyerovitch in **reverse**: choose 𝒮 so that its topological entropy h(𝒮) = lim (1/n²) log p_𝒮(n) is a right-r.e. real whose **rate of approximation from above is provably slow** — specifically, encoding a halting-time function of a fixed universal machine on inputs of length log n. The Aubrun–Sablik simulation gives explicit quantitative control: the n-th rational upper approximant to h(𝒮) requires reading patches of size at least Φ(n), where Φ is the busy-beaver-like function from the simulated computation.

A polynomial-size circuit enumerating L_𝒮 would yield an n^{O(k)}-time upper approximant to h(𝒮) of accuracy 2^{-n²}, contradicting the constructed slow-approximation lower bound. The load-bearing step is the **factor-map entropy quantitative inequality** of Hochman 2009 §4, which is intrinsically dynamical — it has no Fourier, polynomial, or combinatorial-rectangle analogue.

Crucially, the contradiction passes through *topological entropy*, an invariant defined on infinite-volume limits, not on finite truth tables.

## 4. Target pnp3 / pnp4 interface

The target Lean interface is `pnp3/Core/BooleanCircuit.lean`'s definition `Circuit.computes` combined with the worst-case size definition `CircuitSize`. The specific theorem statement to formalise:

`theorem tiling_lower_bound : ∀ k, ∃ N, ∀ n ≥ N, ∀ C : Circuit (Fin (n*n) → Bool), C.computes (L_S n) → C.size > n^k`

where `L_S` is the Lean encoding of the bounded tiling language for the Hochman–Meyerovitch-constructed SFT 𝒮, defined in a new file `pnp4/Dynamics/SFTEntropy.lean`. The bridge to P ≠ NP uses the existing `pnp3` reduction infrastructure from SAT to bounded tiling.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- Cluster A (proof complexity): primary mechanism is **topological entropy of ℤ²-SFTs and factor-map inequalities**; no forcing with random variables, no witnessing theorem, no bounded-arithmetic formula complexity, no propositional proof system whatsoever.
- Cluster B (GCT): no orbit closures, no representation-theoretic multiplicities, no Kronecker/plethysm; the invariant is a real-valued dynamical entropy, not a representation-theoretic multiplicity.
- Cluster C (natural property variants): the lower bound is not extracted from a property of the truth table viewed as a Boolean function (no Fourier, no shrinkage, no density, no topology of the function's level sets); it is extracted from the **infinite-volume thermodynamic limit** of the language's tiling presentation.
- Cluster D (hardness magnification): no MCSP, no gap problem, no magnification chain; the hardness is for a *specific* NP-complete tiling language directly.
- Cluster E (standard barrier workarounds): no relativization-evasion via syntax, no LPS expanders, no OWF axiom; the non-relativizing ingredient is the Hochman–Meyerovitch construction, which is genuinely about ℤ² recursion-theoretic geometry.

**Cross-domain bridge chosen**: **E14 — symbolic dynamics**, specifically multidimensional SFT entropy realisation and factor-map quantitative entropy bounds.

**Three alternative bridges considered before settling**:
- Alternative 1: **E1 (subfactors / Jones index)** — rejected because while Jones-index gating of computation flow is intriguing, no published subfactor result gives a *quantitative* size-vs-index bound usable as a lower-bound engine; the connection would be analogy-only.
- Alternative 2: **E8 (optimal transport / Ricci on graphs)** — rejected because Ollivier-Ricci on computation DAGs has already been informally explored in ML-theory circles and risks proximity to Cluster C spectral/geometric arguments.
- Alternative 3: **E20 (discrete Morse theory)** — rejected because Forman's discrete vector fields on circuit configuration spaces would most likely collapse into a Betti-number argument, brushing against the forbidden Cluster C persistent-homology line.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Multidimensional SFT entropy realisation (Hochman–Meyerovitch) lives in pure ergodic/symbolic dynamics; despite the tiling-NP folklore link, **no published complexity lower bound uses topological entropy of the language's shift presentation as the hardness invariant** — the existing tiling/complexity literature stops at undecidability/NP-completeness and never crosses into the quantitative entropy realisation theorems.

**Genuine novelty escape**: cross-domain bridge from E14 (Hochman–Meyerovitch entropy realisation + Aubrun–Sablik simulation) combined with the **barrier evasion mechanism that the lower bound is mediated by an infinite-volume invariant (topological entropy) whose value is provably slow-to-approximate** — this is non-relativizing because the construction uses explicit ℤ² geometric self-simulation, non-algebrizing because there is no polynomial extension structure, and non-natural because the "largeness" condition is on a single specific language family parametrised by a fixed universal machine, not on a dense subset of Boolean functions.

VERDICT: idea_card_generated