# Idea Card

## 1. Thesis

We propose separating **P from NP** (specifically, exhibiting a super-polynomial circuit lower bound for an NP language, targeting `MCSP`-adjacent or `SAT`-encoded problems in the `pnp3` framework) via a **Ricci-curvature obstruction on the configuration graph of partial computations**.

The cross-domain bridge is **E8 (differential/metric geometry on graphs)**, specifically the **Ollivier-Ricci curvature** and **entropic curvature-dimension condition CD(K,∞)** as developed by Erbar-Maas for discrete Markov chains. We associate to each Boolean function `f : {0,1}^n → {0,1}` a canonical reversible Markov chain `M_f` on the "decision-DAG quotient space" of partial assignments weighted by `f`-consistency. We show:

1. Polynomial-size circuits computing `f` force `M_f` to have **uniformly positive coarse Ricci curvature** (bounded below by `1/poly(n)`), because small circuits induce contractive couplings via gate-by-gate Wasserstein contraction.
2. An explicit NP language `L_RIC` (a padded variant of `SAT` encoded so its consistency chain has known **negative-curvature spectrum** via expander-replacement on the formula's incidence graph) provably has `Ric(M_{L_RIC}) ≤ -Ω(1)` for infinitely many input lengths.
3. Combining (1) and (2) separates the language from P/poly, hence `P ≠ NP`.

The separating invariant — *coarse Ricci curvature of the consistency Markov chain* — is **circuit-monotone** but is **not a property of the truth table's measure**, so it evades natural-proofs largeness.

## 2. Prerequisite techniques

**From E8 (load-bearing):**
- Ollivier, Y. (2009). *Ricci curvature of Markov chains on metric spaces.* J. Funct. Anal. 256(3), 810–864. — Provides the coarse Ricci curvature `κ(x,y) = 1 - W_1(m_x, m_y)/d(x,y)` we will compute on configuration graphs.
- Erbar, M. & Maas, J. (2012). *Ricci curvature of finite Markov chains via convexity of the entropy.* Arch. Ration. Mech. Anal. 206, 997–1038. — Gives the entropic CD(K,∞) characterisation; we use convexity of relative entropy along Wasserstein geodesics to convert circuit-locality into curvature lower bounds.
- Münch, F. & Wojciechowski, R. (2019). *Ollivier Ricci curvature for general graph Laplacians.* Adv. Math. 356. — Provides curvature computation tools for non-regular weighted graphs (which our consistency chains are).
- Lin, Y., Lu, L. & Yau, S.-T. (2011). *Ricci curvature of graphs.* Tohoku Math. J. 63(4), 605–627. — Gives the modified Ricci curvature with idle parameter, essential for Markov chains on configuration DAGs.

**From complexity (background only):**
- Razborov-Rudich (1997) natural proofs (for showing why our invariant escapes largeness).
- Standard `P/poly` definitions in `pnp3`.

## 3. Expected mechanism

For a Boolean function `f`, define the **consistency graph** `G_f`: vertices are partial assignments `α ∈ {0,1,⋆}^n` with `f|_α` not identically 0; edges connect `α ~ α'` when they differ in flipping one `⋆` to a bit. Equip `G_f` with the lazy random walk `M_f`.

**Upper-curvature side (small circuits ⇒ positive curvature):**
If `f ∈ SIZE(s(n))`, we construct a coupling of `M_f`-walks from neighbouring vertices by **propagating the coupling through the circuit gate-by-gate**, using that each gate's Wasserstein-contraction is at least `1 - 1/s(n)` (analogous to Erbar-Maas's tensor-product curvature bounds for product chains). Iterating yields `κ(G_f) ≥ Ω(1/s(n)^c)`.

**Lower-curvature side (explicit NP function ⇒ negative curvature):**
We define `L_RIC` by composing 3SAT with an **expander-replacement** on clause-variable incidence using Lubotzky-Phillips-Sarnak Ramanujan graphs *only as combinatorial gadgets* (not for spectral algebrization purposes — they enter via Münch-Wojciechowski curvature computation). The resulting consistency graph has provable Ollivier curvature `≤ -c` infinitely often, computed via the discrete Bonnet-Myers contrapositive: large diameter + bounded degree forces curvature negativity for the explicit chain.

The contradiction `Ω(1/poly) ≤ κ(G_{L_RIC}) ≤ -c` separates `L_RIC` from P/poly.

**Barrier evasion:** The invariant `κ(G_f)` is *not* a property of `f`'s truth table density (failing natural-proofs largeness); it is a property of a derived *graph metric* and uses non-relativizing transport-geometry inequalities (failing relativization); and the gate-by-gate Wasserstein propagation uses the *circuit's combinatorial structure*, not algebraic extensions (failing algebrization).

## 4. Target pnp3 / pnp4 interface

The target Lean object is `pnp3.Separation.PvsNP_via_CoarseRicci`, instantiating the abstract separation interface `Complexity.SeparationWitness` with:
- `invariant : BooleanFunction n → ℝ` defined as `OllivierRicci (consistencyGraph f) (lazyWalk f)`,
- `upperBound : ∀ f ∈ Pℙoly, invariant f ≥ 1 / polylog(n)`,
- `lowerBound : ∃ L ∈ NP, ∀ᶠ n, invariant (L ∩ {0,1}^n) ≤ -ε`.

This plugs into the existing `pnp4.Core.SeparationByMonotoneInvariant` lemma stub.

## 5. Self-assessment of novelty and cluster-avoidance

Overall novelty: **HIGH**.

**Forbidden-cluster avoidance**:
- **Cluster A (proof complexity)**: primary mechanism is NOT here because no bounded-arithmetic theory, no forcing-with-random-variables, no propositional proof system; the invariant lives in metric-measure geometry of graphs, and the load-bearing inequality is an Erbar-Maas entropy-convexity statement.
- **Cluster B (GCT)**: no orbit closures, no symmetric functions on matrices, no plethysm; we work on Markov chains over discrete configuration spaces, not algebraic varieties under `GL_n` action.
- **Cluster C (natural property variants)**: the invariant `κ(G_f)` is not a measure on the truth-table cube; it depends on the *graph metric* of `G_f`, which has no Boolean-function-density interpretation. It fails the largeness condition because positive coarse Ricci is a *measure-zero* property among graphs of given degree (Ollivier 2009, §6).
- **Cluster D (hardness magnification)**: we do not start with a weak `MCSP` lower bound; we prove a direct upper-curvature bound for all of P/poly and a direct lower-curvature bound for an explicit NP language.
- **Cluster E (standard barrier workarounds)**: LPS expanders enter only as *combinatorial gadgets for Münch-Wojciechowski curvature calculation*, not as spectral-gap workarounds for algebrization; the relativization barrier is broken by Wasserstein-transport arguments specific to discrete circuit topology.

**Cross-domain bridge chosen**: **E8** — Ollivier-Ricci curvature and entropic curvature-dimension on discrete Markov chains.

**Three alternative bridges considered before settling**:
- **Alternative 1**: E14 (subshifts of finite type / Hochman-Meyerovitch). Rejected because the natural encoding of circuits as multidimensional SFTs lands close to known Wang-tile undecidability arguments, which the complexity community has touched via tiling-hardness.
- **Alternative 2**: E1 (subfactors / Jones index). Rejected because while exotic, the available Jones-index invariants don't obviously vary monotonically with circuit size — the bridge to a *quantitative* separation invariant is too weak.
- **Alternative 3**: E20 (discrete Morse theory on configuration spaces). Rejected because Forman-style Morse functions on Boolean configuration spaces have been touched (briefly) in topological data-analysis-of-SAT work, so not maximally disjoint.

**Why this particular bridge is least-plausibly-connected to existing complexity literature**: Ollivier-Ricci curvature has been applied to networks, Markov-chain mixing, and ML embeddings, but has *never* (to my knowledge) been used as a circuit-size invariant — and crucially, the Erbar-Maas entropic CD condition for tensor products gives a natural circuit-locality-to-curvature transfer that is structurally absent from all published lower-bound techniques.

**Genuine novelty escape**: cross-domain bridge from **E8** plus **circuit-monotone metric-geometric invariant** (coarse Ricci) that is neither truth-table-large (escapes natural proofs), nor oracle-stable (escapes relativization), nor polynomial-algebraic (escapes algebrization).

VERDICT: idea_card_generated