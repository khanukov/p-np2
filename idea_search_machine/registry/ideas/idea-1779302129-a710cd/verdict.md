# Final verdict


Idea id: `idea-1779302129-a710cd`
Created: 2026-05-20T18:35:29+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:35:29+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:36:13+00:00 |

## Thesis

We propose separating **P from NP** (specifically, exhibiting a super-polynomial circuit lower bound for an NP language, targeting `MCSP`-adjacent or `SAT`-encoded problems in the `pnp3` framework) via a **Ricci-curvature obstruction on the configuration graph of partial computations**.

The cross-domain bridge is **E8 (differential/metric geometry on graphs)**, specifically the **Ollivier-Ricci curvature** and **entropic curvature-dimension condition CD(K,∞)** as developed by Erbar-Maas for discrete Markov chains. We associate to each Boolean function `f : {0,1}^n → {0,1}` a canonical reversible Markov chain `M_f` on the "decision-DAG quotient space" of partial assignments weighted by `f`-consistency. We show:

1. Polynomial-size circuits computing `f` force `M_f` to have **uniformly positive coarse Ricci curvature** (bounded below by `1/poly(n)`), because small circuits induce contractive couplings via gate-by-gate Wasserstein contraction.
2. An explicit NP language `L_RIC` (a padded variant of `SAT` encoded so its consistency chain has known **negative-curvature spectrum** via expander-replacement on the formula's incidence graph) provably has `Ric(M_{L_RIC}) ≤ -Ω(1)` for infinitely many input lengths.
3. Combining (1) and (2) separates the language from P/poly, hence `P ≠ NP`.

The separating invariant — *coarse Ricci curvature of the consistency Markov chain* — is **circuit-monotone** but is **not a property of the truth table's measure**, so it evades natural-proofs largeness.

