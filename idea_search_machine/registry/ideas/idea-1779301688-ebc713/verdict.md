# Final verdict


Idea id: `idea-1779301688-ebc713`
Created: 2026-05-20T18:28:08+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:28:08+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:29:14+00:00 |

## Thesis

We propose to separate **P from NP** (specifically: prove a superpolynomial circuit lower bound for an NP-complete problem suitable for the `pnp3` LB_Formulas / `pnp4` LB_GeneralCircuit interface) by importing **Hochman–Meyerovitch's theory of computable entropies realised by multidimensional subshifts of finite type (SFTs)** from symbolic dynamics (domain **E14**).

Bridge: encode a circuit family `{C_n}` deciding an NP-complete language `L` as a **Z²-SFT** `X_C` whose admissible configurations encode tilings that simulate computation traces of `C_n` on inputs of length `n`. The **topological entropy** `h(X_C)` is, by Hochman–Meyerovitch (Annals of Math 2010), a right-recursively-enumerable real, and conversely every such real is realisable; crucially, the **rate of convergence** of finite-window entropy approximations `h_n(X_C) → h(X_C)` is governed by the Kolmogorov-style complexity of the local rules.

We define a **"computation-trace SFT" functor** `C ↦ X_C` such that:
- If `L ∈ P/poly`, then `h(X_C) − h_n(X_C) = O(n^{-k})` polynomially fast for some `k`.
- For `L = SAT`, a diagonal SFT construction (a dynamical analogue of time-hierarchy) forces **subrecursive entropy-convergence** strictly slower than any polynomial.

The contradiction yields `SAT ∉ P/poly`.

