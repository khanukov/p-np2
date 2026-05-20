# Final verdict


Idea id: `idea-1779302551-5ad7f3`
Created: 2026-05-20T18:42:31+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:42:31+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:43:23+00:00 |

## Thesis

We propose separating **P from NP** (in the form of a super-polynomial circuit lower bound for a specific NP language) by transferring an **undecidability-of-entropy** result from the theory of **multidimensional subshifts of finite type (SFTs)** to a circuit-uniform-tile model of Boolean computation. The cross-domain bridge is **E14 — topological/symbolic dynamics**, specifically the **Hochman–Meyerovitch theorem** (Annals of Mathematics 171, 2010, "A characterization of the entropies of multidimensional shifts of finite type"), which shows that the set of topological entropies of ℤ²-SFTs is exactly the set of right-recursively-enumerable numbers.

The conclusion: we encode the computation history of a 3-SAT-solving circuit family as a ℤ²-SFT whose admissible configurations correspond to satisfying assignments embedded along a self-similar Robinson-style aperiodic tiling. The **topological entropy** of this SFT becomes a circuit-size-monotone invariant. Using Hochman–Meyerovitch's **conjugacy between Π₁-computable reals and SFT entropies**, we show that a polynomial-size circuit family would force the entropy of the associated SFT to be a polynomial-time-approximable real, contradicting an entropy lower bound established via **block-gluing obstructions** (Pavlov–Schraudner). The separation therefore rests on a topological-dynamical invariant, not on combinatorial counting of circuits.

