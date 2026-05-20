# Final verdict


Idea id: `idea-1779302254-e94d9b`
Created: 2026-05-20T18:37:34+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:37:34+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:38:19+00:00 |

## Thesis

**Thesis**: Separate **P from NP** (specifically, exhibit a language in NP requiring super-polynomial circuits) by encoding SAT-solving circuit families as a **multidimensional subshift of finite type (SFT)** over a structured alphabet, and applying the **Hochman–Meyerovitch characterisation of topological entropies of ℤᵈ-SFTs** (d ≥ 2) together with **Pavlov–Schraudner-type undecidability obstructions** to entropy realisation under uniformly local constraints.

**Bridge (E14)**: Each circuit family `{C_n}` solving SAT induces, via a tile-system encoding of gate-locality + input-encoding consistency, a ℤ²-SFT `X_C` whose topological entropy `h(X_C)` is a Π₁-computable real determined by the circuit-size growth. Boolean circuits of polynomial size yield SFTs whose entropy lies in a restricted "polynomially-presentable" sub-class with effectively computable upper approximations at a controlled rate. The set of SAT-witnessing tile systems, however, must realise entropies forced (by a tile-encoding of #SAT counting via Furstenberg–Weiss-style fibre-entropy decompositions) into a class of right-recursively enumerable reals **without matching left-r.e. upper approximation at polynomial rate**.

**Conclusion**: A polynomial-size SAT-solving circuit family would yield a ℤ²-SFT whose entropy is simultaneously polynomially left-r.e. approximable and equals a quantity forced to be only right-r.e. approximable — contradiction, hence `P ≠ NP`.

