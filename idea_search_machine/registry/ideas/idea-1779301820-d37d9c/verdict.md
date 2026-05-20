# Final verdict


Idea id: `idea-1779301820-d37d9c`
Created: 2026-05-20T18:30:20+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:30:20+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:31:14+00:00 |

## Thesis

I propose to separate **P from NP** (specifically, to lower-bound general Boolean circuits computing a specific NP-hard tiling-derived language) by importing the **undecidability and entropy machinery of multidimensional subshifts of finite type (SFTs)** from symbolic dynamics. The bridge is **E14 — topological/symbolic dynamics**, specifically the Hochman–Meyerovitch theorem characterising the set of topological entropies of ℤ²-SFTs as exactly the right-recursively-enumerable reals, together with Hochman's later work on effective dynamical systems as factors of SFTs.

The core idea: encode a parametrised family of NP instances as **finite patches of a ℤ²-SFT** whose **patch-complexity function** p_n (number of globally extendable n×n patterns) has a growth rate controlled by the topological entropy h. Hochman–Meyerovitch lets us *design* an SFT whose entropy equals a chosen right-r.e. real encoding a hard computation, while the **Desai entropy-density theorem** (and the simulation theorem of Aubrun–Sablik / Durand–Romashchenko–Shen) forces any sub-exponential **circuit** decoding patch-extendability to violate a **factor-map entropy inequality**. The conclusion is a super-polynomial circuit lower bound for the language "is this n×n patch globally extendable in 𝒮", which is NP-complete by Berger-style reduction.

The novelty is that the lower bound is extracted not from a combinatorial / Fourier / algebraic invariant of the function, but from a **dynamical-systems invariant (topological entropy and its factor behaviour) of the language's natural ℤ²-shift presentation**.

