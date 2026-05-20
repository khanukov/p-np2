# Final verdict


Idea id: `idea-1779301562-a79c72`
Created: 2026-05-20T18:26:02+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:26:02+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:26:52+00:00 |

## Thesis

I propose separating **P from NP** (in the form of a superpolynomial circuit lower bound for an NP language) by reformulating circuit computation as a **subshift of finite type (SFT) on a Cayley-like graph**, then invoking **Hochman–Meyerovitch's characterization of computable topological entropies** to show that any polynomial-size family of circuits computing a particular self-referential NP property forces the resulting 2D SFT to have a topological entropy that is **simultaneously** a right-recursively-enumerable real (by Hochman–Meyerovitch) **and** strictly less than a specific transcendental value determined by the language's Kolmogorov-style description complexity. The contradiction yields the separation.

**Cross-domain bridge**: E14 — topological/symbolic dynamics, specifically the Hochman–Meyerovitch theorem on multidimensional SFT entropies.

**Conclusion**: a specific padded NP-complete language (a "tiling-encoded SAT" variant) cannot be decided by polynomial-size circuit families because the entropy of its associated SFT must lie outside the computable entropies admitting polynomial-rate approximation.

The key novelty: circuit *families* (indexed by input length) are encoded as a **multidimensional shift space** where the second dimension is input length. Lower bounds on circuit size translate to lower bounds on the **complexity of approximating** the SFT's topological entropy from below, a quantity controlled by Hochman–Meyerovitch rather than by any combinatorial counting / random-restriction argument.

