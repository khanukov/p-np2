# Final verdict


Idea id: `idea-1779300193-8d8f8f`
Created: 2026-05-20T18:03:13+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:03:13+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:04:11+00:00 |

## Thesis

We propose a separation strategy targeting a **specific structured NP problem** — the **Rectangular Permanent Coincidence Problem (RPCP)**: deciding, given two arithmetic circuits $C_1, C_2$ over $\mathbb{Z}$ of polynomial size computing $n \times n$ integer matrices, whether $\mathrm{perm}(C_1(x)) = \mathrm{perm}(C_2(x))$ on at least one input $x \in \{0,1\}^n$. The strategy combines **proof-complexity lifting** with **GCT-style symmetry obstructions**: we conjecture and aim to prove that any subexponential nondeterministic algorithm for RPCP would yield, via Pich–Krajíček-style witnessing in $V^1_2$ + extension, a formal proof of a permanent-vs-determinant containment that is *provably refuted* by an orbit-closure obstruction in the Mulmuley–Sohoni programme (specifically, a Kronecker-coefficient–based occurrence obstruction shown by Bürgisser–Ikenmeyer–Panova-style methods to separate the relevant $\mathrm{GL}_{n^2}$ orbit closures). The obstruction is a representation-theoretic invariant of a **measure-zero algebraic variety** (the permanent orbit closure), not of generic Boolean functions. The Lean target encodes RPCP-hardness as a `ResearchGapWitness` whose validity is reduced to (a) a bounded-arithmetic non-provability statement and (b) an explicit representation-theoretic non-occurrence. Neither component is constructive on truth tables, neither holds on a positive measure of Boolean functions, and both fail to relativize because they depend on the algebraic structure of the permanent polynomial that no oracle preserves.

