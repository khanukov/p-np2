# Final verdict


Idea id: `idea-1779300899-35eed6`
Created: 2026-05-20T18:14:59+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:14:59+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:15:47+00:00 |

## Thesis

We propose to separate NP from P/poly by leveraging a **proof-complexity-to-circuit-lower-bound transfer** specific to a *non-natural, non-relativizing* witness: the **unprovability of NP-hardness lower-bound statements in the bounded arithmetic theory `VNC^1`** (or `V^0_2`) for a *specific* canonical NP-complete problem — namely, a tailored variant of **TAUT for resolution-with-substitution refutation lengths on Tseitin formulas over expander graphs**. The thesis is that, conditional on a *witnessing meta-theorem* (à la Krajíček–Pich), the existence of polynomial-size P/poly circuits deciding this Tseitin variant would yield a `VNC^1`-formalizable algorithm whose correctness proof requires reasoning that provably exceeds `VNC^1`'s capacity, contradicting Pich's "feasible interpolation for unary NP." The escape from natural proofs is structural: the property "this specific Tseitin family on Ramanujan expanders has no polynomial circuit" is **measure-zero** (it singles out one explicit graph sequence) and is **not constructively checkable** on truth tables — verifying membership requires solving an instance of the underlying expansion certificate, which itself is conjecturally outside `AC^0[p]`. The escape from relativization is via the *combinatorial geometry of the specific expander*, which has no oracle analogue. We do **not** count solutions, do not invoke shrinkage, and do not use Fourier / spectral concentration on the truth table.

