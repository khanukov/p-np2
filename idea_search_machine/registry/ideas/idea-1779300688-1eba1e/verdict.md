# Final verdict


Idea id: `idea-1779300688-1eba1e`
Created: 2026-05-20T18:11:28+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:11:28+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:12:17+00:00 |

## Thesis

We propose attacking P vs NP via a **proof-complexity-to-circuit-lower-bound transfer** route, specifically: showing that any `P/poly` circuit family solving `SAT` would yield a feasibly-constructive proof of a combinatorial statement (a variant of the Paris-Wilkie / dual-weak-pigeonhole principle for a specific gadget construction) inside a bounded arithmetic theory `VNC^1` or `VPV`, where such a proof is known to be impossible under the assumption that `RSA` (or another concrete one-way function) is secure against quasi-polynomial adversaries. The target is not an arbitrary `P/poly` lower bound but specifically a **Jeřábek-style witnessing collapse**: a SAT-solving circuit family witnesses, in a uniform way, an `∀Σ^b_1` formula in `S^1_2(α)` whose witnessing is provably hard given hardness of factoring. The route is non-natural (the property "SAT-solving" is not testable on truth tables in `poly(2^n)` since SAT itself requires the input length to scale), non-relativizing (uses arithmetic encoding of cryptographic objects), and non-algebrizing (the cryptographic hardness assumption breaks low-degree extension). The novelty is in pinning the bounded-arithmetic-witnessing target to a **specific gadget** — a Goldreich-style local PRG composed with a Tseitin formula over an expander — for which the witnessing collapse can be made concrete enough to drive a Lean-formalisable contradiction at the level of a `Route` definition.

