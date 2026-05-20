# Final verdict


Idea id: `idea-1779300551-cf7566`
Created: 2026-05-20T18:09:11+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:09:11+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:10:16+00:00 |

## Thesis

We propose a separation route via **proof complexity lower bounds for a specific bounded-arithmetic theory `VNC¹` extended with a `dual-weak-PHP` axiom**, leveraging the Pich–Krajíček correspondence to translate unprovability into circuit lower bounds for an *explicit* `NP`-language: the **Nisan–Wigderson designs evaluator** `NW-EVAL` (deciding whether a given assignment is consistent with a fixed NW-design output pattern). The thesis is that `NW-EVAL ∈ NP` but does not have `P/poly` circuits, established by showing: (i) any `P/poly` circuit family for `NW-EVAL` would be formalizable as a feasibly-constructible sequence in `VNC¹ + dWPHP(PV)`; (ii) such formalizability contradicts a *witnessing theorem* refinement (Krajíček–Pudlák style) that forces the existence of a `PLS`-style search problem with no feasible witness, instantiated against the NW combinatorial design parameters. The novelty is that the unprovability argument is anchored to a **non-algebrizing cryptographic hard-core predicate** (Goldreich–Levin embedded into the NW design seed), so the obstruction is not a generic property of Boolean functions but a property of *short proofs* about a specific construction. The class of functions for which the obstruction certificate exists has **measure zero** in the space of Boolean functions (it depends on a specific design matrix), defeating largeness; testing membership requires solving a `Σ²`-complete proof-search problem, defeating constructivity.

