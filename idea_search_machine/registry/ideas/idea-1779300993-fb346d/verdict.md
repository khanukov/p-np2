# Final verdict


Idea id: `idea-1779300993-fb346d`
Created: 2026-05-20T18:16:33+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:16:33+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:17:13+00:00 |

## Thesis

We propose to separate `NP` from `P/poly` by exhibiting a **proof-complexity-theoretic obstruction** specific to the `Circuit-SAT` tautology family `‖τ_n‖`: namely, that any sequence of `P/poly`-size circuits `C_n` allegedly deciding SAT would yield, via the KPT witnessing theorem applied inside `APC_1` (Jeřábek's approximate counting arithmetic), a feasibly-definable refutation of `dWPHP(PV)` — the dual weak pigeonhole principle for polynomial-time functions — contradicting Jeřábek's theorem that `APC_1 ⊬ ¬dWPHP(PV)` relative to a structural assumption about **hardness condensation** (Buhrman-Kabanets style). Concretely, the target is to formalise the implication: if `SAT ∈ P/poly` then `APC_1` proves a specific Σ^b_1 statement encoding an unconditional condenser construction, which Jeřábek/Pich/Müller-Pich techniques rule out **at a specific natural problem** (not arbitrary `P/poly`). The novelty lies in routing through `APC_1`'s approximate counting (which is *not* a property of truth tables, hence non-natural in the Razborov-Rudich sense) and avoiding any "fraction of random functions" predicate. The Lean target is to construct a `ResearchGapWitness` whose underlying obstruction is the non-provability of a *named* arithmetical sentence, not a circuit-class property.

