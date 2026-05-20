# Final verdict


Idea id: `idea-1779300435-567577`
Created: 2026-05-20T18:07:15+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:07:15+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:08:12+00:00 |

## Thesis

We propose a separation route via **proof-complexity-lifting against bounded arithmetic theories of approximate counting**, specifically targeting the canonical NP problem `SAT` (not arbitrary `P/poly`). The thesis: there exists an explicit family of CNF tautologies — **dual-rail Nisan-Wigderson generator tautologies** `τ_{NW}(f_n)` keyed to a *specific uncomputable hard function* `f_n` (the lex-least function of circuit complexity exactly `2^{n/3}`) — such that any `P/poly`-circuit family solving SAT on these instances would yield a `V^0_2`-proof of the consistency of a stronger fragment `APC_1 + dWPHP(P/poly)`, contradicting a known unprovability result (Krajíček–Pudlák, Jeřábek). The hardness witness is **not** a property of truth tables but of a **specific formula sequence whose key parameter is uncomputable**, evading naturality. The route reduces P=NP to provability of an arithmetic `Π^b_1` statement that has been independently shown unprovable in the relevant theory. The Lean target is to formalise the *reduction* from a `P/poly` SAT-solver to a feasibly-constructive `APC_1`-proof of the NW-generator's range membership, leaving the unprovability side as an admitted lemma sourced from Jeřábek 2007. The novelty is in routing the separation through **a specific non-constructive hard function as a key** rather than through truth-table statistics: the property "circuit on these particular NW-instances is correct" is neither poly(2^n)-testable nor large.

