# Final verdict


Idea id: `idea-1779296542-2de8b1`
Created: 2026-05-20T17:02:22+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T17:02:22+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T17:03:40+00:00 |

## Thesis

We propose to separate NP from P/poly by leveraging **bounded-arithmetic unprovability of circuit upper bounds** for a specific structured NP problem: the **τ-formula tautology problem associated with Nisan-Wigderson generators instantiated on a hard combinatorial design from explicit Ramanujan-graph expanders**. Concretely, fix the NP language `L_NW` = {(G,y) : y ∉ range(NW_G)} where G is an explicit (n,m,d)-design from LPS Ramanujan graphs. The thesis is: any P/poly circuit family deciding `L_NW` would yield, via Krajíček's feasible interpolation framework, a polynomial-size proof in `PV_1` (or `S^1_2`) of a specific propositional tautology family `τ_n` encoding "NW_G is not surjective". But Razborov's witnessing theorem combined with Pich's recent strengthening shows such tautologies require super-polynomial proofs in any proof system where feasible interpolation holds, conditional on a **specific non-relativizing, non-naturalizable hardness hypothesis about the LPS expander's spectral gap interacting with NW combinatorics**. The novelty: we do not assume circuit lower bounds — we derive them from proof-complexity lower bounds that themselves rest on the algebraic geometry of LPS graphs (number-theoretic, not generic). The argument routes through a property that is **measure-zero** on Boolean functions (the property of "being a τ-formula derived from an LPS-NW instance") and **non-constructive to test** (testing requires checking number-theoretic primality witnesses for Cayley generators).

