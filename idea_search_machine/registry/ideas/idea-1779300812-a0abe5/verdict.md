# Final verdict


Idea id: `idea-1779300812-a0abe5`
Created: 2026-05-20T18:13:32+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:13:32+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:14:17+00:00 |

## Thesis

We propose to separate `P` from `NP` (in the form of a super-polynomial circuit lower bound for an `NP`-complete problem) via a **proof-complexity-to-circuit-lower-bound transfer using non-automatizability of Extended Frege at a specific bounded-arithmetic theory**. Concretely: target the language `MCSP*` (a padded, self-reducible variant of MCSP whose YES-instances encode succinct circuit-equivalence certificates) and show that any `P/poly` family deciding `MCSP*` would induce, via Cook-style propositional translations, a quasi-polynomial-size Extended Frege refutation of a specific family of *hard tautologies* — namely, the Nisan-Wigderson-based "anti-checker" tautologies of Razborov-Rudich-Krajicek style, but instantiated on an explicit one-way function candidate (e.g., Goldreich's local PRG with predicate `P5`). The lower bound on EF-refutation size is obtained not by feasible interpolation (which is open for EF) but by a **witnessing-failure argument inside `VNP_2`**: if EF had short refutations, then `VNP_2` would prove a Σ^b_1 sentence asserting inversion of `P5`-local PRGs, contradicting the conditional theorem of Krajicek-Pich on the consistency of `VNP_2 + ¬OWF_local`. The property witnessing hardness is **non-constructive** (it requires deciding consistency of a fragment of bounded arithmetic relative to a cryptographic assumption) and **non-large** (it picks out the specific `MCSP*`-decider class). This evades natural proofs by violating both (a) and (b) of Razborov-Rudich.

