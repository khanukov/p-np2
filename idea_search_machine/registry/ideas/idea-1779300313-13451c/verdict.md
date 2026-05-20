# Final verdict


Idea id: `idea-1779300313-13451c`
Created: 2026-05-20T18:05:13+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:05:13+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:06:08+00:00 |

## Thesis

We propose to separate NP from P/poly by leveraging **proof-complexity-theoretic feasible disjunction property** restricted to a *measure-zero, non-constructive* class of circuits: those whose existence as small NP-solvers would yield a propositional proof of a specific tautology family (encoding SAT-non-membership for random 3-SAT at the satisfiability threshold) in a bounded-arithmetic fragment $\mathsf{APC}_1$ extended by a *uniform* hard one-way-function axiom (Nisan-Wigderson-style derandomisation hypothesis). The witness property is: "the truth table of $f_n$ is the indicator of an NP-language whose satisfaction predicate, when encoded as a $\Sigma^b_1$-formula, admits a *witnessable refutation skeleton* in $\mathsf{APC}_1 + \mathsf{dWPHP}(\mathsf{PV})$." This property is (i) **not poly(2^n)-testable** — testing it requires deciding $\Sigma^b_1$ provability, which is undecidable in general; (ii) **not large** — it picks out a measure-zero subfamily defined by Kolmogorov-style descriptions tied to a fixed proof system; (iii) **not preserved under arbitrary oracle insertion** — the bounded-arithmetic encoding refers to the *uniform* structure of the SAT-verifier, which oracle gates erase. The separation follows by combining Krajíček's witnessing for $\mathsf{APC}_1$ with Pich-Santhanam's recent unprovability transfer (2023): if SAT $\in$ P/poly, then $\mathsf{APC}_1$ proves a contradiction with the OWF axiom, contradicting Pich's consistency result.

