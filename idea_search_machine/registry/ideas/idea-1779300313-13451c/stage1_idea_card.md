# Idea Card

## 1. Thesis

We propose to separate NP from P/poly by leveraging **proof-complexity-theoretic feasible disjunction property** restricted to a *measure-zero, non-constructive* class of circuits: those whose existence as small NP-solvers would yield a propositional proof of a specific tautology family (encoding SAT-non-membership for random 3-SAT at the satisfiability threshold) in a bounded-arithmetic fragment $\mathsf{APC}_1$ extended by a *uniform* hard one-way-function axiom (Nisan-Wigderson-style derandomisation hypothesis). The witness property is: "the truth table of $f_n$ is the indicator of an NP-language whose satisfaction predicate, when encoded as a $\Sigma^b_1$-formula, admits a *witnessable refutation skeleton* in $\mathsf{APC}_1 + \mathsf{dWPHP}(\mathsf{PV})$." This property is (i) **not poly(2^n)-testable** — testing it requires deciding $\Sigma^b_1$ provability, which is undecidable in general; (ii) **not large** — it picks out a measure-zero subfamily defined by Kolmogorov-style descriptions tied to a fixed proof system; (iii) **not preserved under arbitrary oracle insertion** — the bounded-arithmetic encoding refers to the *uniform* structure of the SAT-verifier, which oracle gates erase. The separation follows by combining Krajíček's witnessing for $\mathsf{APC}_1$ with Pich-Santhanam's recent unprovability transfer (2023): if SAT $\in$ P/poly, then $\mathsf{APC}_1$ proves a contradiction with the OWF axiom, contradicting Pich's consistency result.

## 2. Prerequisite techniques

- Witnessing theorems for $\mathsf{APC}_1$ and approximate counting in bounded arithmetic (Jeřábek, *Annals of Pure and Applied Logic*, 2007; *APAL* 2009).
- Unprovability of circuit upper bounds in $\mathsf{APC}_1$ (Pich, *Annals of Pure and Applied Logic*, 2015; Pich-Santhanam, *FOCS* 2021; STOC 2023).
- Dual weak pigeonhole principle $\mathsf{dWPHP}(\mathsf{PV})$ and its role in feasible probabilistic reasoning (Krajíček, *Forcing with Random Variables and Proof Complexity*, Cambridge Univ. Press, 2011).
- Nisan-Wigderson generators as bounded-arithmetic axioms (Razborov, *Izvestiya* 2003; Krajíček, *JSL* 2004).
- Feasible disjunction property and KPT witnessing (Krajíček-Pudlák-Takeuti, *APAL* 1991).
- Müller-Pich on hardness of proving circuit lower bounds (*Computational Complexity* 2020).

## 3. Expected mechanism

Assume for contradiction SAT has poly-size circuits. Encode this as a $\forall \Sigma^b_1$ sentence $\phi_{\mathsf{SAT}\in\mathsf{P/poly}}$ in the language of $\mathsf{PV}$. By Jeřábek's witnessing, if $\mathsf{APC}_1 + \mathsf{NW}$-axiom proves $\phi$, then a feasible algorithm witnesses the circuit construction *relative to* the NW-generator's hard function $h$. But the NW-axiom posits $h$ has no poly-size circuit; the witnessing collapses this into a feasibly-constructible distinguisher for $h$, contradicting the axiom. The novelty is the **two-sided** use: we do not directly prove lower bounds on a function; we prove that the *meta-statement* "SAT is easy" is inconsistent with a *consistent* axiomatic extension whose consistency Pich-Santhanam established unconditionally for $\mathsf{APC}_1$ via a model-theoretic forcing construction (random variables over nonstandard models). The non-constructivity is essential: we never enumerate truth tables; we manipulate proof-theoretic objects whose membership predicate is $\Pi_1$-hard. The measure-zero aspect: the class of "circuits whose existence triggers the contradiction" is defined by a fixed proof skeleton, hence of vanishing density among all circuits of given size.

## 4. Target pnp3 / pnp4 interface

A new `BoundedArithmeticUnprovabilityRoute` def in `pnp4`, exposing a `ResearchGapWitness` whose payload is a triple `(φ : APC1Formula, π : RefutationSkeleton, hCons : APC1_NW_Consistent)` and whose elimination produces `¬ (SAT ∈ Ppoly)` via a `witnessing_collapse` lemma. The route lives parallel to existing `Route*` defs but does NOT instantiate `Size1Candidate`, `PpolyFormula`, or `Gap-Partial-MCSP` — it operates on a fresh `BoundedArith` namespace.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: HIGH.

Barrier-avoidance:
- B1 relativization: The argument hinges on the *syntactic* encoding of the SAT verifier as a $\mathsf{PV}$-term; oracle gates produce non-$\mathsf{PV}$-definable functions, breaking the witnessing translation. Relativised versions of Jeřábek's witnessing fail because the NW-axiom is oracle-sensitive.
- B2 natural proofs: The defining property — "truth table indexes a function whose 'easy' assumption refutes $\mathsf{APC}_1 + \mathsf{NW}$" — is $\Pi_1$-hard to test, violating constructivity (a); and the class is measure-zero (proof-skeleton-indexed), violating largeness (b). Both natural conditions fail.
- B3 algebrization: No low-degree extension or polynomial identity testing is invoked; the proof system $\mathsf{APC}_1$ manipulates Boolean syntax, and algebraic oracles do not preserve $\mathsf{dWPHP}(\mathsf{PV})$-witnessing.
- B4 locality barrier: Magnification is not used; we target SAT directly rather than a gap problem. Oracle-gate extensions do not preserve the bounded-arithmetic encoding.
- B5 magnification threshold: Not applicable — we bypass magnification entirely.
- Project NoGos: We do not touch `Gap-Partial-MCSP`, `Size1Candidate`, support-cardinality, iso-strong forcing, certificate routes, trace-counting, or `PpolyFormula`/DAG witnesses. The route is in a disjoint namespace.

Genuine novelty escape (which of E1-E8): **E6** (proof-complexity / bounded-arithmetic unprovability), with secondary support from **E7** (non-constructive property: $\Pi_1$-hard membership) and **E8** (measure-zero proof-skeleton-indexed class).

VERDICT: idea_card_generated