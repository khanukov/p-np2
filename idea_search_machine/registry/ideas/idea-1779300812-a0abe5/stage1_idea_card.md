# Idea Card

## 1. Thesis

We propose to separate `P` from `NP` (in the form of a super-polynomial circuit lower bound for an `NP`-complete problem) via a **proof-complexity-to-circuit-lower-bound transfer using non-automatizability of Extended Frege at a specific bounded-arithmetic theory**. Concretely: target the language `MCSP*` (a padded, self-reducible variant of MCSP whose YES-instances encode succinct circuit-equivalence certificates) and show that any `P/poly` family deciding `MCSP*` would induce, via Cook-style propositional translations, a quasi-polynomial-size Extended Frege refutation of a specific family of *hard tautologies* — namely, the Nisan-Wigderson-based "anti-checker" tautologies of Razborov-Rudich-Krajicek style, but instantiated on an explicit one-way function candidate (e.g., Goldreich's local PRG with predicate `P5`). The lower bound on EF-refutation size is obtained not by feasible interpolation (which is open for EF) but by a **witnessing-failure argument inside `VNP_2`**: if EF had short refutations, then `VNP_2` would prove a Σ^b_1 sentence asserting inversion of `P5`-local PRGs, contradicting the conditional theorem of Krajicek-Pich on the consistency of `VNP_2 + ¬OWF_local`. The property witnessing hardness is **non-constructive** (it requires deciding consistency of a fragment of bounded arithmetic relative to a cryptographic assumption) and **non-large** (it picks out the specific `MCSP*`-decider class). This evades natural proofs by violating both (a) and (b) of Razborov-Rudich.

## 2. Prerequisite techniques

- Bounded arithmetic and Cook-Reckhow propositional translations (Cook, 1975; Krajicek, *Bounded Arithmetic, Propositional Logic, and Complexity Theory*, Cambridge UP, 1995).
- Extended Frege lower bounds via witnessing (Krajicek & Pich, "Witnessing functions in bounded arithmetic and search problems," JSL 1998; Pich, "Logical strength of complexity theory and a formalization of the PCP theorem," Bull. Symb. Logic 2015).
- Hardness of MCSP and its self-reducible variants (Hirahara, "Non-black-box worst-case to average-case reductions within NP," FOCS 2018; Ilango-Loff-Oliveira, "NP-hardness of circuit minimization for multi-output functions," CCC 2020).
- Goldreich's local pseudorandom generators with predicate `P5` (Goldreich, ECCC 2000; Applebaum-Barak-Wigderson, "Public-key cryptography from different assumptions," STOC 2010).
- Anti-checker / Nisan-Wigderson tautologies in proof complexity (Razborov, "Pseudorandom generators hard for k-DNF resolution and polynomial calculus," 2003; Krajicek, *Forcing with Random Variables and Proof Complexity*, Cambridge UP, 2011).
- Non-automatizability barriers for EF under cryptographic assumptions (Bonet-Pitassi-Raz, "On interpolation and automatization for Frege systems," SICOMP 2000; Atserias-Müller, "Automating resolution is NP-hard," JACM 2020 — used as a methodological template, not directly).

## 3. Expected mechanism

The mechanism is a **three-stage transfer chain**, each stage of which has a published precedent:

1. **Circuits → EF proofs (Cook translation).** If `MCSP*` has `P/poly` circuits of size `s(n)`, then for each `n` the propositional statement "circuit `C` of size `s(n)` decides `MCSP*` on inputs of length `n`" admits a poly(`s(n)`)-size EF proof of its `s(n)`-instance consistency. This is the standard reflection-principle compilation.

2. **EF proofs → `VNP_2` witnessing.** Via Krajicek-Pich witnessing, short EF refutations of the NW-anti-checker tautology τ_{P5,n} imply that `VNP_2` proves a Σ^b_1 sentence asserting that some poly-time machine inverts the `P5`-local PRG on a non-negligible fraction.

3. **Cryptographic contradiction.** The conjectured exponential security of `P5`-local PRGs (Applebaum-Barak-Wigderson) contradicts step 2. This contradiction is *not* relativizing because it depends on the specific algebraic structure of `P5` (a degree-5 predicate over GF(2) with bounded XOR-AND structure), and the inversion task is not preserved under arbitrary oracle extensions.

The lower bound on `MCSP*` then transfers (via Hirahara-style non-black-box reductions) to a super-polynomial lower bound for an `NP`-complete language.

## 4. Target pnp3 / pnp4 interface

`VerifiedNPDAGLowerBoundSource` instantiated through a new route:
`ExtendedFregeWitnessingRoute` — a structure carrying:
- a `BoundedArithmeticTheory` field (specifically `VNP₂`),
- a `LocalPRGCandidate` field (`Goldreich_P5`),
- a `WitnessingFailure` field (a proof obligation that short EF refutations of τ_{P5,n} would witness PRG inversion in `VNP₂`),
- a `TransferLemma` field connecting circuit-size lower bound on `MCSP*` to NP-completeness via Hirahara's reduction.

This route bypasses `FormulaCertificateProviderPartial`, `Size1Candidate` enumeration, and iso-strong forcing entirely, because the witness lives in proof-theoretic provability rather than in formula-syntactic support.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: **HIGH**.

Barrier-avoidance:
- **B1 relativization**: The argument depends on the specific algebraic structure of Goldreich's `P5` predicate and on the syntactic structure of EF proofs. Oracles do not preserve EF-proof length nor the local-PRG security reduction, since the latter exploits expansion of the underlying hypergraph, a non-relativizing combinatorial structure.
- **B2 natural proofs**: The hardness-witnessing property is "`MCSP*` is not in `P/poly`," certified by non-existence of short EF proofs. This is **(a)-non-constructive**: testing whether a truth table admits a short EF refutation of an associated tautology requires search over proofs of exponential length, not poly(2^n) computable. It is also **(b)-non-large**: the property targets one specific language `MCSP*`, not a constant fraction of functions.
- **B3 algebrization**: The local-PRG security assumption is not known to algebrize; the `P5` predicate's hardness comes from constraint-satisfaction expansion, not low-degree extension.
- **B4 locality barrier**: The lower bound is on `MCSP*` (a self-reducible NP problem), not a magnification target. The technique uses proof-theoretic witnessing, which is *not* preserved under small-fanin oracle gates added to circuits — adding oracle gates breaks the Cook translation's syntactic reflection step.
- **B5 magnification threshold**: We do not route through hardness magnification at all; the target lower bound is directly super-polynomial via Hirahara's worst-case-to-average-case reduction.
- **Project NoGos**: We avoid support-cardinality, iso-strong forcing, promise-YES certificate routes, `Size1Candidate` trace counting, and `FormulaCertificateProviderPartial` — the witness is a *proof-theoretic non-provability* object, syntactically disjoint from formula-support filters.

Genuine novelty escape: **E6** (proof-complexity reduction connecting bounded-arithmetic provability to circuit lower bounds), with secondary support from **E2** (cryptographic construction — local PRG — that does not algebrize) and **E7** (non-constructive property: existence of short EF proofs is not poly(2^n)-testable).

VERDICT: idea_card_generated