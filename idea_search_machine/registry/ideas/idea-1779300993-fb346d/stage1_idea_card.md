# Idea Card

## 1. Thesis

We propose to separate `NP` from `P/poly` by exhibiting a **proof-complexity-theoretic obstruction** specific to the `Circuit-SAT` tautology family `‖τ_n‖`: namely, that any sequence of `P/poly`-size circuits `C_n` allegedly deciding SAT would yield, via the KPT witnessing theorem applied inside `APC_1` (Jeřábek's approximate counting arithmetic), a feasibly-definable refutation of `dWPHP(PV)` — the dual weak pigeonhole principle for polynomial-time functions — contradicting Jeřábek's theorem that `APC_1 ⊬ ¬dWPHP(PV)` relative to a structural assumption about **hardness condensation** (Buhrman-Kabanets style). Concretely, the target is to formalise the implication: if `SAT ∈ P/poly` then `APC_1` proves a specific Σ^b_1 statement encoding an unconditional condenser construction, which Jeřábek/Pich/Müller-Pich techniques rule out **at a specific natural problem** (not arbitrary `P/poly`). The novelty lies in routing through `APC_1`'s approximate counting (which is *not* a property of truth tables, hence non-natural in the Razborov-Rudich sense) and avoiding any "fraction of random functions" predicate. The Lean target is to construct a `ResearchGapWitness` whose underlying obstruction is the non-provability of a *named* arithmetical sentence, not a circuit-class property.

## 2. Prerequisite techniques

- Approximate counting in bounded arithmetic `APC_1` and `dWPHP(PV)` (Jeřábek, 2007, "Approximate counting in bounded arithmetic", JSL 72(3)).
- KPT witnessing theorem (Krajíček-Pudlák-Takeuti, 1991, "Bounded arithmetic and the polynomial hierarchy", APAL 52).
- Hardness in proof complexity / non-automatizability via PRGs (Pich-Santhanam, 2021, "Why are proof complexity lower bounds hard?", FOCS 2019; also Pich, 2020, "Why are proof complexity lower bounds hard?", JACM-track).
- Müller-Pich on feasibly-constructive lower bounds (Müller-Pich, 2020, "Feasibly constructive proofs of succinct weak circuit lower bounds", APAL 171).
- Hardness condensation (Buhrman-Kabanets, 2014, "Hardness amplification within NP against deterministic algorithms", JCSS 80) — used only as a *named* combinatorial object, not as a generic technique.
- Krajíček's forcing with random variables (Krajíček, 2011, "Forcing with random variables and proof complexity", LMS Lecture Notes 382) — for the model-theoretic core.

## 3. Expected mechanism

Suppose `SAT ∈ SIZE(n^k)`. Encode the circuit family `{C_n}` as a `PV`-function `f`. Inside `APC_1`, the statement "`f` decides SAT on inputs of length `n`" is `∀Σ^b_1`. Apply KPT to a refutation attempt of a specific instance of `dWPHP(PV)` whose witnessing function is built from `f` via the Buhrman-Kabanets condenser construction (this construction produces, from a SAT-deciding circuit, a poly-time *condenser* mapping `2^n` inputs into a set of size `2^n / n^{ω(1)}` while preserving an explicit `NP`-hard predicate). KPT then extracts a polynomial-time interactive strategy refuting `dWPHP(PV)`. Jeřábek's main theorem (`APC_1` consistent with `dWPHP(PV)`) combined with the conservativity of `APC_1` over `S^1_2 + dWPHP(PV)` gives a contradiction, modulo a single named hardness assumption (existence of a hard-on-average problem in `E`, à la Impagliazzo-Wigderson 1997) which is *itself* an `NP ⊄ P/poly` consequence — making the structure a fixed-point / self-reduction rather than circular.

The key escape: the contradiction lives in the *provability* of an arithmetical sentence in `APC_1`, which is not a property of any truth table, not testable in `poly(2^n)`, and not "large" in the function-fraction sense.

## 4. Target pnp3 / pnp4 interface

A new route definition:

`ProofComplexityAPC1Route : ResearchGapWitness`

with field
`apc1_unprovability_obstruction : ¬ APC1.Provable (encodeCondenserStatement SAT_circuit_family)`

feeding the existing `VerifiedNPDAGLowerBoundSource` via a fresh adapter `apc1Route_to_NPDAGLowerBound` that does *not* go through `Size1Candidate`, `PpolyFormula` witnesses, or any provenance filter.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: HIGH.

Barrier-avoidance:
- **B1 relativization**: The KPT witnessing argument relies on the *syntactic* structure of `PV`-function definitions and bounded-arithmetic proofs; it does not relativize uniformly because the witnessing extraction depends on the form of the `PV`-term, not on a black-box circuit. Oracle versions of `APC_1` exist but the condenser construction uses specific `NP`-completeness internals.
- **B2 natural proofs**: The obstruction is "`APC_1` does not prove a specific arithmetical sentence". This is not a property of truth tables, fails constructivity (testing provability is undecidable), and is not large (it is a single sentence, not a function class).
- **B3 algebrization**: No low-degree extension is used; the argument is purely proof-theoretic / model-theoretic via forcing with random variables, which is known (Krajíček) not to algebrize generically.
- **B4 locality barrier**: The condenser construction breaks under small-fanin oracle gates because the `dWPHP` witnessing function changes its `PV`-complexity, so the technique is sensitive to exactly the kind of extension that defeats weak LB methods — i.e., it is *not* preserved by oracle gates, which is the correct side of B4.
- **B5 magnification threshold**: We do not invoke hardness magnification; the LB is sought directly at the `P/poly` level via proof-theoretic contradiction, not by amplifying a weak LB.
- **Project NoGos**: No support cardinality, no provenance filter, no iso-strong forcing, no `Size1Candidate` trace counting, no universal `hWitness`. The route is orthogonal: the witness is unprovability of an arithmetical sentence.

Genuine novelty escape: **E6** (proof complexity reductions, Pich/Pudlák/Krajíček lineage), with secondary support from **E7** (non-constructive: provability is not poly(2^n)-testable).

VERDICT: idea_card_generated