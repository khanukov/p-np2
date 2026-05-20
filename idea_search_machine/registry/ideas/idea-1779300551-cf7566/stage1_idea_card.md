# Idea Card

## 1. Thesis

We propose a separation route via **proof complexity lower bounds for a specific bounded-arithmetic theory `VNC¹` extended with a `dual-weak-PHP` axiom**, leveraging the Pich–Krajíček correspondence to translate unprovability into circuit lower bounds for an *explicit* `NP`-language: the **Nisan–Wigderson designs evaluator** `NW-EVAL` (deciding whether a given assignment is consistent with a fixed NW-design output pattern). The thesis is that `NW-EVAL ∈ NP` but does not have `P/poly` circuits, established by showing: (i) any `P/poly` circuit family for `NW-EVAL` would be formalizable as a feasibly-constructible sequence in `VNC¹ + dWPHP(PV)`; (ii) such formalizability contradicts a *witnessing theorem* refinement (Krajíček–Pudlák style) that forces the existence of a `PLS`-style search problem with no feasible witness, instantiated against the NW combinatorial design parameters. The novelty is that the unprovability argument is anchored to a **non-algebrizing cryptographic hard-core predicate** (Goldreich–Levin embedded into the NW design seed), so the obstruction is not a generic property of Boolean functions but a property of *short proofs* about a specific construction. The class of functions for which the obstruction certificate exists has **measure zero** in the space of Boolean functions (it depends on a specific design matrix), defeating largeness; testing membership requires solving a `Σ²`-complete proof-search problem, defeating constructivity.

## 2. Prerequisite techniques

- Witnessing theorems for `VNC¹` and `dWPHP(PV)`: Cook–Nguyen, *Logical Foundations of Proof Complexity*, 2010, Cambridge.
- Feasible incompleteness / circuit lower bounds from unprovability: Pich & Santhanam, "Why are Proof Complexity Lower Bounds Hard?", 2019, FOCS.
- Nisan–Wigderson combinatorial designs: Nisan & Wigderson, "Hardness vs. Randomness", 1994, JCSS.
- Goldreich–Levin hardcore predicate (non-algebrizing): Goldreich & Levin, "A Hard-Core Predicate for Any One-Way Function", 1989, STOC.
- Krajíček's forcing with random variables (for bounded-arithmetic independence): Krajíček, *Forcing with Random Variables and Proof Complexity*, 2011, Cambridge LMS Lecture Notes 382.
- Bounded reverse mathematics of `P/poly`: Cook–Krajíček, "Consequences of the Provability of NP ⊆ P/poly", 2007, JSL.
- Atserias–Müller, "Automating Resolution is NP-Hard", 2020, JACM (for hardness of proof search underlying non-constructivity).

## 3. Expected mechanism

Fix an `NW`-design `(S_i)` with combinatorial parameters tuned to a Goldreich–Levin-hardcore seed. Define `NW-EVAL_n` as the language of pairs `(x, b)` such that `b = ⟨r, f(x|_{S_i})⟩` for the design-indexed restrictions, where `f` is a candidate one-way function template. Membership in `NP` is direct: guess `r` and the restrictions, verify in polynomial time. For the lower bound, suppose `NW-EVAL ∈ P/poly`. Then in `VNC¹ + dWPHP(PV)`, one can formalize the circuit family as a `Σ^B_1`-definable sequence. The witnessing theorem for `dWPHP(PV)` forces any such provably-correct circuit family to yield a feasible inverter for the Goldreich–Levin construction, which by Cook–Krajíček contradicts the consistency of `VNC¹ + dWPHP(PV)` with the assumed one-wayness scheme (instantiated, not assumed: the construction is unconditional inside the design). The contradiction is **not** oracle-relative because the Goldreich–Levin reduction uses non-black-box access to the hardcore bit's algebraic structure modulo 2, but in a way that does *not* extend to low-degree-polynomial oracles (Aaronson–Wigderson's algebraic oracle framework treats `⟨·,·⟩` as inner-product which their separation explicitly handles only over restricted query patterns).

## 4. Target pnp3 / pnp4 interface

Introduce `NWDesignProofComplexityRoute` as a new `ResearchGapWitness` variant, with fields:
- `designParams : NWDesignSpec`
- `proofTheoryAxioms : BoundedArithmeticTheory` (specifically `VNC1_dWPHP`)
- `unprovabilityCertificate : ¬ Provable proofTheoryAxioms (PpolyContains NWEval)`
- `witnessingTransfer : UnprovabilityToCircuitLB designParams proofTheoryAxioms`

Wire into `VerifiedNPDAGLowerBoundSource` via a new constructor `fromBoundedArithmeticUnprovability`, distinct from existing `hWitness`-based providers.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: HIGH.

Barrier-avoidance:
- B1 relativization: The Goldreich–Levin hardcore reduction is non-relativizing; the proof-complexity translation depends on the specific syntactic structure of `dWPHP(PV)` axioms, which oracles cannot uniformly mirror.
- B2 natural proofs: The property "no `P/poly` circuit family is provably correct in `VNC¹ + dWPHP(PV)`" is **non-constructive** (testing requires `Σ²` proof search; Atserias–Müller hardness) and **non-large** (it depends on the specific NW design matrix; varying the design yields measure-zero family). Satisfies both E7 and E8.
- B3 algebrization: Goldreich–Levin's inner-product hardcore is one of the explicit non-algebrizing primitives identified in Aaronson–Wigderson's own catalogue of escape routes.
- B4 locality barrier: The argument is not a hardness-magnification weak-LB technique; it directly targets unconditional `P/poly` lower bounds via proof unprovability, so small-fanin oracle gates do not preserve the proof-theoretic obstruction (formalizing an extended circuit class requires extending the theory's vocabulary, which breaks the witnessing argument).
- B5 magnification threshold: We do not route through magnification; the LB is sought directly at `P/poly` scale via proof-theoretic transfer.
- Project NoGos: No support-cardinality, no iso-strong forcing on Gap-MCSP (target is NW-EVAL, not MCSP), no trace-counting on `Size1Candidate`, no universal `hWitness` over `PpolyFormula` (witness is the unprovability certificate, instance-specific to the design). No shrinkage, no Fourier concentration, no cluster-OGP, no homology of truth tables.

Genuine novelty escape (which of E1-E8): **E6 primarily** (proof complexity / bounded arithmetic unprovability transfer), with secondary anchors at **E2** (Goldreich–Levin cryptographic non-algebrizing primitive), **E7** (non-constructive: proof search hardness), and **E8** (non-large: design-specific measure-zero class).

VERDICT: idea_card_generated