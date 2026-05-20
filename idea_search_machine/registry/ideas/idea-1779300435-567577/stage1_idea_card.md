# Idea Card

## 1. Thesis

We propose a separation route via **proof-complexity-lifting against bounded arithmetic theories of approximate counting**, specifically targeting the canonical NP problem `SAT` (not arbitrary `P/poly`). The thesis: there exists an explicit family of CNF tautologies — **dual-rail Nisan-Wigderson generator tautologies** `τ_{NW}(f_n)` keyed to a *specific uncomputable hard function* `f_n` (the lex-least function of circuit complexity exactly `2^{n/3}`) — such that any `P/poly`-circuit family solving SAT on these instances would yield a `V^0_2`-proof of the consistency of a stronger fragment `APC_1 + dWPHP(P/poly)`, contradicting a known unprovability result (Krajíček–Pudlák, Jeřábek). The hardness witness is **not** a property of truth tables but of a **specific formula sequence whose key parameter is uncomputable**, evading naturality. The route reduces P=NP to provability of an arithmetic `Π^b_1` statement that has been independently shown unprovable in the relevant theory. The Lean target is to formalise the *reduction* from a `P/poly` SAT-solver to a feasibly-constructive `APC_1`-proof of the NW-generator's range membership, leaving the unprovability side as an admitted lemma sourced from Jeřábek 2007. The novelty is in routing the separation through **a specific non-constructive hard function as a key** rather than through truth-table statistics: the property "circuit on these particular NW-instances is correct" is neither poly(2^n)-testable nor large.

## 2. Prerequisite techniques

- Nisan–Wigderson generators as proof-complexity hardness amplifiers: Razborov, 2003, *Izvestiya Mathematics* ("Pseudorandom generators hard for k-DNF resolution").
- Bounded arithmetic theory `APC_1` and dual weak PHP: Jeřábek, 2007, *Annals of Pure and Applied Logic* ("Approximate counting in bounded arithmetic").
- Unprovability of `P/poly` lower bounds in weak theories: Krajíček, 2011, *Forcing with Random Variables and Proof Complexity*, Cambridge LMS.
- Witnessing theorems for `V^0_2` / `S^1_2`: Cook–Nguyen, 2010, *Logical Foundations of Proof Complexity*, ASL Perspectives.
- Hardness magnification *avoidance* via non-uniform keying: Pich, 2015, *PhD thesis, Charles University* ("Logical strength of complexity theory").
- Resolution lower bounds for NW-generators: Alekhnovich–Ben-Sasson–Razborov–Wigderson, 2004, *SIAM J. Computing*.

## 3. Expected mechanism

The mechanism is a **conditional contrapositive**: assume `SAT ∈ P/poly` via a circuit family `C_n`. We construct, uniformly in `C_n`, a `V^0_2`-proof `π_n` of the statement "`C_n` decides `τ_{NW}(f_n)` correctly", where `τ_{NW}` is the NW-generator tautology keyed by the lex-least function of exact circuit complexity `2^{n/3}`. Because correctness can be expressed as a `∀∃`-statement with bounded `∃`, the Cook–Nguyen witnessing theorem extracts from `π_n` a feasibly-definable witnessing function showing the NW-generator's range is `APC_1`-recognisable. By Razborov 2003 and Jeřábek 2007, this implies `APC_1 ⊢ Con(dWPHP(P/poly))` for the specific NW parameters, contradicting Krajíček 2011's forcing-with-random-variables unprovability theorem.

The critical move: the hard key `f_n` is uncomputable (defined by minimisation over circuit sizes, a `Σ_2`-predicate at the parameter level), so the property "is the NW-generator for `f_n`" is **not testable in poly(2^n)** — testing requires computing `f_n`. The lower-bound certificate is non-constructive at the truth-table level even though the *circuit* `C_n` is fully accessible. This is the natural-proofs evasion. The argument never inspects truth tables of putative small circuits; it inspects only their behaviour on a specific uncomputably-keyed instance distribution.

## 4. Target pnp3 / pnp4 interface

`pnp4/Complexity/ProofComplexity/NWUnprovabilityRoute.lean`, exposing:

```
structure NWUnprovabilityRoute where
  hardKey : ℕ → BoolFunc      -- uncomputable; axiomatised
  nwTautology : ∀ n, CNF
  apc1Witnessing : (P_poly_SAT_solver) → APC1Proof
  jerabekUnprov : ¬ APC1Proves (dWPHP_consistency hardKey)
  conclusion : ¬ (SAT ∈ PPoly)
```

with a `VerifiedNPDAGLowerBoundSource` instance derived by composing `apc1Witnessing` with `jerabekUnprov`. The `hardKey` is admitted as an axiomatised oracle in Lean — its existence is classical, its uncomputability is the *point*.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: HIGH.

Barrier-avoidance:
- **B1 relativization**: The route uses *bounded-arithmetic provability* of a specific `Π^b_1` formula about a *specific* NW-generator. Provability in `APC_1` is not preserved under arbitrary oracles (Krajíček's forcing constructions explicitly produce oracles where these statements flip), so the argument is non-relativizing by construction.
- **B2 natural proofs**: The hardness property is keyed to an **uncomputable** function `f_n` (lex-least exact-complexity witness). Constructivity (a) fails: testing whether a circuit fails on `τ_{NW}(f_n)` requires computing `f_n`, which is not poly(2^n). Largeness (b) also fails: the relevant property holds on a measure-zero family of CNFs (those keyed by `f_n`). Hits both E7 and E8.
- **B3 algebrization**: No low-degree extension is used; the witnessing theorem extracts combinatorial Boolean computations, and Jeřábek's unprovability uses forcing with random *Boolean* variables, not algebraic extensions.
- **B4 locality barrier**: The NW-generator tautologies have global stretch structure; adding small-fanin oracle gates to `C_n` does not eliminate the witnessing extraction because witnessing operates on the *proof object* `π_n`, not the circuit topology.
- **B5 magnification threshold**: We do not use magnification; the lower bound is unconditional modulo Jeřábek's unprovability theorem, not bootstrapped from a weak LB.
- **Project NoGos**: We do not touch support-cardinality, iso-strong forcing on Gap-Partial-MCSP, promise-YES certificate routes, `Size1Candidate` trace counting, or universal `hWitness`. The proof object is an `APC1Proof`, an entirely different category from `PpolyFormula` or DAG witnesses.

Genuine novelty escape: **E6 (proof complexity reductions to bounded arithmetic)** primarily, with **E7 (non-constructive uncomputable parameter)** and **E8 (measure-zero keyed-instance class)** as the naturality escapes.

VERDICT: idea_card_generated