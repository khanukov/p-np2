# Idea Card

## 1. Thesis

We propose to separate NP from P/poly by leveraging **bounded-arithmetic unprovability of circuit upper bounds** for a specific structured NP problem: the **τ-formula tautology problem associated with Nisan-Wigderson generators instantiated on a hard combinatorial design from explicit Ramanujan-graph expanders**. Concretely, fix the NP language `L_NW` = {(G,y) : y ∉ range(NW_G)} where G is an explicit (n,m,d)-design from LPS Ramanujan graphs. The thesis is: any P/poly circuit family deciding `L_NW` would yield, via Krajíček's feasible interpolation framework, a polynomial-size proof in `PV_1` (or `S^1_2`) of a specific propositional tautology family `τ_n` encoding "NW_G is not surjective". But Razborov's witnessing theorem combined with Pich's recent strengthening shows such tautologies require super-polynomial proofs in any proof system where feasible interpolation holds, conditional on a **specific non-relativizing, non-naturalizable hardness hypothesis about the LPS expander's spectral gap interacting with NW combinatorics**. The novelty: we do not assume circuit lower bounds — we derive them from proof-complexity lower bounds that themselves rest on the algebraic geometry of LPS graphs (number-theoretic, not generic). The argument routes through a property that is **measure-zero** on Boolean functions (the property of "being a τ-formula derived from an LPS-NW instance") and **non-constructive to test** (testing requires checking number-theoretic primality witnesses for Cayley generators).

## 2. Prerequisite techniques

- Feasible interpolation for proof systems: Krajíček, "Interpolation theorems, lower bounds for proof systems, and independence results for bounded arithmetic", JSL 1997.
- Nisan-Wigderson generators in proof complexity: Razborov, "Pseudorandom generators hard for k-DNF resolution and polynomial calculus resolution", Annals of Math 2015.
- τ-formulas and circuit-LB ↔ proof-LB bridge: Krajíček, "Forcing with Random Variables and Proof Complexity", LMS Lecture Notes 2011.
- Unprovability of circuit upper bounds in bounded arithmetic: Pich, "Circuit lower bounds in bounded arithmetic via Nisan-Wigderson generators", APAL 2015; Pich & Santhanam, "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly", STOC 2021.
- LPS Ramanujan graph constructions: Lubotzky, Phillips, Sarnak, "Ramanujan graphs", Combinatorica 1988.
- NW designs from explicit expanders: Nisan & Wigderson, "Hardness vs randomness", JCSS 1994.
- Witnessing theorems in `S^1_2`: Buss, "Bounded Arithmetic", Bibliopolis 1986; Krajíček-Pudlák-Takeuti relations.

## 3. Expected mechanism

The mechanism has three layers. **Layer 1 (encoding)**: Encode the assertion "NW_G is not a P/poly-breakable PRG" as a sequence of propositional tautologies `τ_n(G)` over variables representing a candidate circuit `C` and a candidate distinguisher. The encoding uses LPS-specific spectral data (eigenvalue bounds from Deligne's theorem on Ramanujan conjecture for GL_2) — this data is **number-theoretic** and does not survive oracle substitution.

**Layer 2 (proof-complexity LB)**: Show that `τ_n(G)` requires super-polynomial proofs in Extended Frege (or weaker, depending on what we can prove) by adapting Razborov's PRG technique, exploiting that LPS designs satisfy a strong "no small subset is mostly hit" combinatorial property derived from the spectral gap. This adaptation is the crux — existing results give such bounds for resolution; we push to `AC^0`-Frege via Pich-Santhanam-style switching with LPS-graph-specific switching lemmas.

**Layer 3 (transfer)**: A P/poly upper bound for `L_NW` would, by feasible interpolation applied to `τ_n(G)`, yield short proofs — contradicting Layer 2. Therefore `L_NW ∉ P/poly`. Since `L_NW ∈ NP` (verifier guesses the preimage absence certificate via design structure), we get `NP ⊄ P/poly`.

The key non-trivial step is establishing feasible interpolation at strong enough proof systems, which is where the work concentrates and where reviewers will (rightly) probe hardest.

## 4. Target pnp3 / pnp4 interface

A new route definition `LPSExpanderNWProofComplexityRoute` parameterised by the LPS prime parameter `p`, producing a `ResearchGapWitness` whose payload is a structure `BoundedArithmeticUnprovabilityCertificate` carrying:
- the `τ_n` family schema,
- a feasible-interpolation lemma instance,
- a proof-size lower bound functional `ProofSizeLB : Nat → Nat` exceeding any polynomial,
- the transfer lemma `proofLB_to_circuitLB`.

This plugs into `VerifiedNPDAGLowerBoundSource` via a new constructor distinct from the refuted iso-strong / support-cardinality / certificate-route families.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: HIGH.

Barrier-avoidance:
- **B1 relativization**: The argument uses Deligne's bound on LPS eigenvalues (number-theoretic, GL_2 representation theory). Oracle substitution destroys the spectral structure; the τ-formulas themselves are tied to specific arithmetic of `PSL_2(F_q)`. Non-relativizing.
- **B2 natural proofs**: The "hard" property is "being a τ-formula from an LPS-NW design" — this is a measure-zero, non-constructive class (E7+E8). Testing membership requires verifying LPS Cayley generator number-theoretic data, not poly(2^n) on truth tables. Fails largeness and constructivity simultaneously.
- **B3 algebrization**: Algebraic oracles extend low-degree polynomial reasoning, but the LPS spectral gap is a deep arithmetic statement (Ramanujan conjecture for GL_2) that is not captured by low-degree extensions. The proof-complexity transfer uses witnessing theorems, not polynomial identity testing.
- **B4 locality barrier**: We are not in the hardness-magnification regime; we target P/poly directly via proof complexity. Oracle gates inside circuits do not affect feasible-interpolation arguments at the propositional level, since the τ-formulas constrain the circuit's I/O behaviour, not its internal gate fanin.
- **B5 magnification threshold**: Not applicable — we do not start from a sub-threshold LB and try to magnify; we target super-polynomial directly via proof complexity.
- **Project NoGos**: No support-cardinality (we never count supports). No iso-strong forcing (we use feasible interpolation, a different framework). No promise-YES certificate route at canonical Gap-MCSP (target language is `L_NW`, not Gap-Partial-MCSP). No trace-counting over `Size1Candidate`. No universal `hWitness` over arbitrary formulae (witness is LPS-specific).

Genuine novelty escape: **E6** (proof-complexity reduction: bounded-arithmetic unprovability → circuit LB), reinforced by **E7** (non-constructive property: LPS membership requires number-theoretic verification) and **E8** (measure-zero class of τ-formulas among all Boolean functions).

VERDICT: idea_card_generated