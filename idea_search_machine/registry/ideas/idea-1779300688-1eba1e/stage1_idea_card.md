# Idea Card

## 1. Thesis

We propose attacking P vs NP via a **proof-complexity-to-circuit-lower-bound transfer** route, specifically: showing that any `P/poly` circuit family solving `SAT` would yield a feasibly-constructive proof of a combinatorial statement (a variant of the Paris-Wilkie / dual-weak-pigeonhole principle for a specific gadget construction) inside a bounded arithmetic theory `VNC^1` or `VPV`, where such a proof is known to be impossible under the assumption that `RSA` (or another concrete one-way function) is secure against quasi-polynomial adversaries. The target is not an arbitrary `P/poly` lower bound but specifically a **Jeřábek-style witnessing collapse**: a SAT-solving circuit family witnesses, in a uniform way, an `∀Σ^b_1` formula in `S^1_2(α)` whose witnessing is provably hard given hardness of factoring. The route is non-natural (the property "SAT-solving" is not testable on truth tables in `poly(2^n)` since SAT itself requires the input length to scale), non-relativizing (uses arithmetic encoding of cryptographic objects), and non-algebrizing (the cryptographic hardness assumption breaks low-degree extension). The novelty is in pinning the bounded-arithmetic-witnessing target to a **specific gadget** — a Goldreich-style local PRG composed with a Tseitin formula over an expander — for which the witnessing collapse can be made concrete enough to drive a Lean-formalisable contradiction at the level of a `Route` definition.

## 2. Prerequisite techniques

- KPT witnessing theorem and `S^1_2` provability: Krajíček-Pudlák-Takeuti, 1991, *Annals of Pure and Applied Logic*.
- Bounded arithmetic and feasibly-constructive proofs: Krajíček, *Bounded Arithmetic, Propositional Logic and Complexity Theory*, 1995, Cambridge University Press.
- Approximate counting in `VPV` / `VNC^1`: Jeřábek, 2007, *Annals of Pure and Applied Logic* ("Approximate counting in bounded arithmetic").
- Hardness of feasible interpolation under factoring: Krajíček-Pudlák, 1998, *JSL* ("Some consequences of cryptographical conjectures for `S^1_2` and `EF`").
- Pich's framework relating circuit LB provability to LB themselves: Pich, 2015, *Annals of Pure and Applied Logic* ("Circuit lower bounds in bounded arithmetic via Nisan-Wigderson generators").
- Müller-Pich on consistency of strong circuit LBs: Müller-Pich, 2020, *Annals of Pure and Applied Logic*.
- Goldreich's local PRG candidate: Goldreich, ECCC 2000.
- Tseitin tautologies over expanders, hardness in Resolution: Ben-Sasson-Wigderson, 2001, *JACM*.

## 3. Expected mechanism

Assume a `P/poly` circuit `C_n` solves SAT. Encode `C_n` as a propositional translation of an `∀Σ^b_1` sentence `Φ` in `S^1_2(α)` (with `α` denoting the circuit family). By KPT witnessing, if `S^1_2(α) ⊢ Φ`, then a feasibly-constructive Student-Teacher protocol witnesses `Φ` in polynomially many rounds. We instantiate `Φ` on a Goldreich-PRG-composed-with-expander-Tseitin gadget `G_n`: the SAT instance encodes "find a preimage under the local PRG of a string that violates a Tseitin parity constraint." Hardness of factoring (lifted to Goldreich's PRG via standard reductions, or alternatively assumed directly for the PRG) implies the witnessing protocol must, in some round, reveal a preimage — contradicting cryptographic hardness against quasi-polynomial adversaries. The contradiction is **specific to the gadget**, not a generic counting argument. Crucially, the property "circuit family solves SAT on this gadget" is **not** a natural property: it is not testable in `poly(2^n)` on truth tables (the gadget structure depends on `n`, and verifying SAT-solving requires solving SAT), and it holds on a measure-zero set of function families. The non-relativizing ingredient is the arithmetic interpretation of the PRG-security reduction; the non-algebrizing ingredient is the use of factoring hardness, which has no known algebraic-oracle analogue.

## 4. Target pnp3 / pnp4 interface

Define a new route:

```
BoundedArithmeticWitnessingCollapseRoute :
  (SAT_in_Ppoly) →
  (∃ Φ : SigmaB1Formula,
     S12_provable Φ ∧
     ¬ FeasibleWitnessing Φ (under_OWF_hardness))
  → False
```

instantiated at the `GoldreichTseitinGadget n` and producing a `VerifiedNPDAGLowerBoundSource` via the witnessing-vs-cryptography contradiction. The Lean interface object would be `BoundedArithmeticGadgetWitness` parallel to `ResearchGapWitness`, carrying the gadget specification, the KPT-protocol formalisation, and the cryptographic-hardness hypothesis as a parameter.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: HIGH.

Barrier-avoidance:
- **B1 relativization**: The argument crucially uses arithmetic encoding of a concrete one-way function (Goldreich PRG / factoring), which does not relativize — relativized worlds can make OWFs trivially break or trivially hold without affecting `P^O = NP^O`.
- **B2 natural proofs**: The property "C_n correctly decides SAT on `GoldreichTseitinGadget`-encoded instances" is (a) not constructively testable in `poly(2^n)` because verification requires solving SAT instances of size scaling with `n`, and (b) measure-zero — only a vanishing fraction of function families decide SAT. Both naturality conditions fail.
- **B3 algebrization**: Factoring / Goldreich-PRG hardness has no known algebraic-oracle analogue and is widely conjectured non-algebrizing; the witnessing reduction uses cryptographic security, not low-degree extension.
- **B4 locality barrier**: Hardness-magnification gadgets are not invoked; the lower bound target is full SAT on a specific gadget, not a magnification-threshold problem. Oracle-gate extensions do not preserve cryptographic security of the embedded PRG.
- **B5 magnification threshold**: We do not pass through magnification; the contradiction is direct via bounded arithmetic witnessing.
- **Project NoGos**: The route is orthogonal to support-cardinality, iso-strong forcing on Gap-Partial-MCSP, promise-YES certificates, trace-counting, and universal `hWitness`. It does not reduce to any of these on specialisation because the contradiction is driven by KPT witnessing against a cryptographic primitive, not by combinatorial / structural properties of formulas or DAGs at canonical parameters.

Genuine novelty escape: **E6** (proof-complexity reduction connecting bounded-arithmetic provability to circuit lower bounds, à la Pich / Müller-Pich), combined with **E2** (cryptographic one-way function as the non-algebrizing seed) and **E7** (non-constructive property: SAT-deciding is not poly(2^n)-testable).

VERDICT: idea_card_generated