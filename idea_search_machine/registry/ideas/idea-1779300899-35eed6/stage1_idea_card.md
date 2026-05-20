# Idea Card

## 1. Thesis

We propose to separate NP from P/poly by leveraging a **proof-complexity-to-circuit-lower-bound transfer** specific to a *non-natural, non-relativizing* witness: the **unprovability of NP-hardness lower-bound statements in the bounded arithmetic theory `VNC^1`** (or `V^0_2`) for a *specific* canonical NP-complete problem — namely, a tailored variant of **TAUT for resolution-with-substitution refutation lengths on Tseitin formulas over expander graphs**. The thesis is that, conditional on a *witnessing meta-theorem* (à la Krajíček–Pich), the existence of polynomial-size P/poly circuits deciding this Tseitin variant would yield a `VNC^1`-formalizable algorithm whose correctness proof requires reasoning that provably exceeds `VNC^1`'s capacity, contradicting Pich's "feasible interpolation for unary NP." The escape from natural proofs is structural: the property "this specific Tseitin family on Ramanujan expanders has no polynomial circuit" is **measure-zero** (it singles out one explicit graph sequence) and is **not constructively checkable** on truth tables — verifying membership requires solving an instance of the underlying expansion certificate, which itself is conjecturally outside `AC^0[p]`. The escape from relativization is via the *combinatorial geometry of the specific expander*, which has no oracle analogue. We do **not** count solutions, do not invoke shrinkage, and do not use Fourier / spectral concentration on the truth table.

## 2. Prerequisite techniques

- Feasible interpolation and proof complexity lower bounds: Krajíček, 1997, *Journal of Symbolic Logic*.
- Unprovability of circuit lower bounds in bounded arithmetic: Pich & Santhanam, 2021, *FOCS*.
- Tseitin formulas on expanders, resolution lower bounds: Ben-Sasson & Wigderson, 2001, *JACM*.
- Ramanujan graph constructions: Lubotzky, Phillips, Sarnak, 1988, *Combinatorica*.
- Witnessing theorems for `VNC^1` / `V^0_2`: Cook & Nguyen, 2010, *Logical Foundations of Proof Complexity*, Cambridge.
- Bounded reverse mathematics of P/poly: Cook & Krajíček, 2007, *JSL*.
- KPT witnessing theorem: Krajíček, Pudlák, Takeuti, 1991, *Annals of Pure and Applied Logic*.

## 3. Expected mechanism

Fix an explicit Ramanujan expander sequence `G_n` (LPS). The Tseitin contradiction `T(G_n, ω)` for odd-charge `ω` is unsatisfiable; its resolution refutation length is exp(Ω(n)) (BSW01). We define `L_Tseitin ⊆ NP` as the language of *satisfiable* perturbations (one charge flipped). Suppose for contradiction `L_Tseitin ∈ P/poly` via circuits `C_n`. By a *non-uniform* witnessing argument (extending KPT to `VNC^1` augmented with a "circuit oracle" symbol), the existence of `C_n` is formalizable as a `Σ^B_1` sentence whose proof of correctness would, by Pich-Santhanam-style unprovability, require a `Σ^B_2` induction principle — but the expander's algebraic certificate (eigenvalue gap from LPS) is a `Π^B_1` fact unprovable in `VNC^1`. The contradiction yields the separation. The transfer is **not** natural because it is gated on the *specific* LPS expander (measure zero) and requires solving the expansion certificate (not poly(2^n)-testable from truth tables). It does **not** relativize because the LPS construction's correctness uses quaternion-algebra number theory absent from any oracle.

## 4. Target pnp3 / pnp4 interface

A new route definition: `BoundedArithmeticUnprovabilityRoute` producing a `VerifiedNPDAGLowerBoundSource` whose witness field is a triple `(LPSExpanderCertificate n, TseitinPerturbedInstance n, VNC1UnprovabilityToken)`, feeding the existing `ResearchGapWitness` aggregator via a new constructor `ResearchGapWitness.ofProofComplexityTransfer`.

## 5. Self-assessment of novelty and barrier-avoidance

Overall novelty: HIGH.

Barrier-avoidance:
- **B1 relativization**: The LPS expander's spectral certificate uses Deligne's bound on Ramanujan–Petersson; this number-theoretic fact has no oracle analogue, so the proof does not relativize.
- **B2 natural proofs**: The hard property is "membership in a specific LPS-Tseitin family," which is (a) **not constructive** — verifying it requires checking an algebraic eigenvalue bound, not a poly(2^n) truth-table test — and (b) **not large** — it is a measure-zero singleton family. Both naturality conditions fail. (Escapes E7 and E8.)
- **B3 algebrization**: We use high-degree number-theoretic facts (quaternion orders, Deligne); no low-degree polynomial extension over a generic finite field encodes the LPS spectral gap.
- **B4 locality barrier**: The argument does not proceed by counting hard inputs or by a weak-LB technique amenable to oracle-gate extension; it proceeds by a metamathematical unprovability transfer where adding small-fanin oracle gates would require re-axiomatising `VNC^1`, which changes the theory rather than circumventing the bound.
- **B5 magnification threshold**: We do not route through hardness magnification at all; the lower bound is obtained directly from unprovability, not from amplifying a sub-threshold bound.
- **Project NoGos**: No support-cardinality, no iso-strong forcing, no Promise-YES certificate route, no trace-counting on `Size1Candidate`, no universal `hWitness` over `PpolyFormula`. The witness is a metamathematical unprovability token paired with an explicit algebraic certificate — orthogonal to all refuted families.

Genuine novelty escape (which of E1-E8): **E6** (proof-complexity / bounded-arithmetic reduction) as primary, with **E7** (non-constructive property: requires uncomputable-in-poly(2^n) expansion certificate) and **E8** (measure-zero class: singleton LPS family) as secondary structural escapes from naturality.

VERDICT: idea_card_generated