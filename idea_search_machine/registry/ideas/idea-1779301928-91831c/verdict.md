# Final verdict


Idea id: `idea-1779301928-91831c`
Created: 2026-05-20T18:32:08+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:32:08+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:32:45+00:00 |

## Thesis

We propose separating P from NP by exhibiting an explicit NP language whose characteristic sequences, viewed as orbits of a computable Z^d-action, generate a **subshift of finite type (SFT) whose topological entropy is uncomputable at a specific rate**, while any P-time language's corresponding subshift has **computably approximable entropy with a polynomial modulus**. The cross-domain bridge is **E14 — topological/symbolic dynamics**, specifically the **Hochman–Meyerovitch theorem** (Annals of Math, 2010) which characterises the set of entropies of multidimensional SFTs as exactly the upper semicomputable nonnegative reals (Π₀₁ right-recursively-enumerable numbers).

The separation idea: encode SAT instances as local matching rules of a 2D SFT in such a way that the topological entropy of the resulting subshift equals a specific Π₀₁ real `h_SAT` whose **right-approximation modulus** is provably super-polynomial. For any P-time decidable language, a uniform construction yields an SFT whose entropy is approximable with a polynomial-time-computable modulus (because membership decisions feed into a finite-window approximation). The two moduli classes are disjoint, separating P from NP via entropy-modulus rate.

The load-bearing cross-domain step is Hochman–Meyerovitch's **simulation of Turing machines by SFTs with controlled entropy contribution**: their construction gives quantitative control on how computational hardness translates to entropy approximation rates — a quantitative dimension never exploited by complexity theory.

