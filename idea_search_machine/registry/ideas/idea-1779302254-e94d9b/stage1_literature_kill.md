## Q1

Not killed by Baker-Gill-Solovay 1975 (https://epubs.siam.org/doi/10.1137/0204037), because the proposed mechanism encodes circuit families into a specific combinatorial/dynamical object (ℤ²-SFTs) whose entropy is sensitive to local tile constraints. Relativization barriers apply to proofs that treat the oracle as a black box; tile-encoding of gate-locality is not obviously oracle-invariant — an oracle gate could be encoded as a single tile-symbol breaking the locality decomposition. So the route is *plausibly non-relativizing*. **Not a kill on this axis.**

## Q2

**Killed (conditionally) by Razborov–Rudich, "Natural Proofs," JCSS 55(1):24–35, 1997** (https://www.sciencedirect.com/science/article/pii/S0022000097914940), because the proposed dichotomy is a *combinatorial property of the circuit family's truth-table* (the witness-counting entropy `h_witness_given_input` is precisely a #P-style density, hence a property of the function computed). The "entropy approximation rate" is:

- **Constructive**: Hochman (2009) explicitly frames entropy approximation as a *computable* (Medvedev-degree) procedure on the SFT's language — so the property is constructive in P/poly-relevant sense.
- **Large**: it is satisfied by "most" hard functions (any function with sufficient #SAT density entropy lies outside left-poly-r.e. by counting).

This is exactly the Razborov–Rudich setup. The paper explicitly notes that any lower bound proof factoring through a #P-like density measure of the truth table falls under natural proofs and contradicts pseudorandom function generators (assuming hardness of factoring/DDH). **Hard kill.**

## Q3

Conditional kill: **Aaronson–Wigderson, "Algebrization," ACM TOCT 1(1):2, 2009** (https://dl.acm.org/doi/10.1145/1490270.1490272), applies under the assumption that the tile-system encoding admits a low-degree extension (which Cook–Levin-style encodings standardly do — clause satisfaction is a low-degree polynomial). The entropy decomposition `h_input + h_witness|input` is preserved under arithmetization since it is a counting quantity. So the technique algebrizes, hence cannot separate P from NP per Aaronson–Wigderson Thm 1.1. **Conditional hard kill.**

## Q4

Killed by **Chen, Jin, Williams, et al., "Hardness magnification and locality" / "Beyond Natural Proofs: Hardness Magnification and Locality," JACM 2022** (https://dl.acm.org/doi/10.1145/3460120) and **Oliveira–Pich–Santhanam, CCC 2019** (https://drops.dagstuhl.de/opus/volltexte/2019/10849/), because the proposed mechanism is *exactly* a locality-bounded reduction: SFT constraints are by definition uniformly local (finite window), and the entropy lower bound is extracted from local consistency. Chen et al. show that any lower bound proof going through a "local" reduction of this type cannot cross the magnification threshold from weak models to general circuits. The SFT-locality is far below the magnification threshold's required non-locality. **Hard kill on the locality axis.**

## Q5

Conditional: equivalent to the open problem of separating #P from FP/poly via entropy/density of satisfying assignments — see **Stockmeyer, "On approximation algorithms for #P," SICOMP 1985** and the BPP^NP approximate counting line. The "approximation rate" dichotomy is essentially asking whether #SAT density is poly-time approximable, which by Stockmeyer reduces to Σ₂ⁿ approximation — a long-open question. Not a fresh route; reduces to known open problems.

## Q6

Not killed by direct refutation. No paper explicitly says "SFT-entropy encoding of SAT cannot prove P≠NP." **Not found after search** for: "SFT lower bound P NP", "subshift complexity circuit lower bound", "symbolic dynamics computational complexity barrier".

## Q7

Killed by being below the magnification threshold: **Oliveira–Pich–Santhanam (OPS19)** (https://drops.dagstuhl.de/opus/volltexte/2019/10849/) shows magnification requires lower bounds for problems with very specific sparsity/parameter regimes (e.g., MCSP[2^√n]). `SAT_tile` as defined is a standard NP-complete-flavored language with no such sparsity tuning; its lower bounds, even if proven for restricted models matching SFT-locality, would not magnify. **Hard kill: too weak.**

## Q8

Killed by **Hochman (2009), Inventiones 176** (https://link.springer.com/article/10.1007/s00222-008-0161-7) itself — the paper used as a prerequisite. Hochman's Medvedev-degree analysis shows the entropy approximation rate is tied to the *computability* (Π₁-degree) of the language, *not* to its circuit complexity. There is no theorem in Hochman 2009 §6 establishing a "polynomial-rate left-r.e." subclass corresponding to P/poly — the prerequisite is misread. The Medvedev degrees discussed are recursion-theoretic (Π₁ classes), and collapse all polynomial-time computable languages to degree **0**, providing no separation power. Also see **Aubrun–Sablik, "Simulation of effective subshifts by two-dimensional SFT," Acta Applicandae 2013** (https://link.springer.com/article/10.1007/s10440-013-9802-y), which shows the SFT-simulation framework is *too coarse* to detect polynomial-time distinctions: every Π₁-computable subshift is simulated, with no rate-sensitivity. **Hard kill: the load-bearing lemma does not exist in the cited literature.**

## Final verdict

Multiple hard kills:
- **Q2**: Natural proofs barrier directly applies (the entropy is a large, constructive property of the truth table).
- **Q3**: Algebrizes (counting/density quantities are preserved under low-degree extension).
- **Q4/Q7**: SFT-locality is below magnification threshold; Chen et al. JACM 2022 directly bars local reductions.
- **Q8**: The claimed "polynomial-rate" refinement of Hochman 2009 §6 does not exist — Medvedev degrees are recursion-theoretic and blind to P/poly distinctions; Aubrun–Sablik confirms SFT-simulation is rate-insensitive.

`LIT_RED`

```
VERDICT: LIT_RED
```