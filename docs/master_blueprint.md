> **Status (2025-09-24)**: Updated after the September audit.  The combinatorial core is formalised; only the complexity bridge remains axiomatic.
>
# Master Blueprint 2025 → 20XX

This note summarises the long-term plan towards a formal proof that `P ≠ NP`.  The Lean development now proves every combinatorial ingredient that feeds the Family Collision-Entropy Lemma (FCE-Lemma).  The remaining gaps concern classical complexity theory (circuit simulations, magnification, and the Karp–Lipton collapse).

## 0. Foundation

* Maintain the Lean library of Boolean functions, subcubes, entropy, and sunflower technology.  ✅ Completed in `Pnp2/`.
* Record outstanding axioms explicitly (`ComplexityClasses.P_subset_Ppoly`, `NPSeparation.*`).

## 1. From restricted to general models

Strengthen known lower bounds for `MCSP` in restricted circuit classes to depth `o(log N)` with exponent `1+ε`.  This remains an open mathematical problem; the Lean repository provides infrastructure for experimenting with the combinatorial side (decision-tree covers, entropy bounds).

## 2. Trigger magnification

Formalise the magnification theorem that converts the improved `MCSP` bound into `NP ⊄ P/poly`.  This step is currently modelled by the axiom `magnification_AC0_MCSP`.

## 3. Break algebrisation / relativisation

Develop a meet-in-the-middle SAT algorithm for compositions `ACC⁰ ∘ MCSP`, or argue that the previous steps already bypass known barriers.  `Algorithms/SatCover.lean` and `acc_mcsp_sat.lean` provide stubs for future work; they compile and expose constructive interfaces but still rely on exponential enumeration.

## 4. Uniformisation

Convert the non-uniform separation into `P ≠ NP` using the Karp–Lipton argument.  The axiom `karp_lipton` marks the remaining gap; everything else needed on the Lean side (covers, entropy control) is already in place.

## 5. Proof-complexity lock-in (optional)

As an alternative route, pursue strong lower bounds for Extended Frege proofs, leveraging the formalised cover technology.

## 6. Cryptographic connection (optional)

Explore connections between `MCSP` hardness, pseudorandom generators, and one-way functions.  These directions are not yet reflected in the Lean code but can reuse the combinatorial infrastructure.

## 7. Verification and publication

* `Cover/BuildCover.lean` now implements the well-founded recursion with proofs of coverage and a universal cardinal bound.
* `family_entropy_cover.lean` packages the cover with the explicit `mBound` estimate required by downstream arguments.
* `low_sensitivity_cover.lean` completes the decision-tree cover, including the low-sensitivity fallback, without any axioms.
* `Cover/Compute.lean` and `Algorithms/SatCover.lean` provide executable enumerators for experimentation.
* Documentation (`docs/*.md`) has been refreshed to reflect the September 2025 state.

### Current snapshot

* ✅ `buildCover` recursion, coverage, and cardinality bound (`Cover/BuildCover.lean`).
* ✅ Sunflower lemma (`Sunflower/Sunflower.lean`) and agreement lemmas (`Agreement.lean`).
* ✅ Entropy monotonicity and bounds (`entropy.lean`, `bound.lean`, `cover_numeric.lean`).
* ✅ Low-sensitivity decision-tree cover (`low_sensitivity_cover.lean`).
* ⚠️ Pending: replace the axioms in `ComplexityClasses.lean` and `NP_separation.lean` with constructive proofs.

The blueprint remains a living document; contributors should update this file whenever milestones are reached or research priorities shift.
