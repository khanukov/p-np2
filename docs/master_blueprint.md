> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
# Master Blueprint 2025 → 20XX

This note summarizes a long-term plan towards a formal proof that `P ≠ NP`.
The outline below condenses ongoing discussions and research snippets.  It is
not a proof, but a roadmap for the remaining steps.

## 0. Foundation

* Consolidate all published arguments into a single machine-checked corpus.
* Formalise the lower bound for `MCSPpoly` against $AC^0_d$ and the
  magnification theorem.  From these, derive
  `$NP \nsubseteq P/\mathsf{poly}$` under a weak assumption.

## 1. From restricted to general models

Strengthen the current linear lower bound for `MCSP` in restricted circuits to
an $(1+\varepsilon)$ exponent for all depth $o(\log N)$ circuits.  The goal is
to avoid the Natural Proofs barrier by working with sparse languages.

## 2. Trigger magnification

Apply the magnification theorem to the improved bound from step 1, obtaining the
non-uniform separation `$NP \nsubseteq P/\mathsf{poly}`.

## 3. Break algebrisation / relativisation

Develop a meet-in-the-middle SAT algorithm for compositions `ACC⁰ ∘ MCSP` or, if
that fails, argue that the previous steps already go beyond algebrising
techniques.  Key pieces are a structural compression lemma ("Lemma B") and its
consequences for sub-exponential SAT.

## 4. Uniformisation

Convert the non-uniform separation into `$P ≠ NP` using weak-uniform
translations (e.g. Rossman–Williams) and the Karp–Lipton argument.  Verify that
a potential collapse of `PH` cannot bypass the conclusion.

## 5. Proof-complexity lock-in

As an alternative route, show strong lower bounds for Extended Frege proofs.
Combined with the previous steps, this would also yield `$P ≠ NP`.

## 6. Cryptographic connection

Relate the hardness of `MCSP` to pseudorandom generator constructions and
one-way functions.  Establishing such a generator would reinforce the failure of
Natural Proofs and provide an independent path to `$P ≠ NP`.

## 7. Verification and publication

Machine-check every component, provide demo code for the SAT algorithms, and
maintain a public repository with Lean scripts and accompanying notes.

---

### Current status

Much of the foundational material (Step 0) is available in print but only partly
formalised.  Steps 1–3 are active research; the key missing piece is proving a
rectangular cover of `ACC⁰ ∘ MCSP` tables of size at most `2^{N - N^{\delta}}`.
Recent commits formalise the `coreAgreement` lemma and implement a recursive `buildCover` using `sunflower_step` and `exists_coord_entropy_noninc`.  The cardinal drop lemma `exists_coord_card_drop` is now proven.  The lemma `buildCover_pointwiseMono` has also been established.  The counting lemma `buildCover_card_bound` has now been proven.
The intended proof performs a double induction on the entropy budget `h` and on
the number of uncovered pairs.  Writing

```
μ(F, h, Rset) = 2 * h + |uncovered F Rset|
```

each branch of the recursion strictly decreases this measure:
low-sensitivity families are covered via `low_sensitivity_cover`, otherwise a
coordinate split reduces the entropy budget, and occasionally a sunflower step
covers multiple functions at once.  Combining these cases yields a bound of at
most `mBound n h` rectangles before the measure collapses to zero.  This argument is now fully formalised in Lean.  The file `acc_mcsp_sat.lean` outlines the SAT reduction and awaits integration with the decision-tree cover.
A small `DecisionTree` module with evaluation and size utilities now also
provides path handling via `subcube_of_path` and the lemmas
`path_to_leaf_length_le_depth` and a leaf-count bound `leaf_count_le_pow_depth`.
This sketches the decision-tree argument for covering smooth functions.
Additional modules `collentropy.lean` and `family_entropy_cover.lean` provide
single-function entropy tools and a bundled `FamilyCover` record extracted from
`cover2.lean` with an explicit `mBound` size estimate.
The repository now also includes `Cover/Compute.lean` and
`Algorithms/SatCover.lean`, offering constructive enumeration of the cover and a
simple SAT solver stub.  Their proofs remain incomplete but they integrate with
the existing API.

This document records the plan for future reference and serves as a pointer for
contributors interested in the overarching project.
