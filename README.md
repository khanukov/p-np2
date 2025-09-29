# P≠NP formalization repository
> **Status (2025-09-24)**: All combinatorial and entropy proofs in `Pnp2/` are complete.  The classical inclusion `P ⊆ P/poly` is now proven constructively; the only remaining axioms sit in the magnification bridge (`NP_separation.lean`).

This project develops, in Lean 4, the infrastructure required for the **Family Collision‑Entropy Lemma (FCE‑Lemma)**.  The lemma asserts that Boolean-function families with small collision entropy admit a subexponential cover by monochromatic subcubes.  Establishing this result is a key milestone on the roadmap towards a formal separation `P ≠ NP`.

The final bridge now follows the classical route “`NP ⊄ P/poly` + `P ⊆ P/poly` ⇒ `P ≠ NP`” without appealing to any collapse of the polynomial hierarchy.  Remaining axioms concentrate on magnification for `MCSP` and on the constructive cover itself.

Every file that participates in the cover construction now has full proofs.  Classical complexity-theoretic statements that are not yet formalised appear as explicit axioms and are tracked in `TODO.md`.

## Layout

### Foundations
* `BoolFunc.lean` – points, Boolean functions, subcubes, and basic probability utilities (`prob`, `prob_restrict_false`, `prob_restrict_true`).
* `BoolFunc/Support.lean` – support lemmas such as `eval_eq_of_agree_on_support`.
* `BoolFunc/Sensitivity.lean` – sensitivity, block sensitivity, and helper facts for decision trees.
* `Boolcube.lean` – subcube structures, enumeration helpers (`toFinset`, `size`), and the combinatorial split lemma `exists_coord_card_drop`.
* `DecisionTree.lean` – finite decision trees with depth/leaf bounds and `subcube_of_path` extraction.

### Entropy and combinatorics
* `entropy.lean`, `collentropy.lean`, `CollentropyBasic.lean` – collision entropy for families and single functions, including the monotonicity lemma `H₂_restrict_le`.
* `sunflower.lean`, `Sunflower/…` – a fully formalised sunflower lemma (`sunflower_exists_classic`) and refinements for scattered families (`RSpread`).
* `Agreement.lean` – the core-agreement lemma used by the sunflower step.

### Cover pipeline
* `Cover/Measure.lean`, `Cover/Uncovered.lean`, `Cover/Lifting.lean`, `Cover/SubcubeAdapters.lean`, `Cover/Bounds.lean`, `Cover/CoarseBound.lean`, `Cover/BuildCover.lean` – termination measure, search helpers, lifting lemmas, and the well-founded recursion implementing `buildCover`.
* `cover2.lean` – high-level orchestration (`sunflower_step`, `buildCover_covers`, `buildCover_card_bound`).
* `family_entropy_cover.lean` – bundled `FamilyCover` record exposing `buildCover` together with the explicit `mBound` bound.
* `Cover/Compute.lean`, `Algorithms/SatCover.lean` – constructive (exponential-time) enumerators used for experimentation and a SAT solver stub.
* `low_sensitivity_cover.lean`, `low_sensitivity.lean`, `merge_low_sens.lean`, `cover_size.lean`, `sat_cover.lean` – decision-tree cover for smooth families and tools to combine entropy and sensitivity arguments.
* `cover_numeric.lean`, `bound.lean` – numeric bounds for the experimental cover and the inequality `mBound_le_two_pow_linear`.

### Complexity interface
* `canonical_circuit.lean`, `Algorithms/` – canonical circuits and executable experiments.
* `acc_mcsp_sat.lean` – meet-in-the-middle SAT outline.
* `ComplexityClasses.lean`, `NP_separation.lean` – bridge from the FCE-Lemma to `P ≠ NP` (remaining axioms: `magnification_AC0_MCSP`, `FCE_implies_MCSP`).
* `TM/Encoding.lean`, `Circuit/Family.lean`, `PsubsetPpoly.lean` – groundwork for the classical inclusion `P ⊆ P/poly`.

### Documentation and experiments
* `docs/` – research notes and blueprints updated during the September 2025 audit.
* `experiments/` – Python tooling for enumerating small Boolean circuits (`lemma_b_search.py`, `single_gate_count.py`, `collision_entropy.py`, `capacity_drop.py`, `sunflower_step.py`) with logged results in `results_n*.md`.
* `Task_description.md`, `fce_lemma_proof.md` – background notes on the FCE-Lemma programme.

## Logic conventions

All Prop-level arguments freely use classical reasoning:

* `Classical` is routinely opened and noncomputable sections are used when convenient.
* Standard mathlib axioms such as `funext`, `propext`, and `Classical.choice` are part of the accepted toolkit.
* Noncomputable definitions are permitted because the project is about existence proofs, not extraction of efficient programs.

Whenever a constructive variant is desirable for later tooling, the documentation marks it explicitly.

## Building

The development targets **Lean 4** together with **mathlib4** ≥ 4.22.0-rc2.  Install `elan` (which also provides the `lake` tool) and run

```bash
elan toolchain install $(cat lean-toolchain)
```

to fetch the compiler.  Afterwards build the project with

```bash
lake exe cache get
lake build
```

If the cache download is blocked, rerun `lake build` to compile mathlib from source.

Smoke tests:

```bash
lean --run Pnp2/examples.lean     # runnable examples
lake env lean --run scripts/smoke.lean
lake test                         # unit-style tests for helper executables
./scripts/check.sh                # full build + smoke test
```

## Experiments

Prototype scripts in `experiments/` require Python 3:

```bash
python3 experiments/lemma_b_search.py 4 2      # exhaustive gate enumeration
python3 experiments/capacity_drop.py 6 3       # capacity-drop statistics
python3 experiments/collision_entropy.py 3 1   # collision entropy tables
python3 experiments/sunflower_step.py --t 3 0,1 0,2 1,2
```

Enumerations for `n ≤ 8` are documented in `results_n*.md`.

## Current status and open tasks

The constructive cover (`buildCover`, `familyEntropyCover`, `decisionTree_cover`) is completely formalised.  Outstanding work is concentrated in the magnification bridge:

* Replace the assumptions `magnification_AC0_MCSP` and `FCE_implies_MCSP` in `NP_separation.lean` with formal proofs.
* Strengthen the experimental numeric bounds in `cover_numeric.lean` (the current `2^n` cap is a safe placeholder).

See `TODO.md` for a detailed task list and progress tracker.
