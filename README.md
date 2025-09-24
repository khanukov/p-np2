# P≠NP formalization repository
> **Status (2025-08-06)**: This repository is incomplete; unproven statements are currently marked with `axiom` placeholders while their proofs are developed.


This repository collects experimental Lean files that sketch a formal proof of the **Family Collision‑Entropy Lemma (FCE‑Lemma)**.  The lemma aims to cover families of Boolean functions with a subexponential number of monochromatic subcubes and is a building block for a potential proof that `P ≠ NP`.

The project is **not** yet a complete proof: several key statements are
currently provided as axioms without proof.  Many basic lemmas have now been
formalised, so the repository also serves as a record of ongoing progress
towards a full argument.

The development now happens entirely in the `Pnp2` namespace.  The previous
development tree is kept only as a historical snapshot and is no longer part of
the build.

Several files continue to contain axiomatic placeholders
(`axiom`) while the formal proofs are completed.  These markers are
tracked in `TODO.md` and will be removed as the project progresses.

## Layout

* `BoolFunc.lean` – basic types for Boolean functions, points and subcubes (fully
  proved).  The module now also defines simple probability utilities
  (`prob`, `prob_restrict_false`, `prob_restrict_true`) for measuring how often
  a function outputs `true` under various restrictions.
* `BoolFunc/Support.lean` – helper lemmas about the coordinate support of
  Boolean functions, e.g. `eval_eq_of_agree_on_support`.
* `BoolFunc/Sensitivity.lean` – defines sensitivity and basic lemmas used by the
  low-sensitivity cover.
* `Boolcube.lean` – extended definitions for subcubes.  Alongside the
  basic `Subcube` structure this module now provides enumeration helpers
  (`toFinset` and `size`), a monotonicity lemma for inclusion and the
  cardinal split result `exists_coord_card_drop`.  Lightweight structures
  `LabeledCube` and `Cover` expose the building blocks for recursive
  cover constructors.  The module now integrates a sunflower step via the
  lemma `sunflower_exists_classic` whose combinatorial proof is now
  completely formalised.

* `entropy.lean` – collision entropy framework with the entropy monotonicity lemma `H₂_restrict_le`. The earlier halving axiom has been removed.
* `sunflower.lean` – reexports the classical sunflower lemma
  `sunflower_exists_classic`; the full combinatorial proof is now present
  in the repository.
* `Sunflower/RSpread.lean` – definition of scattered families (`RSpread`).
  The lemma `RSpread.mono` now shows that a larger spread parameter implies
  a smaller one when `0 < R₂ ≤ R₁`.  Additional helper lemmas
  (`RSpread.card_bound`, `RSpread.one_of_nonempty`, `RSpread.card_filter_le`)
  rephrase the definition and handle the trivial case `R = 1`.
* `Agreement.lean` – complete proof of the core‑agreement lemma.
* `cover2.lean` – reimplementation of the cover builder with `buildCover_pointwiseMono`, `sunflower_step`, and supporting combinatorial lemmas. Earlier counting lemmas such as `buildCover_card_bound` have been removed.
* `cover_size.lean` – minimal notion of cover size with an elementary cardinality bound.
* `sat_cover.lean` – evaluates circuits on representative points of a rectangle cover and proves basic correctness properties.
* `Cover/Compute.lean` – lightweight wrapper exposing a constructive
  variant `buildCoverCompute` that enumerates the rectangles as a list.
  The current implementation reuses the naive exhaustive scan of the Boolean
  cube, so it is exponentially slow but fully constructive.  Its specification
  is proven and the file is used by `Algorithms/SatCover` for basic SAT
  experimentation.
* `bound.lean` – arithmetic bounds deriving the subexponential size estimate;
  the main inequality `mBound_lt_subexp` is now fully proved in the
  `Pnp2` namespace.
* `collentropy.lean` – collision entropy of a single Boolean function with
  basic lemmas such as `H₂Fun_le_one`.
* `CollentropyBasic.lean` – trimmed-down entropy file containing only the bounds needed for the SAT solver. All numeric inequalities are now fully proved.
* `family_entropy_cover.lean` – convenience wrapper returning a `FamilyCover`
  record extracted from `cover2.lean`; the record includes an explicit
  `mBound` cardinality estimate.
* `merge_low_sens.lean` – provides `mergeLowSensitivityCover` and `merge_cover` to combine low‑sensitivity and entropy covers, together with accompanying correctness lemmas.
* `DecisionTree.lean` – minimal decision-tree datatype with depth, leaf-count,
  path extraction, a `subcube_of_path` helper and lemmas
  `path_to_leaf_length_le_depth` and `leaf_count_le_pow_depth`
  bounding recorded paths and leaf count.
* `low_sensitivity_cover.lean` – decision-tree covers for low-sensitivity families. The main theorem `decisionTree_cover` combines the combinatorial `buildCover` estimate in the large-sensitivity regime with a singleton enumeration fallback, eliminating the earlier dependency on the unfinished lemma `exists_common_monochromatic_subcube`.
* `canonical_circuit.lean` – Boolean circuits with a basic canonicalisation function.
* `low_sensitivity.lean` – trivial cover for smooth functions (self-contained).
* `Algorithms/SatCover.lean` – constructive SAT search procedure scanning the
  rectangles from `buildCoverCompute`.  It currently falls back to enumerating
  all points but provides the intended interface for meet-in-the-middle
  extensions.
* `acc_mcsp_sat.lean` – outline of the meet-in-the-middle SAT connection.
* `NP_separation.lean` – axiomatic bridge from the FCE-Lemma to `P ≠ NP`, relying on assumptions such as `magnification_AC0_MCSP`, `karp_lipton`, and `FCE_implies_MCSP`.
* `ComplexityClasses.lean` – minimal definitions of `P`, `NP` and `P/poly`; inclusion `P ⊆ P/poly` is currently assumed as an axiom.
* `cover_numeric.lean` – placeholder numeric bounds; `buildCover_card` assumes a provisional `2^n` upper bound on the cover size.

* `table_locality.lean` – defines the locality property and proves a
  basic version of the table locality lemma (roadmap B‑2) with the
  trivial bound `k = n`.
* `examples.lean` – runnable examples illustrating the definitions.
* `experiments/` – small Python tools exploring rectangle covers, including `lemma_b_search.py`, `single_gate_count.py`, `collision_entropy.py`, `capacity_drop.py`, and `sunflower_step.py`.
  The directory also contains enumeration logs such as `results_n2_n3.md`, `results_n4_n5.md`, `results_n6.md`, and `results_n7_n8.md`.
* `docs/` – assorted background notes. `E1_roadmap.md` outlines the ACC⁰∘MCSP approach. Additional materials include `buildCover_card_bound_outline.md` (historical proof outline for a now‑removed counting lemma), `canonical_eq_proof_plan.md`, `collision_entropy_solution.md`, `master_blueprint.md`, `lemma_B_plan.md`, `b3_b5_details.md`, and `np_not_p_poly_sketch.md`. The theorem `canonical_eq_iff_eqv` from `canonical_eq_proof_plan.md` is formalised in `Pnp2/canonical_circuit.lean`.
* `Task_description.md`, `fce_lemma_proof.md` – original research notes explaining the FCE‑Lemma project.

## Logic conventions

All Prop-level arguments in the repository freely use classical reasoning.  In
particular:

* we routinely `open Classical` and work in `noncomputable` sections when this
  simplifies a proof;
* standard mathlib axioms such as `funext`, `propext`, and `Classical.choice`
  are part of the accepted toolkit;
* noncomputable definitions are allowed whenever they shorten proofs—our
  results are proofs of existence rather than executable programs;
* previously formalised lemmas from mathlib (including statements about
  computability, automata, and decision trees) may be reused without providing
  constructive rederivations.

Whenever a constructive variant is desirable for extraction or experimentation,
the documentation marks it explicitly as a future enhancement.

## Building

The Lean files require **Lean 4** together with **mathlib4** (version ≥ 4.22.0-rc2).
A minimal `lakefile.lean` and `lean-toolchain` are included.  Install `elan` (which also provides the `lake` tool, e.g. via `sudo apt-get install elan`) and run

```bash
elan toolchain install $(cat lean-toolchain)
```

to set up the compiler.  Then fetch the cached dependencies and build the
project with:

```bash
lake exe cache get
lake build
```

If the cache download fails due to network restrictions, simply run
`lake build` again to compile Mathlib from source. This may take a
few minutes the first time.

`examples.lean` can be run directly with `lean --run examples.lean` once the
dependencies have been downloaded.  A minimal smoke test is provided in
`scripts/smoke.lean`:

```bash
lake env lean --run scripts/smoke.lean
```
which simply checks that the base definitions compile successfully.

For a full consistency check that builds the entire project and runs the smoke
test in one go, you can use:

```bash
./scripts/check.sh
```

## Experiments

The `experiments/` directory contains Python scripts that enumerate small
Boolean circuits to collect data for Lemma B.  Invoke them with Python 3:

```bash
python3 experiments/lemma_b_search.py     # exhaustive search of small circuits
python3 experiments/single_gate_count.py  # list functions from a single gate
python3 experiments/capacity_drop.py 6 3  # α drop for up to 6 inputs
python3 experiments/capacity_drop.py --prefix 7 3  # prefix drop on 7 inputs
python3 experiments/collision_entropy.py 3 1         # log2 of unique functions
python3 experiments/collision_entropy.py 3 1 --circuits  # weight by circuit count
python3 experiments/collision_entropy.py 3 1 --list-counts  # table counts
python3 experiments/collision_entropy.py 3 1 --list-counts --descending
python3 experiments/collision_entropy.py 3 1 --list-counts --top 5
python3 experiments/sunflower_step.py --t 3 0,1 0,2 1,2  # search for a small sunflower
```

## Status

This repository is a research prototype. Many central lemmas remain incomplete and are marked with `axiom`. In particular:
* `decisionTree_cover` is still unfinished: `exists_common_monochromatic_subcube` in `low_sensitivity_cover.lean` and several path-permutation lemmas in `DecisionTree.lean` remain as `sorry`s.
* `NP_separation.lean` derives `P ≠ NP` from unproven assumptions (`magnification_AC0_MCSP`, `karp_lipton`, `FCE_implies_MCSP`).
* `ComplexityClasses.lean` assumes `P ⊆ P/poly`.

See `TODO.md` for an up-to-date list of outstanding tasks.

## Development plan

The immediate goal is to replace the axioms above with formal proofs and to
obtain verified bounds for the cover construction.  The project deliberately
allows classical choice and other nonconstructive steps for these Prop-level
results.  The current search routine `firstUncovered` therefore keeps its
classical implementation; a constructive rewrite is tracked separately for the
moment when executable artefacts become a priority.
