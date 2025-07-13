# P≠NP formalization repository

This repository collects experimental Lean files that sketch a formal proof of the **Family Collision‑Entropy Lemma (FCE‑Lemma)**.  The lemma aims to cover families of Boolean functions with a subexponential number of monochromatic subcubes and is a building block for a potential proof that `P ≠ NP`.

The project is **not** yet a complete proof: several key statements are
currently provided as axioms without proof.  Many basic lemmas have now been
formalised, so the repository also serves as a record of ongoing progress
towards a full argument.

## Layout

* `BoolFunc.lean` – basic types for Boolean functions, points and subcubes (fully
  proved).  The module now also defines simple probability utilities
  (`prob`, `prob_restrict_false`, `prob_restrict_true`) for measuring how often
  a function outputs `true` under various restrictions.
* `BoolFunc/Support.lean` – helper lemmas about the coordinate support of
  Boolean functions, e.g. `eval_eq_of_agree_on_support`.
* `BoolFunc/Sensitivity.lean` – defines sensitivity and basic lemmas used by the
  low-sensitivity cover.
* `Boolcube.lean` – extended definitions.  The old sunflower branch of
  `buildCover` has been removed, leaving a simplified entropy-based
  construction. A new lemma `monochromatic_point` shows that single-point subcubes are automatically
  monochromatic for any Boolean function. Monotonicity and counting bounds are currently axioms.

* `entropy.lean` – collision entropy framework with the full `EntropyDrop`
  lemma proven alongside basic tools such as `collProb_le_one`.  The
  auxiliary lemma `exists_restrict_half` shows that some input bit
  restricts a family to at most half its size.  Its real-valued
  variant `exists_restrict_half_real` and the probability version
  `exists_restrict_half_real_prob` provide the bridge to analytic
  bounds, and `exists_coord_entropy_drop` turns this into a one‑bit drop
  of collision entropy.
* `sunflower.lean` – full classical sunflower lemma `sunflower_exists` now formalised.
* `Sunflower/RSpread.lean` – definition of scattered families (`RSpread`).
  The lemma `RSpread.mono` now shows that a larger spread parameter implies
  a smaller one when `0 < R₂ ≤ R₁`.  Additional helper lemmas
  (`RSpread.card_bound`, `RSpread.one_of_nonempty`, `RSpread.card_filter_le`)
  rephrase the definition and handle the trivial case `R = 1`.
* `Agreement.lean` – complete proof of the core‑agreement lemma.
* `cover.lean` – experimental cover builder that keeps track of the
  set of uncovered inputs via `firstUncovered`.  The entropy split now
  uses `exists_coord_entropy_drop`, and the sunflower step relies on
  `sunflower_exists`.  Monochromaticity and size bounds are stated as
  axioms pending full proofs.  A helper lemma `AllOnesCovered.union`
  now abstracts the union step in the coverage proof.
* `bound.lean` – arithmetic bounds deriving the subexponential size estimate;
  the main inequality `mBound_lt_subexp` is now fully proven.
* `collentropy.lean` – collision entropy of a single Boolean function with
  basic lemmas such as `H₂Fun_le_one`.
* `family_entropy_cover.lean` – convenience wrapper returning a `FamilyCover`
  record extracted from `cover.lean`.
* `merge_low_sens.lean` – stub combining low‑sensitivity and entropy covers.
* `DecisionTree.lean` – minimal decision-tree datatype with depth, leaf-count,
  path extraction, a `subcube_of_path` helper and lemmas
  `path_to_leaf_length_le_depth` and `leaf_count_le_pow_depth`
  bounding recorded paths and leaf count.
* `low_sensitivity_cover.lean` – lemma skeletons using these trees.
* `canonical_circuit.lean` – Boolean circuits with a basic canonicalisation function.
* `low_sensitivity.lean` – trivial cover for smooth functions (self-contained).
* `acc_mcsp_sat.lean` – outline of the meet-in-the-middle SAT connection.
* `NP_separation.lean` – axiomatic bridge from the FCE-Lemma to `P ≠ NP`.
* `ComplexityClasses.lean` – minimal definitions of `P`, `NP` and `P/poly` for
  stating complexity results.
* `cover_numeric.lean` – placeholder numeric bounds wrapping `buildCover`.
* `table_locality.lean` – defines the locality property and proves a
  basic version of the table locality lemma (roadmap B‑2) with the
  trivial bound `k = n`.
* `examples.lean` – runnable examples illustrating the definitions.
* `experiments/` – small Python tools exploring rectangle covers, including
  `lemma_b_search.py`, `single_gate_count.py`, and `collision_entropy.py`.
  The directory also contains enumeration logs such as
  `results_n2_n3.md`, `results_n4_n5.md`, and `results_n6.md`.
* `docs/` – assorted background notes.  The file `E1_roadmap.md` contains the current roadmap for the ACC⁰∘MCSP subexponential SAT approach.
* `Task_description.md`, `fce_lemma_proof.md` – original research notes explaining the FCE‑Lemma project.

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
python3 experiments/collision_entropy.py 3 1         # log2 of unique functions
python3 experiments/collision_entropy.py 3 1 --circuits  # weight by circuit count
python3 experiments/collision_entropy.py 3 1 --list-counts  # table counts
python3 experiments/collision_entropy.py 3 1 --list-counts --descending
python3 experiments/collision_entropy.py 3 1 --list-counts --top 5
```

## Status

This is still a research prototype. The core-agreement lemma is fully proven, and the entropy-drop lemma `exists_coord_entropy_drop` is proved in `entropy.lean`.  The cardinal analogue `exists_coord_card_drop` is now implemented directly in `Boolcube.lean`; an earlier standalone demonstration file has been removed. `buildCover` splits on uncovered pairs using `sunflower_step` or the entropy drop, and preliminary proofs of its properties (`buildCover_mono` and `buildCover_card_bound`) have been added. The convenience wrapper `coverFamily` exposes these results via lemmas `coverFamily_mono`, `coverFamily_spec_cover` and `coverFamily_card_bound`. Collision entropy for a single function lives in `collentropy.lean`.  A formal definition of sensitivity with the lemma statement `low_sensitivity_cover` is available.  A small `DecisionTree` module provides depth, leaf counting, path extraction and the helper `subcube_of_path`.  Lemmas `path_to_leaf_length_le_depth` and `leaf_count_le_pow_depth` bound the recorded paths and the number of leaves, and `low_sensitivity_cover_single` sketches the tree-based approach.  `acc_mcsp_sat.lean` sketches the SAT connection. Numeric counting bounds remain open, so the repository documents ongoing progress rather than a finished proof.

The migration to the new `pnp` namespace is largely complete.  Every module has
been copied from the historical `Pnp2` directory and now compiles under the new
hierarchy.  The old files remain for reference because several of the migrated
modules are only skeletons.  See `migration.md` for a list of missing proofs and
tests that still need to be ported.

## Development plan

The next milestone is completing the Family Collision-Entropy Lemma in Lean. Key
tasks are:
1. ~~finish the cardinal lemma `exists_coord_card_drop` in `Boolcube.lean` to
   complement the proved entropy drop,~~
2. ~~move all modules from `Pnp2` into the `pnp` directory and extend the test
   suite to cover the migrated code,~~
3. complete the `buildCover` correctness proof and establish the bound
   `mBound_lt_subexp`,
4. integrate the decision-tree cover into `low_sensitivity_cover`,
5. expose `FamilyCover` and single-function entropy utilities throughout the
   codebase.
Once these are done the lemma `FCE_lemma` will follow.
