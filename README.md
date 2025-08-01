# P≠NP formalization repository

This repository collects experimental Lean files that sketch a formal proof of the **Family Collision‑Entropy Lemma (FCE‑Lemma)**.  The lemma aims to cover families of Boolean functions with a subexponential number of monochromatic subcubes and is a building block for a potential proof that `P ≠ NP`.

The project is **not** yet a complete proof: several key statements are
currently provided as axioms without proof.  Many basic lemmas have now been
formalised, so the repository also serves as a record of ongoing progress
towards a full argument.

The development now happens entirely in the `Pnp2` namespace.  The previous
development tree is kept only as a historical snapshot and is no longer part of
the build.

Several files continue to contain `sorry` placeholders and axiomatic
statements while the formal proofs are completed.  These markers are
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
  cover constructors.  The module now integrates a sunflower step via `sunflower_exists` that extracts a rectangle covering several functions at once.  A lemma
  `monochromatic_point` still shows that single‑point subcubes are
  automatically monochromatic for any Boolean function.

* `entropy.lean` – collision entropy framework with the full `EntropyDrop`
  lemma proven alongside basic tools such as `collProb_le_one`.  The
  auxiliary lemma `exists_restrict_half` shows that some input bit
  restricts a family to at most half its size.  Its real-valued
  variant `exists_restrict_half_real` and the probability version
  `exists_restrict_half_real_prob` provide the bridge to analytic
  bounds, and `exists_coord_entropy_drop` turns this into a one‑bit drop
  of collision entropy.
* `sunflower.lean` – full classical sunflower lemma `sunflower_exists` now
  formalised **inside `Pnp2`** (ported from the previous development folder).
* `Sunflower/RSpread.lean` – definition of scattered families (`RSpread`).
  The lemma `RSpread.mono` now shows that a larger spread parameter implies
  a smaller one when `0 < R₂ ≤ R₁`.  Additional helper lemmas
  (`RSpread.card_bound`, `RSpread.one_of_nonempty`, `RSpread.card_filter_le`)
  rephrase the definition and handle the trivial case `R = 1`.
* `Agreement.lean` – complete proof of the core‑agreement lemma.
* `cover.lean` – experimental cover builder that keeps track of the
  set of uncovered inputs via `firstUncovered`.  The entropy split now
  uses `exists_coord_entropy_drop`, and the sunflower step relies on
  `sunflower_exists`.  Monochromaticity of the resulting cover is now fully established via the lemma `buildCover_mono`.  The companion counting lemma `buildCover_card_bound` has been proven through a complete measure-based induction on `μ(F, h, Rset) = 2 * h + |uncovered F Rset|`.
  The helper lemma `AllOnesCovered.union` abstracts the union step in
  the coverage proof.
* `Cover/Compute.lean` – lightweight wrapper exposing a constructive
  variant `buildCoverCompute` that enumerates the rectangles as a list.
  The current implementation still returns an empty list, serving as a
  placeholder for the future recursive procedure.  Its specification is
  proven and the file is used by `Algorithms/SatCover` for basic SAT
  experimentation.
* `bound.lean` – arithmetic bounds deriving the subexponential size estimate;
  the main inequality `mBound_lt_subexp` is now fully proved in the
  `Pnp2` namespace.
* `collentropy.lean` – collision entropy of a single Boolean function with
  basic lemmas such as `H₂Fun_le_one`.
* `CollentropyBasic.lean` – trimmed-down entropy file containing only the
  bounds needed for the SAT solver. Several numeric inequalities remain
  admitted for the time being.
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
* `Algorithms/SatCover.lean` – constructive SAT search procedure scanning the
  rectangles from `buildCoverCompute`.  It currently falls back to enumerating
  all points but provides the intended interface for meet-in-the-middle
  extensions.
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
* `docs/` – assorted background notes.  The file `E1_roadmap.md` contains the
  current roadmap for the ACC⁰∘MCSP subexponential SAT approach.  A new note
  `buildCover_card_bound_outline.md` summarises the measure-based induction used
  in the proof of `buildCover_card_bound`.  The document
  `canonical_eq_proof_plan.md` records the original sketch for proving that
  canonical circuits coincide exactly when their evaluations agree.  The
  theorem is formalised in `Pnp2/canonical_circuit.lean` as
  `canonical_eq_iff_eqv`.
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
python3 experiments/capacity_drop.py 6 3  # α drop for up to 6 inputs
python3 experiments/capacity_drop.py --prefix 7 3  # prefix drop on 7 inputs
python3 experiments/collision_entropy.py 3 1         # log2 of unique functions
python3 experiments/collision_entropy.py 3 1 --circuits  # weight by circuit count
python3 experiments/collision_entropy.py 3 1 --list-counts  # table counts
python3 experiments/collision_entropy.py 3 1 --list-counts --descending
python3 experiments/collision_entropy.py 3 1 --list-counts --top 5
```

## Status

This is still a research prototype. The core-agreement lemma is fully proven, and the entropy-drop lemma `exists_coord_entropy_drop` is proved in `entropy.lean`.  The cardinal analogue `exists_coord_card_drop` is now formalised in `Boolcube.lean`; an earlier standalone demonstration file has been removed. `buildCover` splits on uncovered pairs using `sunflower_step` or the entropy drop.  `buildCover_mono` and `buildCover_card_bound` are now fully formalised via a measure-based recursion.  The convenience wrapper `coverFamily` exposes these results via lemmas `coverFamily_mono`, `coverFamily_spec_cover` and `coverFamily_card_bound`. Collision entropy for a single function lives in `collentropy.lean`.  A formal definition of sensitivity with the lemma statement `low_sensitivity_cover` is available.  A small `DecisionTree` module provides depth, leaf counting, path extraction and the helper `subcube_of_path`.  Lemmas `path_to_leaf_length_le_depth` and `leaf_count_le_pow_depth` bound the recorded paths and the number of leaves, and `low_sensitivity_cover_single` sketches the tree-based approach.  `acc_mcsp_sat.lean` sketches the SAT connection. The numeric bounds have been completed in `bound.lean`, culminating in the theorem `family_collision_entropy_lemma_table`. This establishes the sub-exponential cover (Lemma B).
The newly introduced `Cover/Compute.lean` and `Algorithms/SatCover.lean` provide a constructive cover enumerator and a simple SAT search routine; their specifications are proven although the implementations are still placeholders.

Within `Pnp2` the overall structure of the FCE argument is complete and the focus shifts to optimising the constructive algorithms and reconnecting the SAT outline to recover the full `P ≠ NP` implication.

The code base has returned to the `Pnp2` namespace.  All major modules have been ported and `migration.md` now serves only as a historical record.  The build system now targets only `Pnp2` and the historical files are excluded.

Work is ongoing on the decision-tree construction for low-sensitivity families.
The lemma `decisionTree_cover` is currently axiomatic, but the repository
includes helper definitions (`DecisionTree`, `subcube_of_path`) and leaf-count
bounds that will support a full proof in future commits.

### Development namespace

`Pnp2` is now the sole development directory.  It contains all maintained
proof scripts and new lemmas.  The legacy `pnp` folder has been removed and
no longer ships with the repository.

## Development plan

The Family Collision-Entropy Lemma is now formalised. Remaining tasks include:
1. ~~finish the cardinal lemma `exists_coord_card_drop` in `Boolcube.lean` to
   complement the proved entropy drop,~~
2. ~~move all modules from the legacy directory into `Pnp2` and extend the test
   suite to cover the migrated code,~~
3. ~~complete the `buildCover` correctness proof and establish the bound
   `mBound_lt_subexp`,~~
4. integrate the decision-tree cover into `low_sensitivity_cover`,
5. expose `FamilyCover` and single-function entropy utilities throughout the
   codebase.
The lemma `FCE_lemma` is now available, proving the desired sub-exponential bound.
The corollary `family_collision_entropy_lemma_table` packages this result
as **Lemma B**, yielding a joint monochromatic cover of size `2^{n/100}`
for large enough `n`.

The numeric bounds have been incorporated into the development.
