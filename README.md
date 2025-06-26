# P≠NP formalization repository

This repository collects experimental Lean files that sketch a formal proof of the **Family Collision‑Entropy Lemma (FCE‑Lemma)**.  The lemma aims to cover families of Boolean functions with a subexponential number of monochromatic subcubes and is a building block for a potential proof that `P ≠ NP`.

The code is **not** a complete proof: many declarations end with `sorry`.  The goal is to document interfaces and provide a sandbox for future formalisation.

## Layout

* `BoolFunc.lean` – basic types for Boolean functions, points and subcubes (fully proved).
* `Boolcube.lean` – extended definitions together with a proved entropy‑drop lemma.
* `entropy.lean` – collision entropy framework (proof of `EntropyDrop` still marked `sorry`).
* `sunflower.lean` – minimal sunflower lemma used downstream.
* `agreement.lean` – statement of the core‑agreement lemma with proof placeholder.
* `cover.lean` – skeleton of the covering algorithm.
* `bound.lean` – arithmetic bounds deriving the subexponential size estimate.
* `family_entropy_cover.lean` – placeholder for the family version of the cover.
* `merge_low_sens.lean` – stub combining low‑sensitivity and entropy covers.
* `canonical_circuit.lean` – Boolean circuits with a basic canonicalisation function.
* `table_locality.lean` – statement of the table locality lemma (roadmap B‑2).
* `examples.lean` – runnable examples illustrating the definitions.
* `experiments/` – small Python tools exploring rectangle covers, including
  `lemma_b_search.py`, `single_gate_count.py`, and `collision_entropy.py`.
  The directory also contains enumeration logs such as
  `results_n2_n3.md`, `results_n4_n5.md`, and `results_n6.md`.
* `docs/` – assorted background notes.  The file `E1_roadmap.md` contains the current roadmap for the ACC⁰∘MCSP subexponential SAT approach.
* `Task_description.md`, `fce_lemma_proof.md` – original research notes explaining the FCE‑Lemma project.

## Building

The Lean files require **Lean 4** together with **mathlib4** (≥ 2025‑05‑20).
A minimal `lakefile.lean` and `lean-toolchain` are included.  Install `elan`
(which also provides the `lake` tool) and run

```bash
elan toolchain install $(cat lean-toolchain)
```

to set up the compiler.  Then fetch the cached dependencies and build the
project with:

```bash
lake exe cache get
lake build
```

`examples.lean` can also be executed directly with `lean --run examples.lean` once
the dependencies have been downloaded.

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

This is a research prototype.  Many modules contain `sorry` placeholders and only partial proofs.  The repository is intended for exploration and does not constitute a finished argument.
