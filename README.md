# P≠NP formalization repository

This repository collects experimental Lean files that sketch a formal proof of the **Family Collision‑Entropy Lemma (FCE‑Lemma)**.  The lemma aims to cover families of Boolean functions with a subexponential number of monochromatic subcubes and is a building block for a potential proof that `P ≠ NP`.

The code is **not** a complete proof: many declarations end with `sorry`.  The goal is to document interfaces and provide a sandbox for future formalisation.

## Layout

* `bool_func.lean` – basic types for Boolean functions, points and subcubes (fully proved).
* `Boolcube.lean` – extended definitions together with a proved entropy‑drop lemma.
* `entropy.lean` – collision entropy framework (proof of `EntropyDrop` still marked `sorry`).
* `sunflower.lean` – minimal sunflower lemma used downstream.
* `agreement.lean` – statement of the core‑agreement lemma with proof placeholder.
* `cover.lean` – skeleton of the covering algorithm.
* `bound.lean` – arithmetic bounds deriving the subexponential size estimate.
* `family_entropy_cover.lean` – placeholder for the family version of the cover.
* `merge_low_sens.lean` – stub combining low‑sensitivity and entropy covers.
* `examples.lean` – runnable examples illustrating the definitions.
* `experiments/` – small Python tools exploring rectangle covers, including `lemma_b_search.py` and `single_gate_count.py`.
* `docs/` – assorted background notes.  The file `E1_roadmap.md` contains the current roadmap for the ACC⁰∘MCSP subexponential SAT approach.
* `Task_description.md`, `fce_lemma_proof.md` – original research notes explaining the FCE‑Lemma project.

## Building

The Lean files require **Lean 4** together with **mathlib4** (≥ 2025‑05‑20).  The repository does not include a `lakefile`; to experiment, create a Lean project that depends on mathlib and add these files, or invoke `lean` directly once mathlib is available.

`examples.lean` can be executed with `lean --run examples.lean` after the dependencies are set up.

## Experiments

The `experiments/` directory contains Python scripts that enumerate small
Boolean circuits to collect data for Lemma B.  Invoke them with Python 3:

```bash
python3 experiments/lemma_b_search.py     # exhaustive search of small circuits
python3 experiments/single_gate_count.py  # list functions from a single gate
```

## Status

This is a research prototype.  Many modules contain `sorry` placeholders and only partial proofs.  The repository is intended for exploration and does not constitute a finished argument.
