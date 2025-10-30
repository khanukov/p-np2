# P≠NP formalization repository
> **Status (2025-10-24)**: Active development centres on the new `pnp3/` pipeline (Switching-Atlas Lemma → hardness magnification → circuit lower bounds).  Earlier constructive pipelines remain archived for provenance but are no longer part of the active build.

This repository hosts the third major iteration of our Lean 4 formalisation effort aimed at the separation `P ≠ NP`.  The current roadmap, nicknamed **PNP3**, revolves around the **Switching-Atlas Lemma (SAL)** and the downstream magnification bridges needed to transfer SAL-based lower bounds into hardness for (Gap)MCSP and, eventually, into a full separation.

## Scientific contribution

We introduce and Lean-verify a constructive bridge from shrinkage to a uniform atlas of subcubes for whole families of Boolean functions (Switching-Atlas Lemma, SAL) and prove a general Covering-Power capacity bound. **To the best of our knowledge**, this SAL packaging and its end-to-end Lean verification are new contributions to both formal methods and complexity theory.

**Current status**: The development provides a **conditional derivation** of P ≠ NP, contingent on external results (multi-switching, anti-checkers, magnification triggers) that are currently axiomatized. All internal glue and combinatorics are machine-checked.

**Documentation**: See [TECHNICAL_CLAIMS.md](TECHNICAL_CLAIMS.md) for detailed claims, [FAQ.md](FAQ.md) for common questions, and [AXIOM_ANALYSIS_FINAL.md](AXIOM_ANALYSIS_FINAL.md) for axiom tracking.

Historically, versions `Pnp1/` and `Pnp2/` implemented the **Family Collision-Entropy (FCE) Lemma** pipeline.  The corresponding sources are kept offline as read-only artefacts documenting the earlier constructive cover approach.  They still compile with the present toolchain and can be consulted for proofs, experiments, and documentation of the FCE era when needed.

## Repository layout

### Core PNP3 development (`pnp3/`)
* `Core/` – core combinatorics of subcubes, partial decision trees, and the SAL atlas infrastructure.
* `Counting/` – capacity bounds for atlases together with approximation lemmas.
* `ThirdPartyFacts/` – external inputs (multi-switching theorems, lightweight function counts, etc.).
* `Models/` – formal interfaces for (Gap)MCSP variants and related promise problems.
* `LowerBounds/` – lower-bound derivations for formulas and depth-limited circuits based on SAL.
* `Magnification/` – magnification bridges and literature interfaces culminating in the final separation statements.
* `Complexity/` – wrappers around standard complexity classes used by the magnification step.
* `Tests/` – executable Lean regression tests (parity sanity checks, smoke tests, etc.).
* `Docs/` – textual notes, milestone checklists, and bibliographic references for the SAL pipeline.

### Supporting material
* `experiments/` – Python tooling for enumerating small Boolean circuits, computing entropy statistics, and replaying classic experiments.  The scripts double as sanity checks for analytic bounds derived in `pnp3/`.
* `scripts/` – helper shell/Lean scripts (`scripts/check.sh`, smoke tests, cache warmers).
* `TODO.md` – current task tracking and migration checklists.


## Toolchain and build

The project targets **Lean 4** together with **mathlib4** ≥ 4.22.0-rc2.  Install `elan` (which also provides the `lake` tool) and run

```bash
elan toolchain install $(cat lean-toolchain)
```

to fetch the compiler.  Afterwards build the project with

```bash
lake exe cache get
lake build
```

If the cache download is blocked, rerun `lake build` to compile mathlib from source.

### Smoke tests

```bash
lean --run pnp3/Tests/Smoke.lean    # PNP3 regression tests
lake env lean --run scripts/smoke.lean
lake test                           # helper executables
./scripts/check.sh                  # full build + smoke test
```



## Development conventions

* Classical reasoning is freely available (we routinely open `Classical`).
* Noncomputable definitions are permitted whenever they simplify existence proofs; constructive variants are documented explicitly when downstream tooling needs them.
* Extensive file headers describe goals, dependencies, and completion criteria.  Follow the TODO markers inside `pnp3/` modules when contributing new proofs.

## Historical note: from FCE to SAL

The shift from the FCE-Lemma pipeline to the SAL programme (`pnp3/`) reflects the lessons learned during the September 2025 audit:

1. The constructive cover machinery is preserved for reproducibility but no longer drives the main separation strategy.
2. SAL-based magnification aligns better with contemporary lower-bound techniques and offers a clearer path to hardness for (Gap)MCSP.
3. All new development happens inside `pnp3/`, while the legacy directories only serve as archival references for earlier results.

For detailed migration plans and milestone tracking, consult `pnp3/Docs/PLAN.md` and the root `TODO.md`.
