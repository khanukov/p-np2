# P≠NP formalization repository
> **Status (2026-02-20)**: `pnp3/` builds successfully and provides a machine-checked **conditional** partial-pipeline result (`NP ⊄ PpolyFormula`) with explicit external hypotheses.

This repository hosts the third major iteration of our Lean 4 formalisation effort for complexity lower bounds around **Partial MCSP**. The current roadmap, nicknamed **PNP3**, revolves around the **Switching-Atlas Lemma (SAL)** and downstream magnification bridges.

## Scientific contribution

We introduce and Lean-verify a constructive bridge from shrinkage to a uniform atlas of subcubes for whole families of Boolean functions (Switching-Atlas Lemma, SAL) and prove a general Covering-Power capacity bound. **To the best of our knowledge**, this SAL packaging and its Lean verification are new contributions to both formal methods and complexity theory.

**Current status**: The development provides a conditional, machine-checked derivation of `NP ⊄ PpolyFormula` via the partial pipeline. The active final chain is parameterized by explicit locality/certificate assumptions. Shrinkage/switching inputs are still witness-backed external inputs.

**Documentation**: Start with [STATUS.md](STATUS.md), then [TODO.md](TODO.md), [AXIOMS_FINAL_LIST.md](AXIOMS_FINAL_LIST.md), [TECHNICAL_CLAIMS.md](TECHNICAL_CLAIMS.md), and [FAQ.md](FAQ.md).

## Assumptions & External Facts

The current PNP3 pipeline is **conditional**: Lean checks all downstream proofs, but some inputs are still explicit hypotheses.

### External assumptions / imported facts
* Goal-shaped bridge assumptions in `pnp3/ThirdPartyFacts/PpolyFormula.lean`:
  * `GapPartialMCSPPpolyRealToPpolyFormulaGoal p`

### External witnesses / providers (required hypotheses)
* `AC0CircuitWitness` and `LocalCircuitWitness` are required to instantiate shrinkage facts in Part A.
* Locality-lift on the partial bridge requires explicit stability/provider data:
  * `hStable` (restriction stability), or
  * certificate path via `ShrinkageCertificate.Provider` + bound `hCardHalf`.
* Magnification still assumes a structured locality provider:
  * `StructuredLocalityProviderPartial`.

### What is Lean-checked vs. external
* Lean-checked: anti-checker core, locality-lift bridge plumbing, magnification glue, and contrapositive triggers for formula separation.
* External: `GapPartialMCSPPpolyRealToPpolyFormulaGoal p`, shrinkage witnesses, and constructive closure of certificate cardinality obligations (`hCardHalf`) in partial locality-lift usage.
* Constructive entrypoint for the embed gap: `GapPartialMCSPFormulaizer` in `pnp3/ThirdPartyFacts/PpolyFormula.lean`.

## Proof pipeline

The current (conditional) proof chain used by the active final result follows:

`FinalResult → NP_not_subset_PpolyFormula_from_partial_formulas → OPS_trigger_formulas_partial_of_provider_formula_separation → ...`

The ellipsis expands into the SAL + anti-checker pipeline, which ultimately depends on external shrinkage/locality witnesses and bridge/provider hypotheses.

## Repository layout

### Core PNP3 development (`pnp3/`)
* `Core/` – core combinatorics of subcubes, partial decision trees, and the SAL atlas infrastructure.
* `Counting/` – capacity bounds for atlases together with approximation lemmas.
* `ThirdPartyFacts/` – external inputs (multi-switching theorems, lightweight function counts, etc.).
* `Models/` – formal interfaces for Partial MCSP, plus related promise problems.
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

## Planning notes

For detailed migration plans and milestone tracking, consult the root `TODO.md`.
