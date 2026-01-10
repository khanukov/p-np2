# P≠NP formalization repository
> **Status (2025-12-17)**: Active development centres on the new `pnp3/` pipeline (Switching-Atlas Lemma → hardness magnification → circuit lower bounds).  Earlier constructive pipelines remain archived for provenance but are no longer part of the active build.

This repository hosts the third major iteration of our Lean 4 formalisation effort aimed at the separation `P ≠ NP`.  The current roadmap, nicknamed **PNP3**, revolves around the **Switching-Atlas Lemma (SAL)** and the downstream magnification bridges needed to transfer SAL-based lower bounds into hardness for **Partial MCSP**.  The former GapMCSP pipeline now lives under `archive/`.

## Scientific contribution

We introduce and Lean-verify a constructive bridge from shrinkage to a uniform atlas of subcubes for whole families of Boolean functions (Switching-Atlas Lemma, SAL) and prove a general Covering-Power capacity bound. **To the best of our knowledge**, this SAL packaging and its end-to-end Lean verification are new contributions to both formal methods and complexity theory.

**Current status**: The development provides a **conditional derivation** of P ≠ NP, contingent on external switching/shrinkage inputs: the theorems `partial_shrinkage_for_AC0` and `shrinkage_for_localCircuit` both require externally supplied witnesses (`AC0CircuitWitness` and `LocalCircuitWitness`). All anti-checker and magnification bridges are machine-checked theorems.

**Documentation**: See [TECHNICAL_CLAIMS.md](TECHNICAL_CLAIMS.md) for detailed claims, [FAQ.md](FAQ.md) for common questions, and [AXIOM_ANALYSIS_FINAL.md](AXIOM_ANALYSIS_FINAL.md) for external input tracking.

Historically, versions `Pnp1/` and `Pnp2/` implemented the **Family Collision-Entropy (FCE) Lemma** pipeline.  The corresponding sources are kept offline as read-only artefacts documenting the earlier constructive cover approach.  They still compile with the present toolchain and can be consulted for proofs, experiments, and documentation of the FCE era when needed.

## Assumptions & External Facts

The current PNP3 pipeline is **conditional**: Lean checks all downstream proofs, but some inputs are imported as external facts or require explicit witnesses. This section lists the critical dependencies so the documentation matches the actual proof chain.

### External axioms / imported facts
* `PartialMCSP_is_NP_Hard` (imported from `pnp3/ThirdPartyFacts/Hirahara2022.lean`). This is the stated NP-hardness of Partial MCSP used as an external theorem in the final result.
* `P_subset_Ppoly_proof` (imported from `pnp3/ThirdPartyFacts/PsubsetPpoly.lean`). This supplies the standard inclusion `P ⊆ P/poly` as an external proof object.

### External witnesses (required hypotheses)
* `AC0CircuitWitness` and `LocalCircuitWitness` are required to instantiate the shrinkage facts used by the SAL pipeline; these witnesses are supplied externally, while the downstream derivations are Lean-checked.
* `FamilyIsLocalCircuit` witnesses are required in the magnification bridge for partial formulas (`P_ne_NP_from_partial_formulas`) to trigger the non-uniform separation step. In the current codebase this is still an external hypothesis: it is defined as a `Nonempty` wrapper around `LocalCircuitWitness`, and no global constructor is provided yet.

### What is Lean-checked vs. external
* Lean-checked: the logical pipeline from shrinkage/anti-checker assumptions to `NP ⊄ P/poly`, and the classical implication `NP ⊄ P/poly` + `P ⊆ P/poly` ⇒ `P ≠ NP`.
* External: NP-hardness of Partial MCSP, the `P ⊆ P/poly` proof object, and the shrinkage/locality witnesses needed to instantiate the SAL-based machinery.

## Proof pipeline

The current (conditional) proof chain used by the final result follows:

`FinalResult → P_ne_NP_from_partial_formulas → NP_not_subset_Ppoly_from_partial_formulas → OPS_trigger_formulas_partial → …`

The ellipsis (`…`) expands into the SAL + anti-checker pipeline, which ultimately depends on external shrinkage/locality witnesses.

## Repository layout

### Core PNP3 development (`pnp3/`)
* `Core/` – core combinatorics of subcubes, partial decision trees, and the SAL atlas infrastructure.
* `Counting/` – capacity bounds for atlases together with approximation lemmas.
* `ThirdPartyFacts/` – external inputs (multi-switching theorems, lightweight function counts, etc.).
* `Models/` – formal interfaces for Partial MCSP, plus related promise problems.  Legacy GapMCSP models live under `archive/pnp3/Models/`.
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
2. SAL-based magnification aligns better with contemporary lower-bound techniques and offers a clearer path to hardness for Partial MCSP, so the GapMCSP chain has been archived.
3. The Partial MCSP track now drives the main pipeline (final result is in the partial branch), with GapMCSP kept only under `archive/` for legacy reference.
4. All new development happens inside `pnp3/`, while the legacy directories only serve as archival references for earlier results.

For detailed migration plans and milestone tracking, consult `archive/pnp3/Docs/PLAN.md` and the root `TODO.md`.
