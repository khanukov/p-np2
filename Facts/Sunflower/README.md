# Fact: classical sunflower lemma

Repository-level proof-status checklist (outside this standalone fact package):
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

This directory packages the classical Erdős–Rado sunflower lemma as a
self-contained Lake project.  The development mirrors the original
formalisation from the archival boolean complexity prototype but is
reorganised so that other projects can import the lemma without pulling in the
rest of the historical code base.

## Layout

- `FactSunflower.lean` — lightweight wrapper re-exporting the main
  combinatorial statements.
- `FactSunflower/Proof/Sunflower.lean` — core development of the
  classical lemma together with the finite sunflower combinatorics used
  by the cover algorithm.
- `FactSunflower/Proof/Sunflower/RSpread.lean` — the `R`-spread
  condition and its basic properties.
- `FactSunflower/AxiomChecks.lean` — mechanical verification that the
  exported theorems use no axioms beyond classical choice.

The files remain heavily commented in order to document the combinatorial
arguments.  They are intentionally close to the historic sources so that
cross-references remain easy to follow.

## Using the fact in other projects

Importing `FactSunflower` exposes the canonical bound
```
Sunflower.threshold w p = (p - 1) ^ w * w!
```
and the classical existence theorem
```
Sunflower.sunflower_exists_classic
```
together with the `SunflowerFam` structure used by the constructive cover
algorithm.  The auxiliary module also provides the `RSpread` predicate
that appears in the entropy-based arguments of the archival boolean complexity
prototype.

## Building the package locally

The directory ships with its own `lean-toolchain`, so the usual workflow
is simply

```bash
cd Facts/Sunflower
lake build
```

Running `lake build` also evaluates `FactSunflower/AxiomChecks.lean`,
which fails if any of the re-exported declarations start depending on
unexpected axioms.  This gives a quick regression test for the
constructive status of the package.

On the first run Lake downloads `mathlib4` and its auxiliary packages as
specified in `manifest.json`.  Subsequent builds reuse the cached copies
under `.lake/` and finish quickly.
