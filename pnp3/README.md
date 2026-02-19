# `pnp3/`: Active Proof Tree

`pnp3/` is the active Lean formalization tree used by the current project result.
It implements the pipeline:

`Part A (Shrinkage/SAL) -> Part B (Counting) -> Part C (Anti-checker) -> Part D (Magnification)`

## Main entry points
- `Magnification/FinalResult.lean` - final theorem name (`P_ne_NP_final_asymptotic`)
- `Tests/AxiomsAudit.lean` - final-cone axiom dependency printout
- `Tests/CoreConeAxiomsAudit.lean` - core-cone axiom dependency printout
- `Tests/AntiCheckerConeAxiomsAudit.lean` - anti-checker-cone axiom dependency printout

## Directory map
- `Core/` - subcubes, partial decision trees, atlas/SAL core.
- `Counting/` - capacity and approximation bounds.
- `Models/` - Partial MCSP model/language definitions.
- `LowerBounds/` - Part C lower-bound kernels and anti-checker machinery.
- `Magnification/` - Part D bridges and final assembly.
- `ThirdPartyFacts/` - external interfaces/scaffolding and imported bridges.
- `Complexity/` - complexity-class/reduction interfaces used by magnification.
- `Tests/` - regression and audit Lean files.
- `Docs/` - module-local technical notes.

## Documentation policy
Global project status/planning docs are centralized in `docs/` at repository root.
Module-local deep technical notes stay under `pnp3/Docs/`.
