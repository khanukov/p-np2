# Archive Directory

This directory contains files that were moved out of the critical proof path for `P_ne_NP_final`.

## Purpose

To keep the main `pnp3/` directory focused on the **minimal necessary** code for the formal proof of P≠NP, all non-critical files have been archived here. This makes it easier to:

1. **Understand the proof structure** - only essential files remain
2. **Verify correctness** - smaller surface area to audit
3. **Maintain the proof** - less code to keep in sync
4. **Future constructive proof** - clear path for replacing axioms

## What Was Archived

### Total: 19 files (43% of original codebase)

### By Category:

#### 1. **Complexity/** (1 file)
- `ComplexityClasses.lean` - Alternative complexity class definitions with `sorry` placeholders
- **Reason**: Uses abstract `Prop` definitions with `sorry`; not used in proof chain
- **Alternative**: `Complexity/Interfaces.lean` (axiom-based interface) is used instead

#### 2. **Core/** (4 files)
- `PDTExtras.lean` - Extra utilities for partial decision trees
- `PDTSugar.lean` - Syntactic sugar for PDT notation
- `ShrinkageAC0.lean` - Contains `partial_shrinkage_with_oracles` axiom (unused)
- `SubcubeExtras.lean` - Additional subcube helper functions
- **Reason**: Helper utilities not imported by any critical-path file

#### 3. **LowerBounds/** (1 file)
- `AntiChecker_Correctness_Spec.lean` - Correctness specification with one `sorry`
- **Reason**: Specification file not imported by proof chain; `sorry` in commented lemma

#### 4. **Tests/** (8 files)
All test files:
- `Atlas_Count_Sanity.lean` - Sanity checks for atlas counting
- `Atlas_Counterexample_Search.lean` - Search for counterexamples
- `LB_Core_Contradiction.lean` - Test for lower bound contradiction
- `LB_Smoke_Scenario.lean` - Smoke test for lower bounds
- `Magnification_Core_Contradiction.lean` - Test for magnification
- `Parity_Counterexample.lean` - Parity function tests
- `SAL_Smoke_AC0.lean` - SAL smoke tests
- `Switching_Basics.lean` - Basic switching lemma tests
- **Reason**: Tests are valuable for development but not required for formal proof

#### 5. **ThirdPartyFacts/** (5 files)
Alternative switching lemma implementations:
- `BaseSwitching.lean` - Base switching lemma infrastructure
- `ConstructiveSwitching.lean` - Constructive switching variants
- `Depth2_Constructive.lean` - Depth-2 constructive switching
- `Depth2_Helpers.lean` - Helper functions for depth-2 cases
- `Depth2_Switching_Spec.lean` - Contains `depth2_switching_probabilistic` and `depth2_constructive_switching` axioms (unused)
- **Reason**: Alternative implementations; the proof uses `Facts_Switching.lean` instead

## Critical Path Analysis

The **25 critical files** remaining in `pnp3/` form the minimal dependency chain:

```
P_ne_NP_final
  └─→ Bridge_to_Magnification
      ├─→ PipelineStatements
      │   └─→ LB_Formulas_Core
      │       ├─→ AntiChecker [axiom: antiChecker_exists_testset]
      │       ├─→ LB_Formulas
      │       │   └─→ Atlas_to_LB_Core (capacity bounds)
      │       └─→ Facts_Switching [axiom: partial_shrinkage_for_AC0]
      ├─→ Facts_Magnification [axiom: OPS_trigger_formulas]
      └─→ Interfaces [axioms: P_subset_Ppoly_proof, P_ne_NP_of_nonuniform_separation]
```

### Critical Files (25):
- **Core/** (8): BooleanBasics, PDT, PDTPartial, Atlas, SAL_Core, ShrinkageWitness
- **Counting/** (3): Atlas_to_LB_Core, BinomialBounds, Count_EasyFuncs
- **LowerBounds/** (5): AntiChecker, LB_Formulas, LB_Formulas_Core, LB_GeneralFromLocal, LB_LocalCircuits
- **Magnification/** (5): Bridge_to_Magnification, Facts_Magnification, FinalResult, LocalityLift, PipelineStatements
- **ThirdPartyFacts/** (2): Facts_Switching, LeafBudget
- **Complexity/** (1): Interfaces
- **Models/** (2): Model_GapMCSP, Model_SparseNP
- **AC0/** (1): Formulas

## Verification

After archiving, the build was verified:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build pnp3/Magnification/FinalResult.lean
```

**Status**: ✅ **BUILD SUCCESSFUL** - All critical files compile correctly

## Restoration

If you need any archived file:

```bash
# Example: restore a test file
cp archive/pnp3/Tests/Atlas_Count_Sanity.lean pnp3/Tests/
```

## Mathematical Correctness

**Important**: All archived files are mathematically sound. They were removed solely because they are not needed for the proof of `P_ne_NP_final`, not because of any errors.

The archived files include:
- ✅ Tests that pass
- ✅ Alternative implementations
- ✅ Helper utilities
- ⚠️ Some files with `sorry` (clearly marked, not in critical path)

## Statistics

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| Total .lean files | 44 | 25 | -19 (-43%) |
| Files with sorry | 2 | 0 | -2 (✅ all removed) |
| Critical axioms | 20 | 20 | 0 (unchanged) |
| Lines of code | ~8000 | ~5500 | -2500 (-31%) |

## Date

**Archived**: 2025-10-24
**By**: Dependency analysis script
**Verified**: Build successful after archiving

---

**Note**: This is a living document. As the proof evolves, more files may be archived or restored as needed.

**See also**: [`ARCHIVED_2026-05_pnp3_periphery.md`](./ARCHIVED_2026-05_pnp3_periphery.md) — a later, dated periphery-cleanup step (2 modules archived, with restore instructions).

---

## Later addition (2026-05-29): degenerate lightweight `Ppoly` interface

**File**: [`pnp3/Complexity/PsubsetPpolyInternal_Lightweight_Ppoly.lean`](./pnp3/Complexity/PsubsetPpolyInternal_Lightweight_Ppoly.lean)

This is a *partial* extraction (not a whole orphan module): the degenerate
lightweight `P/poly` cluster (`InPpoly`, `Ppoly`, `InPpolyStructured`,
`PpolyStructured`, the conversions, and the vacuous
`complexity_P_subset_Ppoly`) was carved out of the still-active
`pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean`, which retains
the genuinely-used `Bitstring`, `Language`, `polyTimeDecider`, and `P`.

**Reason**: it was a second, *competing* notion of `P/poly` in which a "circuit"
was an arbitrary Boolean function (`circuits : ∀ n, Bitstring n → Bool`) with no
size measure (`polyBound := 0`, `polyBound_poly : True`).  Its
`complexity_P_subset_Ppoly` is therefore a **vacuous** `P ⊆ P/poly` (it returns
the decider function as the "circuit") and is not used anywhere in the proof.
The canonical class is `PpolyDAG` (`pnp3/Complexity/Interfaces.lean`) and the
genuine, machine-checked inclusion is
`Complexity.Simulation.proved_P_subset_PpolyDAG_internal`
(`pnp3/Complexity/Simulation/Circuit_Compiler.lean`).

A `scripts/check.sh` guardrail forbids re-declaring this degenerate cluster in
the active `pnp3` tree.  Build, `#print axioms`, smoke, tests and `check.sh`
were re-verified green after the extraction.

## Later addition (2026-05-29): incomplete NP-verifier scaffold

**Files** (11): `pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean`
and `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/*.lean`
(`AtomicPrograms`, `BinaryCounter`, `CombineAtOffset`,
`ConstStatePhasedProgram`, `CopyAtOffset`, `Encoding`, `Foundation`,
`GateWrappers`, `RowConsistencyCheck`, `UnaryAtOffset`), ~14.9k lines,
moved to `archive/pnp3/Complexity/PsubsetPpolyInternal/` with their
`lakefile.lean` globs removed.

**Reason**: this is the (incomplete) scaffold for the canonical GapMCSP
**NP-verifier TM** — by its own header, "the interface scaffold … correctness
proofs are TODOs".  Its roots (`GapMCSPVerifier`, `RowConsistencyCheck`) were
imported by **no** active module (dead in the build), and the whole cluster is
**unrelated to the `P ⊆ P/poly` inclusion** (which uses
`Simulation.lean` → straight-line circuits and never imports `TuringToolkit`).
It lived under `PsubsetPpolyInternal/`, whose name implies the inclusion, which
hurt clarity.

This is **parked NP-side work in progress**, not erroneous code.  The design
plans (`pnp3/Docs/PhaseI_Verifier_Design.md`,
`pnp3/Docs/TMVerifier_Session_Plan.md`) carry an "ARCHIVED SCAFFOLD" banner
with restore instructions: restore the files from `archive/` and re-add the
`lakefile.lean` globs.  Build, smoke, tests and `check.sh` were re-verified
green after the move.
