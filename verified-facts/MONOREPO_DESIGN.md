# Monorepo Design Document

## Overview

This document describes the monorepo structure implemented for the p-np2 project, organizing verified mathematical facts as isolated, reusable subprojects.

## Motivation

As the P≠NP formalization grows, we identified the need to:

1. **Separate concerns**: Distinguish complete proofs from conditional derivations
2. **Enable reuse**: Allow other Lean projects to depend on specific verified facts
3. **Improve clarity**: Make it obvious which components have no axioms
4. **Facilitate review**: Let reviewers focus on self-contained pieces

## Architecture

```
p-np2/ (root)
├── pnp3/                      # Main PNP3 pipeline (SAL + magnification)
│   └── ... (axioms present)
├── Pnp2/                      # Legacy PNP2 (archived, FCE-based)
│   └── ... (historical)
├── verified-facts/            # ← New: Isolated verified facts
│   ├── README.md              # Overview of subprojects
│   ├── p-subset-ppoly/        # Subproject: P ⊆ P/poly
│   │   ├── lakefile.lean      # Independent build config
│   │   ├── lean-toolchain     # Lean version specification
│   │   ├── README.md          # Subproject documentation
│   │   ├── PSubsetPpoly.lean  # Main export file
│   │   ├── PSubsetPpoly/      # Source files
│   │   └── Utils/             # Helper modules
│   └── [future-fact]/         # Template for more facts
├── lakefile.lean              # Root config (references subprojects)
└── lean-toolchain
```

## Subproject Structure

Each verified fact follows this template:

```
verified-facts/[fact-name]/
├── lakefile.lean              # Lake configuration
├── lean-toolchain             # Lean version (copied from root)
├── README.md                  # Full documentation:
│                              #  - Main theorem statement
│                              #  - Proof method
│                              #  - Structure explanation
│                              #  - Building instructions
│                              #  - References
├── [FactName].lean            # Root export file
├── [FactName]/                # Source directory
│   ├── Core.lean              # Main proof
│   ├── [Module1].lean         # Supporting modules
│   └── [Subdir]/              # Subdirectories as needed
└── Utils/                     # Shared utilities (if needed)
```

## First Subproject: P ⊆ P/poly

### Extraction Process

1. **Identified source**: Pnp2/PsubsetPpoly.lean + dependencies
2. **Mapped dependencies**:
   - TM/Encoding.lean → Turing machine model
   - Circuit/*.lean → Circuit representations
   - Boolcube.lean, BoolFunc.lean → Boolean utilities
   - canonical_circuit.lean → Circuit definitions
   - Utils/Nat.lean → Number theory helpers

3. **Restructured**:
   - Created PSubsetPpoly/ namespace
   - Renamed PsubsetPpoly.lean → Core.lean
   - Fixed all imports (Pnp2.* → PSubsetPpoly.*)
   - Created root export file

4. **Documented**:
   - Subproject README.md (usage, structure, references)
   - verified-facts/README.md (monorepo overview)
   - This design document

5. **Integrated**:
   - Updated root lakefile.lean with require statement
   - Maintained backward compatibility (Pnp2/ still works)

### Statistics

- **Total code**: ~15,876 lines (15 files)
- **Core proof**: 507 KB (Core.lean)
- **Dependencies**: Lean 4.22.0-rc2, mathlib4
- **Status**: ✅ Complete, no axioms, no sorry

## Integration with Root Project

### Root lakefile.lean

```lean
require mathlib from git "..." @ "v4.22.0-rc2"

-- Verified fact: P ⊆ P/poly (isolated subproject)
require «p-subset-ppoly» from "."/  "verified-facts"/"p-subset-ppoly"

lean_lib Pnp2 where ...
@[default_target]
lean_lib PnP3 where ...
```

### Usage in pnp3

```lean
import PSubsetPpoly  -- Access to verified P ⊆ P/poly

-- Use in proofs
axiom P_subset_Ppoly_proof : P_subset_Ppoly  -- Can be replaced with import
```

## Benefits

### 1. Modularity
- Each fact is a standalone Lake project
- Can be built and tested independently
- Clear dependency boundaries

### 2. Reusability
- External Lean projects can depend on specific facts
- No need to import entire p-np2 codebase
- Semantic versioning possible per subproject

### 3. Clarity
- Obvious which results are complete (✅) vs. conditional (⚠️)
- Axiom count per subproject is explicit
- Documentation co-located with code

### 4. Scalability
- Easy to add more verified facts
- Template structure for consistency
- Root project stays organized

### 5. Review-Friendly
- Reviewers can focus on one subproject at a time
- Clear proof boundaries
- Self-contained documentation

## Workflow

### Building Entire Project

```bash
# From root
lake exe cache get  # Get mathlib cache (shared)
lake build          # Builds root + all subprojects
```

### Building Specific Subproject

```bash
cd verified-facts/p-subset-ppoly
lake exe cache get  # If not already cached
lake build          # Build only this fact
```

### Using in External Project

```lean
-- In external project's lakefile.lean
require psubsetppoly from git
  "https://github.com/khanukov/p-np2.git" @ "main" / "verified-facts/p-subset-ppoly"

-- In Lean code
import PSubsetPpoly
example : P ⊆ Ppoly := P_subset_Ppoly
```

## Roadmap: Future Subprojects

Candidates for extraction:

### High Priority
- **Switching Lemma** (if/when formalized)
  - Håstad's depth reduction for AC⁰
  - ~A.1-A.5 axioms from AXIOMS_FINAL_LIST.md

### Medium Priority
- **Sunflower Lemma**
  - Already partially formalized in Pnp2/Sunflower/
  - Combinatorial structure theorem

- **Decision Tree Basics**
  - Pnp2/DecisionTree.lean (68KB)
  - Sensitivity bounds

### Lower Priority
- **Boolean Function Utilities**
  - Pnp2/BoolFunc.lean (35KB)
  - Subcube operations (Pnp2/Boolcube.lean)

- **Circuit Lower Bounds Toolkit**
  - Reusable infrastructure for proving lower bounds

## Maintenance

### Adding a New Verified Fact

1. Create directory: `verified-facts/[fact-name]/`
2. Copy template structure (lakefile, README, etc.)
3. Extract/write source files under `[FactName]/`
4. Fix imports to use new namespace
5. Add documentation (README.md, comments)
6. Add require line to root lakefile.lean
7. Test: `cd verified-facts/[fact-name] && lake build`
8. Update verified-facts/README.md
9. Commit and push

### Updating Existing Subproject

1. Make changes in `verified-facts/[fact-name]/`
2. Test locally: `lake build`
3. Update version in lakefile.lean (if public API changed)
4. Update README.md if structure changed
5. Commit with clear changelog
6. Update root lakefile if needed

## Design Decisions

### Why separate lakefile per subproject?

- Independence: Each fact can specify its own dependencies
- Versioning: Can track versions separately
- Clarity: Build configuration co-located with code

### Why copy lean-toolchain?

- Consistency: Ensures same Lean version across subprojects
- Explicitness: Version visible without checking root
- Forward compatibility: Subproject can update independently if needed

### Why PSubsetPpoly.lean at root?

- Convention: Standard Lean pattern (root exports main definitions)
- Discoverability: User knows where to import from
- Documentation: Natural place for module-level docs

### Why keep Pnp2/ instead of replacing?

- Provenance: Historical record of development
- Reproducibility: Old documentation references still work
- Backward compatibility: Existing imports don't break
- Archive: FCE-based approach preserved for reference

## Comparisons

### Before: Monolithic

```
p-np2/
├── Pnp2/
│   ├── PsubsetPpoly.lean (507KB)
│   ├── TM/...
│   ├── Circuit/...
│   └── ... (all mixed together)
└── pnp3/
    └── ... (references Pnp2.PsubsetPpoly)
```

Issues:
- Can't use P ⊆ P/poly without importing all of Pnp2
- Unclear what's complete vs. conditional
- Hard to review incrementally

### After: Modular

```
p-np2/
├── verified-facts/
│   └── p-subset-ppoly/  (✅ complete, standalone)
├── Pnp2/  (archived)
└── pnp3/  (references verified facts)
```

Benefits:
- Clear separation: complete (verified-facts/) vs. in-progress (pnp3/)
- Reusable: external projects can depend on p-subset-ppoly alone
- Reviewable: reviewers can focus on self-contained modules

## Conclusion

The monorepo structure provides:

✅ **Modularity**: Isolated subprojects with clear boundaries
✅ **Reusability**: External projects can depend on specific facts
✅ **Clarity**: Obvious completion status per component
✅ **Scalability**: Template for adding more verified facts
✅ **Maintainability**: Co-located documentation and code

This design supports the long-term goal of making verified complexity-theoretic results accessible and reusable across the Lean community.

---

**Document Status**: Initial version (2025-10-24)
**Author**: Refactoring by Claude Code
**Last Updated**: 2025-10-24
