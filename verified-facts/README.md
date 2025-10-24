# Verified Facts: Modular Subprojects

This directory contains **isolated, formally verified mathematical facts** extracted as standalone Lean 4 subprojects. Each subproject is:

- ✅ **Self-contained**: Can be built independently
- ✅ **Fully proven**: No axioms, no sorry statements
- ✅ **Reusable**: Can be imported by other Lean projects
- ✅ **Well-documented**: Includes README and proof structure

## Available Subprojects

### 1. P ⊆ P/poly (`p-subset-ppoly/`)

**Theorem**: Every polynomial-time decidable language has polynomial-size circuits.

**Status**: ✅ Complete, ~550KB of verified Lean code

**Main result**:
```lean
theorem P_subset_Ppoly : P ⊆ Ppoly
```

**Method**: Constructive simulation of Turing machines by straight-line Boolean circuits.

**Dependencies**: Lean 4.22.0-rc2, mathlib4

[Full documentation](./p-subset-ppoly/README.md)

---

## Monorepo Structure

The p-np2 repository uses a **monorepo approach** with multiple subprojects:

```
p-np2/
├── pnp3/                  # Main PNP3 pipeline (SAL-based approach)
├── Pnp2/                  # Legacy PNP2 (FCE-based approach, archived)
├── verified-facts/        # ← Isolated verified facts
│   ├── p-subset-ppoly/    # P ⊆ P/poly subproject
│   └── [future facts]/    # More to come...
├── lakefile.lean          # Root lakefile (references subprojects)
└── README.md
```

## Philosophy

As the P≠NP formalization grows, we extract **well-defined, reusable components** into separate subprojects. This approach:

1. **Improves modularity**: Each fact can be understood independently
2. **Enables reuse**: Other projects can depend on individual facts
3. **Clarifies structure**: Shows which results are complete vs. conditional
4. **Facilitates review**: Reviewers can focus on one piece at a time

## Using Subprojects in Your Code

### From within p-np2 repository:

```lean
import PSubsetPpoly  -- Access to P ⊆ P/poly

example : P ⊆ Ppoly := P_subset_Ppoly
```

### From external Lean projects:

Add to your `lakefile.lean`:
```lean
require psubsetppoly from git
  "https://github.com/khanukov/p-np2.git" @ "main" / "verified-facts/p-subset-ppoly"
```

## Roadmap: Future Extracted Facts

Candidates for future extraction:

- **Switching Lemma** (if formalized): Håstad's depth reduction for AC⁰
- **Anti-Checker Construction**: Capacity contradiction for GapMCSP
- **Sunflower Lemma**: Combinatorial structure theorem
- **Decision Tree Lower Bounds**: Sensitivity-based bounds

## Building All Subprojects

From the repository root:

```bash
# Build everything (including all subprojects)
lake build

# Build specific subproject
cd verified-facts/p-subset-ppoly
lake build
```

## Contributing

When adding new verified facts:

1. Create a new subdirectory under `verified-facts/`
2. Structure as a standalone Lake project with:
   - `lakefile.lean` (dependencies)
   - `lean-toolchain` (Lean version)
   - `README.md` (documentation)
   - Source files under a named directory
3. Add reference in root `lakefile.lean`
4. Update this README

## License

All subprojects inherit the license of the parent p-np2 repository.
