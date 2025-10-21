# Development Guide for p-np2

## Quick Start

### First-time Setup

```bash
# Clone the repository
git clone <repository-url>
cd p-np2

# Run setup script (installs Lean toolchain and downloads cache)
./setup.sh
```

### Building and Testing

```bash
# Build the entire project
lake build

# Run tests
lake test
# or use the convenience script:
./test.sh

# Run full project check (build + smoke tests)
./scripts/check.sh
```

## Project Structure

### PNP3 - Main Development (Current Focus)

- **Core/** - Core definitions and SAL pipeline
  - `BooleanBasics.lean` - Basic boolean function definitions
  - `PDT.lean` - Partial Decision Trees (complete ✅)
  - `PDTPartial.lean` - Partial PDT with trunks and tails (complete ✅)
  - `Atlas.lean` - Atlas structure and WorksFor predicate (complete ✅)
  - `SAL_Core.lean` - Switching-Atlas Lemma core (complete ✅)
  - `ShrinkageWitness.lean` - Shrinkage certificate structures (complete ✅)

- **Counting/** - Counting and capacity bounds
  - `BinomialBounds.lean` - Combinatorial bounds (complete ✅)
  - `Count_EasyFuncs.lean` - Counting easy functions (complete ✅)
  - `Atlas_to_LB_Core.lean` - Main counting theorems (complete ✅)

- **ThirdPartyFacts/** - External lemmas and axioms
  - `Facts_Switching.lean` - Multi-switching lemma interface (with axiom)
  - `LeafBudget.lean` - Leaf budget bounds
  - `HastadMSL.lean` - Håstad multi-switching lemma

- **Tests/** - Test files
  - `Parity_Counterexample.lean` - Parity impossibility proof (✅)
  - `SAL_Smoke_AC0.lean` - Smoke tests for AC⁰ (✅)
  - `Atlas_Count_Sanity.lean` - Counting sanity checks (✅)

### PNP2 - Legacy Code

- `ComplexityClasses/` - Complexity class definitions
- `NP_separation/` - Earlier separation attempts

## Current Status

### Step A: SAL Core (~98% complete)
- ✅ All core structures implemented
- ✅ All key theorems proven
- ✅ SAL pipeline working
- ⚠️ Minor TODO: Implement `PDT.WellFormed` (low priority)

### Step B: Counting and Capacity (100% complete ✅)
- ✅ All definitions in place
- ✅ All bounds proven
- ✅ Main theorem `covering_power_bound` proven
- ✅ Incompatibility criteria proven
- ✅ All tests passing

## Development Workflow

### Adding New Theorems

1. Add theorem statement to appropriate file in `pnp3/`
2. Build to check syntax: `lake build`
3. Fill in proof
4. Add tests in `pnp3/Tests/`
5. Run full check: `./scripts/check.sh`

### Working with Axioms

The project uses one external axiom:
- `partial_shrinkage_for_AC0` in `Facts_Switching.lean` - Multi-switching lemma from external literature

For special cases, constructive versions are provided:
- `partial_shrinkage_for_AC0_of_constant` - For constant functions
- `partial_shrinkage_for_AC0_of_pointBound` - For small cubes

### Running Specific Tests

```bash
# Build and check specific file
lake env lean pnp3/Tests/SAL_Smoke_AC0.lean

# Run smoke test script
lake env lean --run scripts/smoke.lean
```

## Key Theorems

### From SAL_Core.lean
- `SAL_from_Shrinkage` - Main SAL theorem: Shrinkage → Working Atlas

### From Atlas_to_LB_Core.lean
- `covering_power_bound` - Covering power capacity bound
- `incompatibility` - Incompatibility criterion for large families
- `unionClass_card_bound` - Union class size bound
- `hammingBall_card_bound` - Hamming ball size bound

### From BinomialBounds.lean
- `unionBound_le_pow_mul` - Union bound: ≤ (k+1) * (max 1 D)^k
- `capacityBound_le_pow_mul` - Combined capacity bound

## Troubleshooting

### Cache Download Fails
If `lake exe cache get` fails, you can still build from scratch:
```bash
lake build
# This will take longer but will work
```

### Lean Version Mismatch
Make sure you're using the correct Lean version:
```bash
elan show  # Should show leanprover/lean4:v4.22.0-rc2
./setup.sh  # Re-run setup if needed
```

### Build Errors
```bash
# Clean build
lake clean
lake build
```

## Contributing

1. Work on the `khanukov/refactor-pdt.refine-to-improve-tails-handling` branch
2. Make changes and test thoroughly
3. Commit with descriptive messages
4. Push to the branch (NOT to main!)

## Documentation

- Full proof plan: `pnp3/Docs/PLAN.md`
- Legacy task description: `Task_description.md`
- Project overview: `README.md`
