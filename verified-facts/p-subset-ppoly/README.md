# P ⊆ P/poly: Verified Proof

**Status**: ✅ Complete, formally verified in Lean 4

This standalone module provides a complete, machine-checked proof that every polynomial-time decidable language admits a family of polynomial-size circuits (P ⊆ P/poly).

## Main Theorem

```lean
theorem P_subset_Ppoly : P ⊆ Ppoly
```

**Proof method**: Constructive simulation of single-tape Turing machines by straight-line Boolean circuits.

## Key Components

### 1. Turing Machine Model (`TM/Encoding.lean`)
- Single-tape deterministic Turing machine
- Step-by-step configuration transitions
- Runtime bounds and tape length tracking

### 2. Circuit Models
- **`Circuit/StraightLine.lean`**: DAG-based straight-line circuits with wire reuse
- **`Circuit/Family.lean`**: Circuit families indexed by input length
- **`Circuit/Builder`**: Incremental circuit construction with gate count tracking

### 3. Main Simulation (`Core.lean`)
- Layer-by-layer TM→circuit transformation
- Each TM step becomes a polynomial-size circuit layer
- Proof of correctness and polynomial size bound
- **Key insight**: Locality of transitions ensures constant gates per step

### 4. Complexity Classes (`ComplexityClasses.lean`)
- Definitions of P, NP, and P/poly
- Main theorem export

## Building

```bash
# From this directory
lake exe cache get  # Download mathlib cache
lake build          # Build the proof

# To verify the main theorem
lean --run PSubsetPpoly.lean
```

## Dependencies

- **Lean 4**: Version 4.22.0-rc2 (see `lean-toolchain`)
- **mathlib4**: Standard library for formalized mathematics

## Proof Structure

1. **Configuration encoding** (TM.Encoding): Represents TM state as Boolean values
2. **Initial circuit** (Core): Encodes starting configuration
3. **Step simulation** (Core): Each TM transition → circuit layer
   - Read symbol under head
   - Branch on (state, symbol) pair
   - Update: write bit, move head, change state
4. **Iteration** (Core): Compose T(n) step circuits for T(n)-time TM
5. **Size bound** (Core): Total gates ≤ poly(n) × T(n) = poly(n)
6. **Final theorem** (ComplexityClasses): P ⊆ P/poly

## Status

- ✅ **No axioms**: All results proven from first principles
- ✅ **No sorry statements**: Complete proof
- ✅ **Type-checked**: Verified by Lean 4 compiler

## Size of Proof

- **Total code**: ~550KB Lean source
- **Main file**: Core.lean (507KB) - detailed simulation proof
- **Supporting code**: ~40KB (TM model, circuit infrastructure)

## References

This result is classical (folklore since 1970s), appearing in standard texts:
- Arora & Barak, *Computational Complexity: A Modern Approach*, Theorem 6.11
- Sipser, *Introduction to the Theory of Computation*, Section 9.3

The novelty here is the **complete formal verification** in a proof assistant.

## License

Same as parent p-np2 repository.

## Usage in Other Projects

To use this verified fact in your own Lean project:

```lean
-- In your lakefile.lean
require psubsetppoly from git
  "https://github.com/khanukov/p-np2.git" @ "main" / "verified-facts/p-subset-ppoly"

-- In your Lean code
import PSubsetPpoly

example : P ⊆ Ppoly := P_subset_Ppoly
```
