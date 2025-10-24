# Important Constraints for P ⊆ P/poly Subproject

## ❌ CANNOT USE Pnp2 DIRECTLY

**CRITICAL**: There is NO option to use Pnp2 code directly in this subproject or import from Pnp2.

This standalone subproject exists specifically because:
- Pnp2 code cannot be used as-is
- We need an isolated, verified version of the P ⊆ P/poly proof
- Direct imports from Pnp2 are not viable for architectural reasons

## Current Status

The copied Pnp2 code has compatibility issues with Lean 4.22.0-rc2:

### Build Errors Found:
1. **Utils/Nat.lean** - API changes in arithmetic operations
2. **PSubsetPpoly/TM/Encoding.lean** - Missing `noncomputable` markers, documentation syntax errors
3. **PSubsetPpoly/canonical_circuit.lean** - Multiple unsolved goals, type mismatches, API incompatibilities

### Next Steps Required:
- Fix all compatibility issues with Lean 4.22.0-rc2
- Update proofs to work with current Mathlib API
- Ensure standalone subproject builds successfully
- DO NOT attempt to revert to using Pnp2 directly

---

**Date**: 2025-10-24
**Session**: claude/refactor-verified-facts-011CUSG9L9hCKhTDLgUSk2dp
