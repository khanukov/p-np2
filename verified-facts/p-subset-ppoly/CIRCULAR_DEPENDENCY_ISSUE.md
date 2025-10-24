# Circular Dependency Issue in P ⊆ P/poly Subproject

## Status: BLOCKED

The P ⊆ P/poly standalone subproject extraction is currently blocked by a circular dependency that exists in the original Pnp2 codebase.

## Progress Completed

✅ All Pnp2 files copied to verified-facts/p-subset-ppoly/PSubsetPpoly/
✅ All imports updated from `Pnp2.*` to `PSubsetPpoly.*`
✅ Lakefile configured with correct Lean toolchain (4.22.0-rc2) and mathlib version
✅ Root PSubsetPpoly.lean file configured to export the main theorem

## Current Blocker: Circular Import Dependency

### The Problem

Two files import each other, creating a build cycle:

```
PSubsetPpoly/PsubsetPpoly.lean:
  import PSubsetPpoly.ComplexityClasses  ← imports ComplexityClasses

PSubsetPpoly/ComplexityClasses.lean:
  import PSubsetPpoly.PsubsetPpoly  ← imports PsubsetPpoly
```

Lake build error:
```
error: build cycle detected:
  +PSubsetPpoly.PsubsetPpoly:leanArts
  +PSubsetPpoly.PsubsetPpoly:olean
  +PSubsetPpoly.ComplexityClasses:setup
  +PSubsetPpoly.ComplexityClasses:leanArts
  +PSubsetPpoly.ComplexityClasses:olean
  +PSubsetPpoly.PsubsetPpoly:setup
```

### Why the Dependency Exists

**PsubsetPpoly.lean needs ComplexityClasses.lean for:**
- `Complexity.Language` type definition
- `Complexity.InPpoly` structure definition
- `Boolcube.Bitstring` type alias

**ComplexityClasses.lean needs PsubsetPpoly.lean for:**
- `Complexity.inPpoly_of_polyBound` function (used in the P_subset_Ppoly theorem)

### Note on Original Pnp2

This same circular dependency exists in the original Pnp2 codebase:
- `Pnp2/PsubsetPpoly.lean` imports `Pnp2.ComplexityClasses`
- `Pnp2/ComplexityClasses.lean` imports `Pnp2.PsubsetPpoly`

The Pnp2 library in lakefile.lean uses `globs` to specify only certain modules, which may explain why this hasn't been an issue before, but attempting to build the full library reveals the circular dependency.

## Potential Solutions

### Option 1: Forward Declarations (Preferred)

Break the cycle by adding forward declarations to PsubsetPpoly.lean:

```lean
-- Forward declarations to avoid circular dependency
namespace Complexity

abbrev Bitstring (n : ℕ) := Fin n → Bool
abbrev Language := ∀ n, Bitstring n → Bool

structure InPpoly (L : Language) where
  polyBound : ℕ → ℕ
  polyBound_poly : ∃ k, ∀ n, polyBound n ≤ n^k + k
  circuits : ∀ n, StraightLineCircuit n
  size_ok : ∀ n, (circuits n).gates ≤ polyBound n
  correct : ∀ n (x : Bitstring n),
    StraightLineCircuit.eval (circuits n) x = L n x

end Complexity
```

Then remove `import PSubsetPpoly.ComplexityClasses` from PsubsetPpoly.lean.

**Pros:** Clean solution, maintains standalone nature
**Cons:** Duplicates type definitions (must match exactly)

### Option 2: Refactor into Three Modules

Create a new module `PSubsetPpoly/Types.lean` with type definitions:

```
Types.lean:
  - Contains Language, Bitstring, InPpoly definitions

PsubsetPpoly.lean:
  - imports Types
  - Contains simulation infrastructure

ComplexityClasses.lean:
  - imports Types
  - imports PsubsetPpoly
  - Contains P, NP, P/poly definitions and P_subset_Ppoly theorem
```

**Pros:** Cleanest architecture, no duplication
**Cons:** Requires more extensive refactoring

### Option 3: Inline ComplexityClasses into Psubsetpoly

Merge ComplexityClasses.lean content into PsubsetPpoly.lean so there's only one file.

**Pros:** Simple, no circular dependency
**Cons:** Creates a very large file, loses modularity

## Recommended Next Steps

1. Implement Option 1 (Forward Declarations) as it requires minimal changes
2. Test that the subproject builds successfully
3. Update pnp3/Complexity/Interfaces.lean to import from PSubsetPpoly
4. Verify pnp3 builds with the new import
5. Document the axiom removal in pnp3/Docs/AXIOMS.md

## Files Modified

- verified-facts/p-subset-ppoly/PSubsetPpoly/* (all files copied and imports updated)
- verified-facts/p-subset-ppoly/lean-toolchain (set to v4.22.0-rc2)
- verified-facts/p-subset-ppoly/lakefile.lean (mathlib version set)
- verified-facts/p-subset-ppoly/PSubsetPpoly.lean (root export file)

## Build Command

Once circular dependency is resolved:
```bash
cd /home/user/p-np2
export PATH="$HOME/.elan/bin:$PATH"
lake build PSubsetPpoly
```

