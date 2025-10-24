import PSubsetPpoly.ComplexityClasses

/-!
# P ⊆ P/poly: Verified Proof

This module provides a complete, formally verified proof that every polynomial-time
decidable language admits a family of polynomial-size circuits (P ⊆ P/poly).

## Main Result

`P_subset_Ppoly : P ⊆ Ppoly`

Proved constructively by simulating Turing machines with straight-line circuits.

## Structure

- `TM.Encoding` - Single-tape Turing machine model
- `Circuit.StraightLine` - Straight-line circuit representation
- `Circuit.Family` - Circuit families
- `Core` - Main simulation proof (TM → circuits)
- `ComplexityClasses` - Complexity class definitions and main theorem

## Dependencies

- Lean 4.22.0-rc2
- mathlib4

## Status

✅ Fully proven - no axioms, no sorry statements
-/

/-!
## Main Export

The key theorem is accessible via:
```lean
import PSubsetPpoly
open ComplexityClasses

#check P_subset_Ppoly -- P ⊆ Ppoly
```
-/
