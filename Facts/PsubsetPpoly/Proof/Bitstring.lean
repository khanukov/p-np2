import Mathlib.Data.Fin.Basic

/-!
# Bitstring primitives for the `P ⊆ P/poly` proof

This module records the minimal interface on Boolean vectors that the
construction of the `P ⊆ P/poly` inclusion relies upon.  The proof only needs
an explicit name for bitstrings of a fixed length, and the ability to view them
as points of the Boolean cube.  All heavier combinatorics has been excised so
that the standalone fact exposes a tiny self-contained API.
-/

namespace Boolcube

/-- A point of the `n`-dimensional Boolean cube. -/
abbrev Point (n : ℕ) := Fin n → Bool

/-- Synonym emphasising the "language theoretic" interpretation of points. -/
abbrev Bitstring (n : ℕ) := Point n

end Boolcube
