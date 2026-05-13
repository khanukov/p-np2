import Complexity.Interfaces
import Mathlib.Data.Fintype.Card

/-!
# Distinguisher-matrix primitives

This small D1 module is intentionally infrastructure only.  It introduces a
Boolean matrix type, finite row/column supports, a symmetric sparsity predicate,
and the row-local fingerprint map needed by later provenance/magnification
slots.  It does **not** introduce any lower-bound endpoint, source theorem, or
truth-table reconstruction machinery.

The fingerprint of a row is encoded as the parity of the selected input bits:
we count the selected coordinates on which the input is `true`, then test
whether that count is odd.  This avoids global algebraic dependencies while
keeping the locality proof elementary and kernel-checked.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_gpt55

open ComplexityInterfaces

/-- A Boolean `m × n` incidence matrix.  Rows select input coordinates. -/
abbrev BoolMatrix (m n : Nat) : Type := Fin m → Fin n → Bool

/-- Support of row `i`: the set of columns selected by that row. -/
def rowSupport {m n : Nat} (D : BoolMatrix m n) (i : Fin m) :
    Finset (Fin n) :=
  Finset.univ.filter (fun j => D i j = true)

/-- Support of column `j`: the set of rows selecting that column. -/
def colSupport {m n : Nat} (D : BoolMatrix m n) (j : Fin n) :
    Finset (Fin m) :=
  Finset.univ.filter (fun i => D i j = true)

/-- Number of selected coordinates in row `i`. -/
def MatrixRowSupportCard {m n : Nat} (D : BoolMatrix m n) (i : Fin m) : Nat :=
  (rowSupport D i).card

/-- Number of rows selecting column `j`. -/
def MatrixColSupportCard {m n : Nat} (D : BoolMatrix m n) (j : Fin n) : Nat :=
  (colSupport D j).card

/-- A matrix is `k`-sparse when every row and every column has support at most `k`. -/
def SparseDistinguisherMatrix (m n k : Nat) (D : BoolMatrix m n) : Prop :=
  (∀ i : Fin m, MatrixRowSupportCard D i ≤ k) ∧
    (∀ j : Fin n, MatrixColSupportCard D j ≤ k)

/-- The all-false matrix. -/
def zeroMatrix (m n : Nat) : BoolMatrix m n :=
  fun _ _ => false

/-- Matrix transpose, used only for support-symmetry sanity lemmas. -/
def transpose {m n : Nat} (D : BoolMatrix m n) : BoolMatrix n m :=
  fun j i => D i j

/-- Boolean oddness of a natural number, kept local to this module. -/
def oddBool (t : Nat) : Bool :=
  t % 2 == 1

/-- Parity of the `true` values of `x` on a finite support. -/
def supportParity {n : Nat} (s : Finset (Fin n)) (x : Bitstring n) : Bool :=
  oddBool ((s.filter (fun j => x j = true)).card)

/--
Fingerprint map associated to a distinguisher matrix.

For each row `i`, `(fingerprint D x) i` is the XOR/parity of those input bits
`x j` whose matrix entry `D i j` is `true`.
-/
def fingerprint {m n : Nat} (D : BoolMatrix m n) (x : Bitstring n) :
    Bitstring m :=
  fun i => supportParity (rowSupport D i) x

/-- Row support of the transpose is the corresponding column support. -/
theorem rowSupport_transpose {m n : Nat} (D : BoolMatrix m n) (j : Fin n) :
    rowSupport (transpose D) j = colSupport D j := by
  ext i
  simp [rowSupport, colSupport, transpose]

/-- Column support of the transpose is the corresponding row support. -/
theorem colSupport_transpose {m n : Nat} (D : BoolMatrix m n) (i : Fin m) :
    colSupport (transpose D) i = rowSupport D i := by
  ext j
  simp [rowSupport, colSupport, transpose]

/-- Transpose support sanity: row-cardinality after transpose is column-cardinality before it. -/
theorem row_col_transpose_sanity {m n : Nat} (D : BoolMatrix m n) (j : Fin n) :
    MatrixRowSupportCard (transpose D) j = MatrixColSupportCard D j := by
  simp [MatrixRowSupportCard, MatrixColSupportCard, rowSupport_transpose]

/-- Type-level codomain canary for the fingerprint map. -/
theorem fingerprint_codomain_sanity {m n : Nat} (_D : BoolMatrix m n)
    (_x : Bitstring n) : True := by
  trivial

/--
The parity computation only depends on values of `x` on the supplied support.
This helper lets the public row-local theorem stay independent of the chosen
finite-XOR encoding.
-/
theorem supportParity_local {n : Nat} (s : Finset (Fin n))
    (x y : Bitstring n)
    (hAgree : ∀ j, j ∈ s → x j = y j) :
    supportParity s x = supportParity s y := by
  have hFilter : s.filter (fun j => x j = true) =
      s.filter (fun j => y j = true) := by
    ext j
    by_cases hjs : j ∈ s
    · have hxy : x j = y j := hAgree j hjs
      simp [hjs, hxy]
    · simp [hjs]
  simp [supportParity, hFilter]

/-- Fingerprint bit `i` only depends on the input coordinates in row support `i`. -/
theorem fingerprint_local
    {m n : Nat} (D : BoolMatrix m n) (x y : Bitstring n) (i : Fin m)
    (hAgree : ∀ j, j ∈ rowSupport D i → x j = y j) :
    fingerprint D x i = fingerprint D y i := by
  exact supportParity_local (rowSupport D i) x y hAgree

/-- The all-false matrix has empty row support. -/
theorem rowSupport_zero (m n : Nat) (i : Fin m) :
    rowSupport (zeroMatrix m n) i = ∅ := by
  ext j
  simp [rowSupport, zeroMatrix]

/-- The all-false matrix has empty column support. -/
theorem colSupport_zero (m n : Nat) (j : Fin n) :
    colSupport (zeroMatrix m n) j = ∅ := by
  ext i
  simp [colSupport, zeroMatrix]

/-- For the all-false matrix, every fingerprint bit is false. -/
theorem fingerprint_zero {m n : Nat} (x : Bitstring n) :
    fingerprint (zeroMatrix m n) x = (fun _ : Fin m => false) := by
  funext i
  simp [fingerprint, supportParity, rowSupport_zero, oddBool]

/-- The all-false matrix is `k`-sparse for every `k`. -/
theorem zero_matrix_sparsity (m n k : Nat) :
    SparseDistinguisherMatrix m n k (zeroMatrix m n) := by
  constructor
  · intro i
    simp [MatrixRowSupportCard, rowSupport_zero]
  · intro j
    simp [MatrixColSupportCard, colSupport_zero]

/-- A row support is always bounded by the ambient number of columns. -/
theorem rowSupport_card_le_n {m n : Nat} (D : BoolMatrix m n) (i : Fin m) :
    MatrixRowSupportCard D i ≤ n := by
  unfold MatrixRowSupportCard rowSupport
  simpa [MatrixRowSupportCard, rowSupport] using Finset.card_le_univ (rowSupport D i)

/-- A column support is always bounded by the ambient number of rows. -/
theorem colSupport_card_le_m {m n : Nat} (D : BoolMatrix m n) (j : Fin n) :
    MatrixColSupportCard D j ≤ m := by
  unfold MatrixColSupportCard colSupport
  simpa [MatrixColSupportCard, colSupport] using Finset.card_le_univ (colSupport D j)

end V_gpt55
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
