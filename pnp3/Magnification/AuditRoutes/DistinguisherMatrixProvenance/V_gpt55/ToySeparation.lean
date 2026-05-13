import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives
import Mathlib.Tactic

/-!
# Toy sparse fingerprint separation

This D2 module is a deliberately tiny, fully explicit smoke theorem for the D1
matrix primitives.  It stays on the audit-route side: the theorem below only
shows that one hand-written sparse Boolean matrix separates one hand-written
YES fingerprint from one hand-written NO fingerprint.  It introduces no source
theorem, no gap object, and no P-vs-NP endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_gpt55

open ComplexityInterfaces

/-- Hamming distance between two same-length bitstrings. -/
def toyFingerprintDistance {m : Nat} (u v : Bitstring m) : Nat :=
  (Finset.univ.filter (fun i : Fin m => u i ≠ v i)).card

/--
Local D2 separation predicate used because D1 intentionally did not yet define
an official `FingerprintSeparation` surface.
-/
def ToyFingerprintSeparation {m n : Nat} (D : BoolMatrix m n)
    (YES NO : Finset (Bitstring n)) (r : Nat) : Prop :=
  ∀ y, y ∈ YES → ∀ z, z ∈ NO → r ≤ toyFingerprintDistance (fingerprint D y) (fingerprint D z)

/--
A `2 × 4` matrix with two singleton rows: row `0` reads input bit `0`, and row
`1` reads input bit `1`.  Thus every row and every column has support at most
one, well below the slot budget `k ≤ 2`.
-/
def toyMatrix : BoolMatrix 2 4 :=
  fun i j =>
    match (i : Nat), (j : Nat) with
    | 0, 0 => true
    | 1, 1 => true
    | _, _ => false

/-- The sole YES point: the all-false four-bit string. -/
def toyYESPoint : Bitstring 4 :=
  fun _ => false

/-- The sole NO point: only the first coordinate is true. -/
def toyNOPoint : Bitstring 4 :=
  fun j => if j = (0 : Fin 4) then true else false

/-- Explicit singleton YES set for the toy instance. -/
def toyYES : Finset (Bitstring 4) :=
  {toyYESPoint}

/-- Explicit singleton NO set for the toy instance. -/
def toyNO : Finset (Bitstring 4) :=
  {toyNOPoint}

/-- The toy matrix is sparse with budget `k = 2`. -/
theorem toyMatrix_sparse : SparseDistinguisherMatrix 2 4 2 toyMatrix := by
  constructor
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases j <;> decide

/-- The two explicit points have fingerprints at Hamming distance exactly one. -/
theorem toy_fingerprint_distance_eq_one :
    toyFingerprintDistance (fingerprint toyMatrix toyYESPoint)
      (fingerprint toyMatrix toyNOPoint) = 1 := by
  decide

/--
Toy sparse fingerprint separation theorem for the D2 slot.

The statement is intentionally local and finite: the explicit sparse matrix
separates the singleton YES set `{0000}` from the singleton NO set `{1000}` at
radius `1` after applying the D1 parity fingerprint map.
-/
theorem toy_fingerprint_separation :
    ToyFingerprintSeparation toyMatrix toyYES toyNO 1 := by
  intro y hy z hz
  simp [toyYES, toyNO] at hy hz
  rw [hy, hz, toy_fingerprint_distance_eq_one]

end V_gpt55
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
