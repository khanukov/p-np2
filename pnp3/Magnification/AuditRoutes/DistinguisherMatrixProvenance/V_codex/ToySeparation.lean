import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives
import Mathlib.Tactic

/-!
# D2 toy sparse fingerprint separation

This module is intentionally tiny.  It reuses the D1 matrix primitives from
`V_gpt55.MatrixPrimitives` and checks, in the Lean kernel, one explicit finite
example: the `2 × 2` identity-style sparse Boolean matrix separates the all-true
bitstring from the all-false bitstring by its parity fingerprint.

The result is only a toy separation fact.  It does not define or promote a
provenance filter, does not state any magnification theorem, and does not claim
any lower-bound or `P ≠ NP` consequence.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_codex

open ComplexityInterfaces
open V_gpt55

/--
The `2 × 2` identity-style distinguisher matrix.

Row `0` selects coordinate `0`; row `1` selects coordinate `1`; every other
entry is false.  Because both dimensions are exactly two, each row and each
column has support cardinality one.
-/
def D_id : BoolMatrix 2 2 :=
  fun i j =>
    match (i : Nat), (j : Nat) with
    | 0, 0 => true
    | 1, 1 => true
    | _, _ => false

/-- The explicit YES point used by the toy theorem: `11`. -/
def toyYes : Bitstring 2 :=
  fun _ => true

/-- The explicit NO point used by the toy theorem: `00`. -/
def toyNo : Bitstring 2 :=
  fun _ => false

/--
Tiny local D2 separation predicate.

D1 deliberately supplies only matrix/fingerprint primitives, so this module uses
only the minimal predicate needed for one toy example: the two selected points
are separated when their fingerprints are unequal.
-/
def ToySeparated (D : BoolMatrix 2 2) (yes no : Bitstring 2) : Prop :=
  fingerprint D yes ≠ fingerprint D no

/-- The identity-style matrix is sparse with row/column support budget `k = 1`. -/
theorem D_id_sparse : SparseDistinguisherMatrix 2 2 1 D_id := by
  constructor
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases j <;> decide

/-- On the all-true toy YES point, both fingerprint bits are true. -/
theorem fingerprint_D_id_toyYes :
    fingerprint D_id toyYes = toyYes := by
  funext i
  fin_cases i <;> decide

/-- On the all-false toy NO point, both fingerprint bits are false. -/
theorem fingerprint_D_id_toyNo :
    fingerprint D_id toyNo = toyNo := by
  funext i
  fin_cases i <;> decide

/-- Coordinate `0` of the toy YES fingerprint is the selected input bit. -/
theorem fingerprint_D_id_toyYes_zero :
    fingerprint D_id toyYes ⟨0, by decide⟩ = toyYes ⟨0, by decide⟩ := by
  decide

/-- Coordinate `1` of the toy YES fingerprint is the selected input bit. -/
theorem fingerprint_D_id_toyYes_one :
    fingerprint D_id toyYes ⟨1, by decide⟩ = toyYes ⟨1, by decide⟩ := by
  decide

/--
Toy sparse fingerprint separation theorem for slot D2.

The matrix is explicit (`D_id`), the dimensions are fixed (`m = n = 2`), the
sparsity budget is checked separately (`k = 1`), and the separated pair is the
explicit YES/NO pair `11` versus `00`.
-/
theorem toy_fingerprint_separation :
    ToySeparated D_id toyYes toyNo := by
  intro hSame
  have hBit : fingerprint D_id toyYes ⟨0, by decide⟩ =
      fingerprint D_id toyNo ⟨0, by decide⟩ := by
    exact congrFun hSame ⟨0, by decide⟩
  rw [fingerprint_D_id_toyYes, fingerprint_D_id_toyNo] at hBit
  simp [toyYes, toyNo] at hBit

end V_codex
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
