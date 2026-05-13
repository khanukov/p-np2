import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives
import Magnification.AuditRoutes.ArbitraryLogWidthTT.Family
import Mathlib.Tactic

/-!
# D3 anti-collapse audit for log-width payloads

This module records the D3 audit lesson for the sparse-distinguisher-matrix
route.  The all-essential log-width truth-table payload construction supplies a
strong syntactic support statement, but that statement alone does not supply the
semantic data required by fingerprint separation: one still needs an explicit
YES/far-NO relation and a matrix whose fingerprints separate it.

The theorem below is intentionally modest and local.  It shows that even while
an arbitrary all-essential payload has the exact renamed support cardinality
from `ArbitraryLogWidthTT`, a bare cardinality/all-essentialness assumption is
compatible with a toy audit relation for which every matrix fails positive
fingerprint separation.  Thus the matrix witness is a real extra obligation,
not a consequence of the payload support theorem.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_gpt55

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT

/-- Hamming distance on fixed-length Boolean fingerprints. -/
def hammingDistance {m : Nat} (a b : Bitstring m) : Nat :=
  (Finset.univ.filter (fun i => a i != b i)).card

/-- Any Boolean string has Hamming distance zero from itself. -/
theorem hammingDistance_self {m : Nat} (a : Bitstring m) :
    hammingDistance a a = 0 := by
  simp [hammingDistance]

/--
Positive-radius fingerprint separation between two finite sets of ambient
inputs.  The matrix is a parameter rather than hidden in the predicate: the
whole point of this audit route is that a separating matrix must be supplied
explicitly.
-/
def FingerprintSeparation {m n : Nat}
    (D : BoolMatrix m n)
    (yesSet noSet : Finset (Bitstring n))
    (radius : Nat) : Prop :=
  ∀ x, x ∈ yesSet → ∀ y, y ∈ noSet →
    radius ≤ hammingDistance (fingerprint D x) (fingerprint D y)

/--
No matrix can positively separate a point from itself.  This is the elementary
anti-collapse kernel: support/cardinality information does not even define a
separable audit relation; if the relation overlaps, every fingerprint map sends
the shared point to the same fingerprint on both sides.
-/
theorem no_self_fingerprintSeparation
    {m n : Nat} (D : BoolMatrix m n) (x : Bitstring n) (r : Nat) :
    ¬ FingerprintSeparation D ({x} : Finset (Bitstring n)) ({x}) (r + 1) := by
  intro hsep
  have hpos : r + 1 ≤ hammingDistance (fingerprint D x) (fingerprint D x) :=
    hsep x (by simp) x (by simp)
  rw [hammingDistance_self] at hpos
  exact Nat.not_succ_le_zero r hpos

/--
Consequently, adding sparsity side conditions to the matrix does not help: no
sparse matrix witness exists for the overlapping singleton toy relation at any
positive radius.
-/
theorem no_sparse_matrix_separates_overlapping_singletons
    {m n k : Nat} (x : Bitstring n) (r : Nat) :
    ¬ ∃ D : BoolMatrix m n,
      SparseDistinguisherMatrix m n k D ∧
        FingerprintSeparation D ({x} : Finset (Bitstring n)) ({x}) (r + 1) := by
  rintro ⟨D, _hSparse, hsep⟩
  exact no_self_fingerprintSeparation D x r hsep

/--
D3 anti-collapse theorem.

For every arbitrary all-essential log-width payload family, the renamed formula
family has exactly the advertised logarithmic support cardinality.  Nevertheless,
that support-cardinality/all-essentialness statement alone does not yield a
positive-radius fingerprint-separation contract: for the toy overlapping
YES/NO singleton relation, there is no sparse matrix witness at all.

This is the intended quantifier discipline for D3.  The result does **not** say
that every payload defeats every possible matrix relation.  It says that the
payload support theorem by itself is too weak to derive fingerprint separation;
an explicit, non-overlapping semantic relation together with a matrix witness is
additional data.
-/
theorem allEssentialLogWidthPayload_no_fingerprintSeparation
    (F : PayloadFamily)
    (hF : AllEssentialPayload F)
    (n : Nat) :
    (FormulaCircuit.support (adversaryFamily_v_arbpayload F n)).card = widthFn n ∧
      ∀ (m k r : Nat) (x : Bitstring n),
        ¬ ∃ D : BoolMatrix m n,
          SparseDistinguisherMatrix m n k D ∧
            FingerprintSeparation D ({x} : Finset (Bitstring n)) ({x}) (r + 1) := by
  constructor
  · exact adversaryFamily_v_arbpayload_support_card F hF n
  · intro m k r x
    exact no_sparse_matrix_separates_overlapping_singletons (m := m) (n := n) (k := k) x r

end V_gpt55
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
