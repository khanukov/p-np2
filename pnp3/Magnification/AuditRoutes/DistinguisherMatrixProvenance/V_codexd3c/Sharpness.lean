import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3a.AntiCollapsePrime
import Mathlib.Tactic

/-!
# D3′-C: full-window sharpness for the D3′-A budget

D3′-A proves that a sparse fingerprint matrix cannot separate the payload-anchor
YES/far-NO relation when its total row budget leaves enough payload coordinates
unqueried.  This file records the matching sharpness sanity check: if the matrix
is allowed one row for every payload coordinate, it can simply read the whole
payload window and separate the same relation at radius `1`.

Progress classification: side-track audit formalization.  This is a
budget-sensitivity theorem for the D3′ matrix route.  It does not introduce a
source theorem, a provenance-filter promotion, a `PpolyDAG` bridge, or a
`P ≠ NP` endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_codexd3c

open ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
open V_gpt55
open V_codexd3a

/--
The full-window payload identity matrix.

There is one row for each logarithmic payload coordinate.  Row `i` selects
exactly the embedded ambient coordinate `payloadEmbed n i` and ignores every
other input coordinate.
-/
def payloadIdentityMatrix (n : Nat) : BoolMatrix (widthFn n) n :=
  fun i j => decide (j = payloadEmbed n i)

/-- Row `i` of the payload identity matrix has singleton support. -/
theorem rowSupport_payloadIdentityMatrix (n : Nat) (i : Fin (widthFn n)) :
    rowSupport (payloadIdentityMatrix n) i = {payloadEmbed n i} := by
  ext j
  simp [rowSupport, payloadIdentityMatrix]

/-- Every row of the payload identity matrix reads exactly one coordinate. -/
theorem payloadIdentityMatrix_row_card (n : Nat) (i : Fin (widthFn n)) :
    MatrixRowSupportCard (payloadIdentityMatrix n) i = 1 := by
  simp [MatrixRowSupportCard, rowSupport_payloadIdentityMatrix]

/-- Every column of the payload identity matrix is queried by at most one row. -/
theorem payloadIdentityMatrix_col_card_le_one (n : Nat) (j : Fin n) :
    MatrixColSupportCard (payloadIdentityMatrix n) j ≤ 1 := by
  rw [MatrixColSupportCard]
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  have ha' : j = payloadEmbed n a := by
    simpa [colSupport, payloadIdentityMatrix] using ha
  have hb' : j = payloadEmbed n b := by
    simpa [colSupport, payloadIdentityMatrix] using hb
  exact payloadEmbed_injective n (ha'.symm.trans hb')

/-- The full-window identity is sparse with row and column sparsity `1`. -/
theorem payloadIdentityMatrix_sparse (n : Nat) :
    SparseDistinguisherMatrix (widthFn n) n 1 (payloadIdentityMatrix n) := by
  constructor
  · intro i
    simp [payloadIdentityMatrix_row_card]
  · intro j
    exact payloadIdentityMatrix_col_card_le_one n j

/-- Parity over a singleton support returns the selected bit. -/
theorem supportParity_singleton {n : Nat} (j : Fin n) (x : Bitstring n) :
    supportParity ({j} : Finset (Fin n)) x = x j := by
  by_cases hx : x j = true
  · have hFilter : ({j} : Finset (Fin n)).filter (fun k => x k = true) = {j} := by
      ext k
      constructor
      · intro hk
        exact (Finset.mem_filter.mp hk).1
      · intro hk
        have hkj : k = j := by simpa using hk
        subst k
        simp [hx]
    simp [supportParity, oddBool, hFilter, hx]
  · have hxFalse : x j = false := by
      cases hBit : x j <;> simp [hBit] at hx ⊢
    have hFilter : ({j} : Finset (Fin n)).filter (fun k => x k = true) = ∅ := by
      ext k
      constructor
      · intro hk
        have hkj : k = j := by simpa using (Finset.mem_filter.mp hk).1
        have hkTrue : x k = true := (Finset.mem_filter.mp hk).2
        subst k
        simp [hxFalse] at hkTrue
      · intro hk
        simp at hk
    simp [supportParity, oddBool, hFilter, hxFalse]

/-- The payload identity fingerprint is literally the payload-window projection. -/
theorem fingerprint_payloadIdentity_apply (n : Nat) (x : Bitstring n)
    (i : Fin (widthFn n)) :
    fingerprint (payloadIdentityMatrix n) x i = x (payloadEmbed n i) := by
  simp [fingerprint, rowSupport_payloadIdentityMatrix, supportParity_singleton]

/--
Two strings have the same full-window identity fingerprint iff they agree on all
embedded payload coordinates.
-/
theorem fingerprint_payloadIdentity_eq_on_payload (n : Nat) (x y : Bitstring n) :
    fingerprint (payloadIdentityMatrix n) x = fingerprint (payloadIdentityMatrix n) y ↔
      ∀ j : Fin n, j ∈ payloadCoords n → x j = y j := by
  constructor
  · intro h j hj
    rcases Finset.mem_image.mp hj with ⟨i, _hi, rfl⟩
    simpa [fingerprint_payloadIdentity_apply] using congrFun h i
  · intro h
    funext i
    simp [fingerprint_payloadIdentity_apply, h (payloadEmbed n i) (by simp [payloadCoords])]

/--
A payload-window disagreement with the anchor creates a fingerprint disagreement
in the corresponding payload-identity row.
-/
theorem exists_fingerprint_disagreement_of_payloadDistance_pos
    {n : Nat} {y : Bitstring n}
    (hyDist : 1 ≤ payloadWindowDistance n y (payloadAnchor n)) :
    ∃ i : Fin (widthFn n),
      fingerprint (payloadIdentityMatrix n) (payloadAnchor n) i ≠
        fingerprint (payloadIdentityMatrix n) y i := by
  have hNonempty : ((payloadCoords n).filter
      (fun j => y j ≠ payloadAnchor n j)).Nonempty := by
    exact Finset.card_pos.mp hyDist
  rcases hNonempty with ⟨j, hjFilter⟩
  have hjPayload : j ∈ payloadCoords n := (Finset.mem_filter.mp hjFilter).1
  have hjDiff : y j ≠ payloadAnchor n j := (Finset.mem_filter.mp hjFilter).2
  rcases Finset.mem_image.mp hjPayload with ⟨i, _hi, rfl⟩
  refine ⟨i, ?_⟩
  simp [fingerprint_payloadIdentity_apply, hjDiff.symm]

/--
The full-window payload identity matrix separates the D3′-A payload-anchor
YES/far-NO relation at radius `1`.

This does **not** refute D3′-A: the D3′-A theorem assumes a budget inequality
that leaves payload coordinates unqueried, while this matrix intentionally uses
one row for every payload coordinate and reads the whole payload window.
-/
theorem payloadIdentity_separates_payloadYes_farNo
    (n ρ : Nat)
    (hρ : 1 ≤ ρ) :
    FingerprintSeparation
      (payloadIdentityMatrix n)
      (payloadYesSet n)
      (payloadFarNoSet n ρ)
      1 := by
  intro x hx y hy
  simp [payloadYesSet] at hx
  subst x
  simp [payloadFarNoSet] at hy
  have hyDistPos : 1 ≤ payloadWindowDistance n y (payloadAnchor n) := by
    omega
  rcases exists_fingerprint_disagreement_of_payloadDistance_pos
      (n := n) (y := y) hyDistPos with ⟨i, hiDiff⟩
  unfold hammingDistance
  exact Finset.card_pos.mpr ⟨i, by simp [hiDiff]⟩

end V_codexd3c
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
