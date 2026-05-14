import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.AntiCollapse
import Mathlib.Tactic

/-!
# D3′-A: non-degenerate anti-collapse for sparse fingerprint matrices

This module is a D3′ replacement for the old overlapping-singleton D3
anti-collapse skeleton.  The relation below is non-degenerate:

* the YES set is the unique all-true payload-window anchor with zero tail;
* the NO set is tail-fixed and Hamming-far from that anchor inside the
  logarithmic payload window; and
* the proof uses the matrix row-support union.  If `m * k + ρ ≤ widthFn n`,
  every `m`-row, `k`-sparse matrix leaves at least `ρ` payload coordinates
  unqueried, so we flip only those coordinates and obtain a far NO point with
  exactly the same fingerprint as the YES anchor.

Progress classification: side-track audit formalization.  This file proves an
anti-collapse fact for a restricted audit route.  It does not introduce a source
theorem, a provenance-filter promotion, a `PpolyDAG` bridge, or a `P ≠ NP`
endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_codexd3a

open ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
open V_gpt55

/-- The all-true bitstring of a fixed length. -/
def allTrueBits (w : Nat) : Bitstring w :=
  fun _ => true

/--
The concrete all-essential payload family used by D3′-A: Boolean AND over the
entire logarithmic payload window.
-/
def andPayloadFamily : PayloadFamily :=
  fun n u => decide (∀ i : Fin (widthFn n), u i = true)

/-- The AND payload accepts the all-true payload-window point. -/
theorem andPayloadFamily_allTrue (n : Nat) :
    andPayloadFamily n (allTrueBits (widthFn n)) = true := by
  simp [andPayloadFamily, allTrueBits]

/--
The AND payload is all-essential: for coordinate `i`, the all-true vector is a
witness, and flipping `i` changes the AND value from true to false.
-/
theorem andPayload_allEssential : AllEssentialPayload andPayloadFamily := by
  intro n i
  refine ⟨allTrueBits (widthFn n), ?_⟩
  simp [andPayloadFamily, allTrueBits]
  exact ⟨i, by simp [flipBit, allTrueBits]⟩

/-- Canonical embedding of a payload-window coordinate into the ambient input. -/
def payloadEmbed (n : Nat) (i : Fin (widthFn n)) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (widthFn_le n)⟩

/-- The embedded logarithmic payload-window coordinates inside `Fin n`. -/
def payloadCoords (n : Nat) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin (widthFn n))).image (payloadEmbed n)

/-- The payload-coordinate embedding is injective. -/
theorem payloadEmbed_injective (n : Nat) : Function.Injective (payloadEmbed n) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin n => x.val) h

/-- The embedded payload window has exactly `widthFn n` coordinates. -/
theorem payloadCoords_card (n : Nat) : (payloadCoords n).card = widthFn n := by
  rw [payloadCoords, Finset.card_image_of_injective _ (payloadEmbed_injective n)]
  simp

/--
The D3′ anchor: payload-window coordinates are true; tail coordinates are false.
-/
def payloadAnchor (n : Nat) : Bitstring n :=
  fun j => decide (j ∈ payloadCoords n)

/-- Payload-window coordinates of the anchor are true. -/
theorem payloadAnchor_payloadCoord (n : Nat) (i : Fin (widthFn n)) :
    payloadAnchor n (payloadEmbed n i) = true := by
  simp [payloadAnchor, payloadCoords]

/-- Tail coordinates of the anchor are false. -/
theorem payloadAnchor_of_not_payload {n : Nat} {j : Fin n}
    (hj : j ∉ payloadCoords n) : payloadAnchor n j = false := by
  simp [payloadAnchor, hj]

/-- Hamming distance restricted to the embedded payload window. -/
def payloadWindowDistance (n : Nat) (x y : Bitstring n) : Nat :=
  ((payloadCoords n).filter (fun j => x j ≠ y j)).card

/-- The non-degenerate YES set: the singleton containing only the payload anchor. -/
def payloadYesSet (n : Nat) : Finset (Bitstring n) :=
  {payloadAnchor n}

/-- Tail-fixed strings are those that agree with the anchor off the payload window. -/
def tailFixedToAnchor (n : Nat) (y : Bitstring n) : Prop :=
  ∀ j : Fin n, j ∉ payloadCoords n → y j = payloadAnchor n j

/--
The D3′ far-NO set: tail-fixed points at payload-window distance at least `ρ`
from the all-true payload anchor.
-/
noncomputable def payloadFarNoSet (n ρ : Nat) : Finset (Bitstring n) := by
  classical
  exact Finset.univ.filter (fun y => tailFixedToAnchor n y ∧ ρ ≤ payloadWindowDistance n y (payloadAnchor n))

/-- YES and far-NO are disjoint as soon as the requested payload distance is positive. -/
theorem payloadYes_farNo_disjoint {n ρ : Nat} (hρ : 1 ≤ ρ) :
    Disjoint (payloadYesSet n) (payloadFarNoSet n ρ) := by
  rw [Finset.disjoint_left]
  intro x hx hno
  simp [payloadYesSet] at hx
  subst x
  simp [payloadFarNoSet, payloadWindowDistance] at hno
  omega

/-- Union of all coordinates queried by any row of a Boolean matrix. -/
def queryUnion {m n : Nat} (D : BoolMatrix m n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin m)).biUnion (fun i => rowSupport D i)

/-- A row support is contained in the query union. -/
theorem rowSupport_subset_queryUnion {m n : Nat} (D : BoolMatrix m n) (i : Fin m) :
    rowSupport D i ⊆ queryUnion D := by
  intro j hj
  exact Finset.mem_biUnion.mpr ⟨i, by simp, hj⟩

/-- Sparse matrices query at most `m * k` coordinates in total. -/
theorem queryUnion_card_le_mul {m n k : Nat} (D : BoolMatrix m n)
    (hSparse : SparseDistinguisherMatrix m n k D) :
    (queryUnion D).card ≤ m * k := by
  unfold queryUnion
  simpa using
    (Finset.card_biUnion_le_card_mul (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => rowSupport D i) (n := k) (by
        intro i _hi
        exact hSparse.1 i))

/-- Coordinates available for the adversarial far-NO flip: payload coordinates not queried by `D`. -/
def unqueriedPayloadCoords {m n : Nat} (D : BoolMatrix m n) : Finset (Fin n) :=
  payloadCoords n \ queryUnion D

/-- At least `ρ` payload coordinates remain unqueried under the D3′-A budget inequality. -/
theorem unqueriedPayloadCoords_card_ge {m n k ρ : Nat} (D : BoolMatrix m n)
    (hSparse : SparseDistinguisherMatrix m n k D)
    (hWindow : m * k + ρ ≤ widthFn n) :
    ρ ≤ (unqueriedPayloadCoords D).card := by
  have hq : (queryUnion D).card ≤ m * k := queryUnion_card_le_mul D hSparse
  have hInter : (payloadCoords n ∩ queryUnion D).card ≤ m * k := by
    exact (Finset.card_le_card Finset.inter_subset_right).trans hq
  have hSplit : (payloadCoords n ∩ queryUnion D).card + (unqueriedPayloadCoords D).card = widthFn n := by
    have h := Finset.card_inter_add_card_sdiff (payloadCoords n) (queryUnion D)
    rw [payloadCoords_card n] at h
    simpa [unqueriedPayloadCoords] using h
  omega

/-- Flip exactly the coordinates in `s` and leave all other coordinates at the anchor value. -/
def flipAnchorOn (n : Nat) (s : Finset (Fin n)) : Bitstring n :=
  fun j => if j ∈ s then ! payloadAnchor n j else payloadAnchor n j

/-- The flipped string agrees with the anchor off the chosen flip set. -/
theorem flipAnchorOn_eq_anchor_of_not_mem {n : Nat} {s : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ s) : flipAnchorOn n s j = payloadAnchor n j := by
  simp [flipAnchorOn, hj]

/-- If all flip coordinates are payload coordinates, the flipped string is tail-fixed. -/
theorem flipAnchorOn_tailFixed {n : Nat} {s : Finset (Fin n)}
    (hs : s ⊆ payloadCoords n) : tailFixedToAnchor n (flipAnchorOn n s) := by
  intro j hjPayload
  exact flipAnchorOn_eq_anchor_of_not_mem (n := n) (s := s) (j := j) (fun hjs => hjPayload (hs hjs))

/-- Payload-window distance from `flipAnchorOn n s` to the anchor counts exactly the payload flips. -/
theorem payloadWindowDistance_flipAnchorOn {n : Nat} {s : Finset (Fin n)}
    (hs : s ⊆ payloadCoords n) :
    payloadWindowDistance n (flipAnchorOn n s) (payloadAnchor n) = s.card := by
  have hFilter :
      (payloadCoords n).filter (fun j => flipAnchorOn n s j ≠ payloadAnchor n j) = s := by
    ext j
    by_cases hjs : j ∈ s
    · have hjPayload : j ∈ payloadCoords n := hs hjs
      simp [flipAnchorOn, hjs, hjPayload]
    · simp [flipAnchorOn, hjs]
  simp [payloadWindowDistance, hFilter]

/-- Membership criterion for the constructed far-NO point. -/
theorem flipAnchorOn_mem_payloadFarNoSet {n ρ : Nat} {s : Finset (Fin n)}
    (hsPayload : s ⊆ payloadCoords n) (hsCard : ρ ≤ s.card) :
    flipAnchorOn n s ∈ payloadFarNoSet n ρ := by
  simp [payloadFarNoSet]
  exact ⟨flipAnchorOn_tailFixed (n := n) (s := s) hsPayload,
    by simpa [payloadWindowDistance_flipAnchorOn (n := n) (s := s) hsPayload] using hsCard⟩

/--
Core combinatorial lemma.  Under `m*k + ρ ≤ widthFn n`, choose a far-NO point
that agrees with the anchor on every coordinate queried by `D`.
-/
theorem exists_farNo_agreeing_on_queryUnion {m n k ρ : Nat} (D : BoolMatrix m n)
    (hSparse : SparseDistinguisherMatrix m n k D)
    (hWindow : m * k + ρ ≤ widthFn n) :
    ∃ y : Bitstring n,
      y ∈ payloadFarNoSet n ρ ∧
        ∀ j : Fin n, j ∈ queryUnion D → y j = payloadAnchor n j := by
  obtain ⟨s, hsAvail, hsCard⟩ :=
    Finset.exists_subset_card_eq (s := unqueriedPayloadCoords D)
      (unqueriedPayloadCoords_card_ge D hSparse hWindow)
  refine ⟨flipAnchorOn n s, ?_, ?_⟩
  · have hsPayload : s ⊆ payloadCoords n := by
      intro j hjs
      exact (Finset.mem_sdiff.mp (hsAvail hjs)).1
    exact flipAnchorOn_mem_payloadFarNoSet (n := n) (ρ := ρ) (s := s) hsPayload (by omega)
  · intro j hjQuery
    apply flipAnchorOn_eq_anchor_of_not_mem
    intro hjs
    have hjNotQuery : j ∉ queryUnion D := (Finset.mem_sdiff.mp (hsAvail hjs)).2
    exact hjNotQuery hjQuery

/-- Agreement on the query union forces all fingerprint bits to agree. -/
theorem fingerprint_same_on_agreeing_queryUnion {m n : Nat} (D : BoolMatrix m n)
    (x y : Bitstring n)
    (hAgree : ∀ j : Fin n, j ∈ queryUnion D → x j = y j) :
    fingerprint D x = fingerprint D y := by
  funext i
  exact fingerprint_local D x y i (by
    intro j hjRow
    exact hAgree j (rowSupport_subset_queryUnion D i hjRow))

/--
D3′-A anti-collapse theorem, stated with the existing finite-set
`FingerprintSeparation` predicate from the D1/D3 matrix route.

For fixed sparse matrix budget `m,k` and positive farness `ρ`, if the payload
window is large enough (`m*k + ρ ≤ widthFn n`), then the non-overlapping
AND-payload YES/far-NO relation cannot be separated at fingerprint radius `1`
by any `m`-row, `k`-sparse fingerprint matrix.
-/
theorem andPayload_no_sparse_fingerprintSeparation
    (m n k ρ : Nat)
    (hρ : 1 ≤ ρ)
    (hWindow : m * k + ρ ≤ widthFn n) :
    ¬ ∃ D : BoolMatrix m n,
      SparseDistinguisherMatrix m n k D ∧
      FingerprintSeparation D (payloadYesSet n) (payloadFarNoSet n ρ) 1 := by
  have _hNonoverlap : Disjoint (payloadYesSet n) (payloadFarNoSet n ρ) :=
    payloadYes_farNo_disjoint hρ
  rintro ⟨D, hSparse, hSep⟩
  obtain ⟨y, hyNo, hyAgree⟩ := exists_farNo_agreeing_on_queryUnion D hSparse hWindow
  have hSame : fingerprint D y = fingerprint D (payloadAnchor n) :=
    fingerprint_same_on_agreeing_queryUnion D y (payloadAnchor n) hyAgree
  have hDist : 1 ≤ hammingDistance (fingerprint D (payloadAnchor n)) (fingerprint D y) := by
    exact hSep (payloadAnchor n) (by simp [payloadYesSet]) y hyNo
  rw [← hSame, hammingDistance_self] at hDist
  omega

/-- The constructed D3′-A relation is explicitly non-overlapping. -/
theorem andPayload_yes_farNo_disjoint (n ρ : Nat) (hρ : 1 ≤ ρ) :
    Disjoint (payloadYesSet n) (payloadFarNoSet n ρ) :=
  payloadYes_farNo_disjoint hρ

end V_codexd3a
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
