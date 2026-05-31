import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives
import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.AntiCollapse
import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d4.ReadSetLocality
import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3c.Sharpness
import Mathlib.Tactic

/-!
# D7: the delocalization criterion (ceiling of the fingerprint audit)

This module turns the D4–D6 verdict into a characterization.  D4 showed a
fingerprint matrix collapses inputs agreeing on its read-set `readSet D`.  D7
reads off the exact dichotomy for the parity-fingerprint view and isolates the
property a family must have to resist *footprint-bounded* distinguishers.

* `CoverableBy yesSet noSet S` — every YES/NO pair differs somewhere inside `S`;
* `separation_coverableBy_readSet` — **necessity**: if `D` separates at radius
  `1`, the YES/NO differences are covered by `readSet D`;
* `exists_separator_of_coverable` / `coordProbe_separates` — **sufficiency**: if
  the differences are covered by `S`, the coordinate-selector matrix with
  `readSet = S` separates at radius `1`.  Hence *footprint-`S` separability ⇔
  difference-coverability by `S`*;
* `Delocalized yesSet noSet B` — no `≤ B`-coordinate set covers the differences;
* `delocalized_no_separator` — **the criterion**: a `B`-delocalized family is
  separated by **no** distinguisher of read-footprint `≤ B`.  Equivalently,
  delocalization is *necessary* to resist footprint-bounded distinguishers.

## Honest boundary — what D7 does NOT settle

`k`-sparsity bounds the read-footprint only by `m * k`; a matrix with many rows
may read **every** coordinate (`readSet D = univ`).  In that *full-footprint /
output-compression* regime the read-set limitation is vacuous:

* `fullFootprint_limitation_vacuous` — if `readSet D = univ`, agreeing on the
  read-set forces `x = y`, so D4/D7 impose no constraint at all.

This is exactly the regime where the Atserias–Müller construction (arXiv
2503.24061) lives: error-correcting-code distinguishers that read all
coordinates but compress to few output bits, separating low-weight differences
via code distance.  D7 therefore characterizes the *coordinate-skipping* regime
completely and **explicitly delimits** the compression+distance regime as
outside its reach — that regime is the genuine open question (a *non*-localizable
lower bound, in the sense of `Localizability of the approximation method`,
arXiv 2212.09285), which this audit cannot manufacture.

Progress classification: side-track audit formalization (characterization +
boundary delimitation).  No source theorem, provenance-filter promotion,
`PpolyDAG` bridge, or `P ≠ NP` endpoint; no lower bound against a real family.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_locality_d7

open ComplexityInterfaces
open V_gpt55
open V_locality_d4
open V_codexd3c

/-- The YES/NO differences are *covered* by the coordinate set `S` when every
YES instance and every NO instance disagree somewhere inside `S`. -/
def CoverableBy {n : Nat} (yesSet noSet : Finset (Bitstring n))
    (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ yesSet, ∀ y ∈ noSet, ∃ j ∈ S, x j ≠ y j

/--
**Necessity.**  If a fingerprint matrix separates the relation at radius `1`,
then the YES/NO differences are covered by what it reads: every YES/NO pair must
disagree somewhere inside `readSet D` (otherwise the fingerprints collide, by
D4).
-/
theorem separation_coverableBy_readSet {m n : Nat} (D : BoolMatrix m n)
    (yesSet noSet : Finset (Bitstring n))
    (hSep : FingerprintSeparation D yesSet noSet 1) :
    CoverableBy yesSet noSet (readSet D) := by
  intro x hx y hy
  by_contra hcov
  push_neg at hcov
  have hfp : fingerprint D x = fingerprint D y :=
    fingerprint_eq_of_agree_on_readSet D x y hcov
  have hpos : (1 : Nat) ≤ hammingDistance (fingerprint D x) (fingerprint D y) :=
    hSep x hx y hy
  rw [hfp, hammingDistance_self] at hpos
  omega

/-- A family is `B`-delocalized when **no** set of at most `B` coordinates covers
its YES/NO differences. -/
def Delocalized {n : Nat} (yesSet noSet : Finset (Bitstring n)) (B : Nat) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ B → ¬ CoverableBy yesSet noSet S

/--
**The delocalization criterion.**

A `B`-delocalized family is separated by **no** fingerprint matrix whose read
footprint has at most `B` coordinates.  Contrapositively, to be separable by a
footprint-`≤ B` distinguisher a family must *fail* to be `B`-delocalized — i.e.
delocalization is necessary to resist footprint-bounded distinguishers.
-/
theorem delocalized_no_separator {m n B : Nat}
    (yesSet noSet : Finset (Bitstring n))
    (hDeloc : Delocalized yesSet noSet B)
    (D : BoolMatrix m n) (hcard : (readSet D).card ≤ B) :
    ¬ FingerprintSeparation D yesSet noSet 1 := by
  intro hSep
  exact hDeloc (readSet D) hcard (separation_coverableBy_readSet D yesSet noSet hSep)

/-! ### Sufficiency: the coordinate-selector distinguisher -/

/-- The coordinate-selector matrix for `S`: row `i` reads coordinate `i` iff
`i ∈ S`, and nothing otherwise.  It is `1`-sparse with `readSet = S`. -/
def coordProbe {n : Nat} (S : Finset (Fin n)) : BoolMatrix n n :=
  fun i j => decide (i = j) && decide (j ∈ S)

theorem rowSupport_coordProbe {n : Nat} (S : Finset (Fin n)) (i : Fin n) :
    rowSupport (coordProbe S) i = if i ∈ S then {i} else ∅ := by
  ext j
  simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and, coordProbe,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases hiS : i ∈ S
  · simp only [hiS, if_true, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, _⟩; rfl
    · rintro rfl; exact ⟨rfl, hiS⟩
  · simp only [hiS, if_false, Finset.notMem_empty, iff_false, not_and]
    rintro rfl hj
    exact hiS hj

theorem fingerprint_coordProbe_apply {n : Nat} (S : Finset (Fin n))
    (x : Bitstring n) (i : Fin n) :
    fingerprint (coordProbe S) x i = if i ∈ S then x i else false := by
  unfold fingerprint
  rw [rowSupport_coordProbe]
  by_cases hiS : i ∈ S
  · simp [hiS, supportParity_singleton]
  · simp [hiS, supportParity, oddBool]

theorem readSet_coordProbe {n : Nat} (S : Finset (Fin n)) :
    readSet (coordProbe S) = S := by
  ext j
  simp only [readSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
    rowSupport_coordProbe]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hiS : i ∈ S
    · simp only [hiS, if_true, Finset.mem_singleton] at hi
      subst hi; exact hiS
    · simp [hiS] at hi
  · intro hj
    exact ⟨j, by simp [hj]⟩

/-- The coordinate-selector matrix is `1`-sparse. -/
theorem coordProbe_sparse {n : Nat} (S : Finset (Fin n)) :
    SparseDistinguisherMatrix n n 1 (coordProbe S) := by
  constructor
  · intro i
    rw [MatrixRowSupportCard, rowSupport_coordProbe]
    by_cases hiS : i ∈ S <;> simp [hiS]
  · intro j
    rw [MatrixColSupportCard]
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    simp only [colSupport, Finset.mem_filter, Finset.mem_univ, true_and, coordProbe,
      Bool.and_eq_true, decide_eq_true_eq] at ha hb
    exact ha.1.trans hb.1.symm

/-- **Sufficiency.**  If the differences are covered by `S`, the
coordinate-selector matrix separates the relation at radius `1`. -/
theorem coordProbe_separates {n : Nat} (S : Finset (Fin n))
    (yesSet noSet : Finset (Bitstring n))
    (hcov : CoverableBy yesSet noSet S) :
    FingerprintSeparation (coordProbe S) yesSet noSet 1 := by
  intro x hx y hy
  obtain ⟨j, hjS, hjne⟩ := hcov x hx y hy
  have hdiff : fingerprint (coordProbe S) x j ≠ fingerprint (coordProbe S) y j := by
    rw [fingerprint_coordProbe_apply, fingerprint_coordProbe_apply]
    simp only [hjS, if_true]
    exact hjne
  unfold hammingDistance
  refine Finset.card_pos.mpr ?_
  exact ⟨j, by simp [hdiff]⟩

/--
**Footprint dichotomy.**  A family is separable by *some* fingerprint matrix
with read-footprint `S` if and only if its YES/NO differences are covered by
`S`.  (For nonempty relations, at radius `1`.)
-/
theorem exists_separator_of_coverable {n : Nat}
    (yesSet noSet : Finset (Bitstring n)) (S : Finset (Fin n))
    (hcov : CoverableBy yesSet noSet S) :
    ∃ D : BoolMatrix n n,
      readSet D = S ∧ FingerprintSeparation D yesSet noSet 1 :=
  ⟨coordProbe S, readSet_coordProbe S, coordProbe_separates S yesSet noSet hcov⟩

/-! ### Honest boundary: the compression / full-footprint regime is not covered -/

/--
If a matrix reads **every** coordinate (`readSet D = univ`), the read-set
limitation is vacuous: two strings agreeing on the read-set are equal.  Hence
D4/D7 impose **no** constraint on full-footprint output-compressing
distinguishers — the regime where the Atserias–Müller code-distance construction
lives.  This delimits the audit: the parity-fingerprint footprint view says
nothing about the compression+distance route, which remains the open question.
-/
theorem fullFootprint_limitation_vacuous {m n : Nat} (D : BoolMatrix m n)
    (hfull : readSet D = Finset.univ) (x y : Bitstring n)
    (hagree : ∀ j ∈ readSet D, x j = y j) :
    x = y := by
  funext j
  exact hagree j (by rw [hfull]; exact Finset.mem_univ j)

end V_locality_d7
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
