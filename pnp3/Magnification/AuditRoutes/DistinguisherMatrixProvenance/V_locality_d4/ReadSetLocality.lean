import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives
import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.AntiCollapse
import Mathlib.Tactic

/-!
# D4: read-set locality limitation for sparse distinguisher matrices

This module records the D4 audit lesson for the sparse-distinguisher-matrix
route (the Atserias–Müller-style "distinguisher" magnification idea, arXiv
2503.24061).  It makes precise, and kernel-checks, the elementary *locality* of
the parity-fingerprint map: the fingerprint of a string under a matrix `D`
depends only on the coordinates that some row of `D` actually reads.

Definitions and results formalised here:

* `readSet D` — the set of input coordinates read by some row of `D`;
* `fingerprint_eq_of_agree_on_readSet` — two strings agreeing on `readSet D`
  have identical fingerprints (the whole-matrix version of the D1 lemma
  `fingerprint_local`);
* `no_fingerprintSeparation_of_agree_on_readSet` — a matrix cannot positively
  separate a YES instance from a NO instance that agree on everything it reads;
* `readSet_card_le_mul` — an `m`-row `k`-sparse matrix reads at most `m * k`
  input coordinates.

Read together with the D3′ pair (`V_codexd3a.AntiCollapsePrime` budget no-go and
`V_codexd3c.Sharpness` full-window separation), this pins the separation power
of a distinguisher to exactly *which* coordinates it reads, and bounds that
quantity by the sparsity budget.  As a sanity check it re-derives the D3
overlapping-singleton anti-collapse kernel as the special case where the YES and
NO instances coincide.

**Honest scope — what this is NOT.**  This is the finite-combinatorial shadow of
the Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam *locality barrier*
(`Beyond Natural Proofs: Hardness Magnification and Locality`, JACM 2022) in the
distinguisher setting, stated only for parity fingerprints.  It does **not**:

* refute the Atserias–Müller route — the `Sharpness` companion shows separation
  *is* achievable once enough coordinates are read;
* introduce a source theorem, a provenance-filter promotion, a `PpolyDAG`
  bridge, or a `P ≠ NP` endpoint;
* claim any lower bound or unconditional consequence.

Progress classification: side-track audit formalization (locality bookkeeping
for the distinguisher route).
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_locality_d4

open ComplexityInterfaces
open V_gpt55

/-- All input coordinates read by some row of `D`: the union of the row
supports.  This is the locality footprint of the fingerprint map. -/
def readSet {m n : Nat} (D : BoolMatrix m n) : Finset (Fin n) :=
  Finset.univ.biUnion (fun i => rowSupport D i)

/-- Each row support is contained in the matrix read-set. -/
theorem rowSupport_subset_readSet {m n : Nat} (D : BoolMatrix m n) (i : Fin m) :
    rowSupport D i ⊆ readSet D :=
  Finset.subset_biUnion_of_mem (fun i => rowSupport D i) (Finset.mem_univ i)

/--
**Locality of the fingerprint map.**

If `x` and `y` agree on every coordinate the matrix reads, then their full
fingerprints are identical.  This lifts the per-row `fingerprint_local` lemma to
the whole matrix.
-/
theorem fingerprint_eq_of_agree_on_readSet {m n : Nat} (D : BoolMatrix m n)
    (x y : Bitstring n)
    (hAgree : ∀ j, j ∈ readSet D → x j = y j) :
    fingerprint D x = fingerprint D y := by
  funext i
  refine fingerprint_local D x y i ?_
  intro j hj
  exact hAgree j (rowSupport_subset_readSet D i hj)

/--
**Read-set locality limitation on separation.**

A distinguisher matrix cannot positively separate a YES instance from a NO
instance when the two agree on everything the matrix reads: their fingerprints
collide, so the Hamming distance is `0` and no positive radius is met.
-/
theorem no_fingerprintSeparation_of_agree_on_readSet {m n : Nat}
    (D : BoolMatrix m n) (yesSet noSet : Finset (Bitstring n)) (r : Nat)
    (x : Bitstring n) (hx : x ∈ yesSet)
    (y : Bitstring n) (hy : y ∈ noSet)
    (hAgree : ∀ j, j ∈ readSet D → x j = y j) :
    ¬ FingerprintSeparation D yesSet noSet (r + 1) := by
  intro hsep
  have hfp : fingerprint D x = fingerprint D y :=
    fingerprint_eq_of_agree_on_readSet D x y hAgree
  have hpos : r + 1 ≤ hammingDistance (fingerprint D x) (fingerprint D y) :=
    hsep x hx y hy
  rw [hfp, hammingDistance_self] at hpos
  exact Nat.not_succ_le_zero r hpos

/--
The D3 overlapping-singleton anti-collapse kernel
(`no_self_fingerprintSeparation`) is the special case of the read-set
limitation where the YES and NO instances are literally the same point (they
agree everywhere, in particular on `readSet D`).
-/
theorem no_self_fingerprintSeparation_via_readSet
    {m n : Nat} (D : BoolMatrix m n) (x : Bitstring n) (r : Nat) :
    ¬ FingerprintSeparation D ({x} : Finset (Bitstring n)) ({x}) (r + 1) :=
  no_fingerprintSeparation_of_agree_on_readSet D {x} {x} r x (by simp) x (by simp)
    (by intro j _; rfl)

/-- The read-set is bounded by the sum of the row-support cardinalities. -/
theorem readSet_card_le_sum {m n : Nat} (D : BoolMatrix m n) :
    (readSet D).card ≤ ∑ i : Fin m, MatrixRowSupportCard D i := by
  simpa [readSet, MatrixRowSupportCard] using
    Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m)))
      (t := fun i => rowSupport D i)

/--
**Quantitative locality.**

An `m`-row `k`-sparse distinguisher matrix reads at most `m * k` input
coordinates.  Combined with `no_fingerprintSeparation_of_agree_on_readSet`, this
is the precise resource bound that any fingerprint separation must overcome: a
sparse matrix is local, so YES/NO instances differing only outside a set of more
than `m * k` coordinates are invisible to it.
-/
theorem readSet_card_le_mul {m n k : Nat} (D : BoolMatrix m n)
    (hSparse : SparseDistinguisherMatrix m n k D) :
    (readSet D).card ≤ m * k := by
  have hrow : ∀ i : Fin m, MatrixRowSupportCard D i ≤ k := hSparse.1
  calc
    (readSet D).card ≤ ∑ i : Fin m, MatrixRowSupportCard D i := readSet_card_le_sum D
    _ ≤ ∑ _i : Fin m, k := Finset.sum_le_sum (fun i _ => hrow i)
    _ = m * k := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end V_locality_d4
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
