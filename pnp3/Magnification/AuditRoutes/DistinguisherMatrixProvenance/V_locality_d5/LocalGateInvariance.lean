import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives
import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.AntiCollapse
import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d4.ReadSetLocality
import Mathlib.Tactic

/-!
# D5: locality is closed under composition (the barrier-robustness shadow)

This module continues the sparse-distinguisher-matrix audit (Atserias–Müller
style magnification, arXiv 2503.24061).  D4 (`V_locality_d4.ReadSetLocality`)
showed that a `k`-sparse distinguisher reads at most `m * k` coordinates and
therefore cannot separate instances that agree on what it reads.  D5 records the
*mechanism* by which that locality is robust — the formal shadow of the
Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam locality barrier
(`Beyond Natural Proofs: Hardness Magnification and Locality`, JACM 2022).

The barrier intuition is: the magnified hard instances are computed by circuits
with **small fan-in oracle gates**, and lower-bound techniques against weak
models are robust to such gates — so adding a local oracle layer does not help.
Here we formalise the elementary core of that robustness for the fingerprint
view:

* `LocalSupport g S` / `KLocal g k` — a map whose every output bit is a "small
  fan-in (≤ k) oracle gate" (depends on ≤ k input coordinates);
* `KLocal.comp` — **composing a `k`-local map with an `ℓ`-local map yields an
  `(ℓ * k)`-local map**: locality is multiplicatively closed, so a bounded-depth
  stack of small-fan-in gates stays local;
* `fingerprint_kLocal` — the `k`-sparse distinguisher fingerprint is `k`-local;
* `no_localPost_separation_of_agree_on_readSet` — post-composing the
  distinguisher with **any** map `h` (in particular any local oracle layer)
  still cannot separate instances that agree on the `≤ m * k` coordinates the
  distinguisher reads.

**Honest scope — what this is NOT.**  This is a side-track audit formalization.
It does **not**:

* refute the Atserias–Müller route — it only analyses the parity-fingerprint
  separation view formalised in this audit, not their full MCSP construction;
* introduce a source theorem, a provenance-filter promotion, a `PpolyDAG`
  bridge, or a `P ≠ NP` endpoint;
* claim any lower bound or unconditional consequence.

Progress classification: side-track audit formalization (compositional locality
bookkeeping for the distinguisher route).
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_locality_d5

open ComplexityInterfaces
open V_gpt55
open V_locality_d4

/-- Generic separation of a YES/NO relation by an arbitrary feature map `f`,
measured in Hamming distance on the output fingerprints. -/
def MapSeparation {n p : Nat} (f : Bitstring n → Bitstring p)
    (yesSet noSet : Finset (Bitstring n)) (radius : Nat) : Prop :=
  ∀ x, x ∈ yesSet → ∀ y, y ∈ noSet → radius ≤ hammingDistance (f x) (f y)

/-- If a feature map collapses a YES point and a NO point to the same output, it
cannot positively separate the relation. -/
theorem no_mapSeparation_of_collapse {n p : Nat} (f : Bitstring n → Bitstring p)
    (yesSet noSet : Finset (Bitstring n)) (r : Nat)
    (x : Bitstring n) (hx : x ∈ yesSet)
    (y : Bitstring n) (hy : y ∈ noSet)
    (hcollapse : f x = f y) :
    ¬ MapSeparation f yesSet noSet (r + 1) := by
  intro hsep
  have hpos : r + 1 ≤ hammingDistance (f x) (f y) := hsep x hx y hy
  rw [hcollapse, hammingDistance_self] at hpos
  exact Nat.not_succ_le_zero r hpos

/-- `S` is a per-output support family for `g`: output bit `i` is determined by
the input coordinates in `S i` (a "fan-in `|S i|` oracle gate"). -/
def LocalSupport {n m : Nat} (g : Bitstring n → Bitstring m)
    (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ (i : Fin m) (x y : Bitstring n), (∀ j ∈ S i, x j = y j) → g x i = g y i

/-- `g` is `k`-local when it admits a per-output support family of fan-in `≤ k`. -/
def KLocal {n m : Nat} (g : Bitstring n → Bitstring m) (k : Nat) : Prop :=
  ∃ S : Fin m → Finset (Fin n), (∀ i, (S i).card ≤ k) ∧ LocalSupport g S

/--
**Locality is closed under composition.**

If `g` is `k`-local and `h` is `ℓ`-local, then `h ∘ g` is `(ℓ * k)`-local.
Each output of `h ∘ g` reads at most `ℓ` outputs of `g`, each of which reads at
most `k` inputs.  This is the formal robustness of locality: stacking
small-fan-in oracle gates keeps the per-output fan-in bounded by the product, so
a bounded-depth local circuit cannot escape the read-set limitation.
-/
theorem KLocal.comp {n m p : Nat}
    {g : Bitstring n → Bitstring m} {h : Bitstring m → Bitstring p}
    {k ℓ : Nat} (hg : KLocal g k) (hh : KLocal h ℓ) :
    KLocal (fun x => h (g x)) (ℓ * k) := by
  obtain ⟨Sg, hSgCard, hSgLoc⟩ := hg
  obtain ⟨Sh, hShCard, hShLoc⟩ := hh
  refine ⟨fun i => (Sh i).biUnion Sg, ?_, ?_⟩
  · intro i
    calc ((Sh i).biUnion Sg).card
        ≤ ∑ i' ∈ Sh i, (Sg i').card := Finset.card_biUnion_le
      _ ≤ ∑ _i' ∈ Sh i, k := Finset.sum_le_sum (fun i' _ => hSgCard i')
      _ = (Sh i).card * k := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ℓ * k := mul_le_mul_right' (hShCard i) k
  · intro i x y hagree
    refine hShLoc i (g x) (g y) ?_
    intro i' hi'
    refine hSgLoc i' x y ?_
    intro j hj
    exact hagree j (Finset.mem_biUnion.mpr ⟨i', hi', hj⟩)

/-- The fingerprint of a `k`-sparse distinguisher matrix is `k`-local, witnessed
by the row supports. -/
theorem fingerprint_kLocal {m n k : Nat} (D : BoolMatrix m n)
    (hSparse : SparseDistinguisherMatrix m n k D) :
    KLocal (fingerprint D) k := by
  refine ⟨fun i => rowSupport D i, ?_, ?_⟩
  · intro i
    simpa [MatrixRowSupportCard] using hSparse.1 i
  · intro i x y hagree
    exact fingerprint_local D x y i hagree

/--
Post-composing the distinguisher fingerprint with **any** map `h` cannot recover
information lost on `readSet D`: if `x` and `y` agree on every coordinate the
matrix reads, the composite outputs are identical.
-/
theorem localPost_fingerprint_eq_of_agree_on_readSet {m n p : Nat}
    (D : BoolMatrix m n) (h : Bitstring m → Bitstring p)
    (x y : Bitstring n)
    (hAgree : ∀ j, j ∈ readSet D → x j = y j) :
    h (fingerprint D x) = h (fingerprint D y) := by
  rw [fingerprint_eq_of_agree_on_readSet D x y hAgree]

/--
**Barrier-robustness shadow.**

A distinguisher composed with any post-map `h` (e.g. any local oracle layer, by
`KLocal.comp`) still cannot separate a YES instance from a NO instance that
agree on everything the matrix reads.  Adding a local processing layer on top of
the fingerprint does not escape the read-set locality limitation of D4.
-/
theorem no_localPost_separation_of_agree_on_readSet {m n p : Nat}
    (D : BoolMatrix m n) (h : Bitstring m → Bitstring p)
    (yesSet noSet : Finset (Bitstring n)) (r : Nat)
    (x : Bitstring n) (hx : x ∈ yesSet)
    (y : Bitstring n) (hy : y ∈ noSet)
    (hAgree : ∀ j, j ∈ readSet D → x j = y j) :
    ¬ MapSeparation (fun z => h (fingerprint D z)) yesSet noSet (r + 1) :=
  no_mapSeparation_of_collapse (fun z => h (fingerprint D z)) yesSet noSet r
    x hx y hy
    (localPost_fingerprint_eq_of_agree_on_readSet D h x y hAgree)

end V_locality_d5
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
