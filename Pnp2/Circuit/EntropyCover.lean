import Pnp2.Circuit.Family
import Pnp2.family_entropy_cover
import Pnp2.bound
import Mathlib.Data.Nat.Log

noncomputable section

open Classical
open scoped BigOperators

namespace Boolcube
namespace Circuit

/-- The length bound used by the encoding of circuits of size `≤ n^c`. -/
def encodingLength (n c : ℕ) : ℕ := 4 * n ^ c

/-- The alphabet size for the encoding of circuits of size `≤ n^c`. -/
def encodingAlphabet (n c : ℕ) : ℕ := Nat.max n (4 * n ^ c) + 5

/-- Auxiliary exponent controlling the size of the encoding space. -/
def powFamilyEntropyBound (n c : ℕ) : ℕ :=
  Nat.log2 (encodingLength n c + 1) + 1 +
    encodingLength n c * (Nat.log2 (encodingAlphabet n c) + 1)

/-- Boolean functions on `n` bits computable by a circuit of size `≤ n^c`. -/
noncomputable def powFamily (n c : ℕ) : Family n :=
  (Finset.univ.filter fun f : BFunc n =>
    ∃ C : Circuit n, gateCount C ≤ n ^ c ∧ ∀ x, Circuit.eval C x = f x)

lemma mem_powFamily {n c : ℕ} {f : BFunc n} :
    f ∈ powFamily n c ↔ ∃ C : Circuit n,
      gateCount C ≤ n ^ c ∧ ∀ x, Circuit.eval C x = f x := by
  classical
  constructor
  · intro hf
    rcases Finset.mem_filter.mp hf with ⟨_, hpred⟩
    exact hpred
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- Extract a canonical witnessing circuit for a function in `powFamily`. -/
noncomputable def powFamilyWitness {n c : ℕ} {f : BFunc n}
    (hf : f ∈ powFamily n c) :
    {C : Circuit n // gateCount C ≤ n ^ c ∧ ∀ x, Circuit.eval C x = f x} := by
  classical
  rcases mem_powFamily.mp hf with ⟨C, hC⟩
  exact ⟨C, hC⟩

/-- Encode a member of `powFamily` as the circuit encoding of its witnessing
small circuit. -/
noncomputable def powFamilyEncodingSubtype (n c : ℕ) :
    {f : BFunc n // f ∈ powFamily n c} →
      Fin (encodingLength n c + 1) ×
        Vector (Fin (encodingAlphabet n c)) (encodingLength n c) :=
  fun f =>
    let witness := powFamilyWitness (n := n) (c := c) f.property
    have hlen : gateCount witness.val ≤ n ^ c := witness.property.1
    encodeVector (n := n) (m := n ^ c) witness.val hlen

/-- The encoding map on `powFamily` is injective. -/
lemma powFamilyEncodingSubtype_injective {n c : ℕ} :
    Function.Injective (powFamilyEncodingSubtype (n := n) (c := c)) := by
  intro f g henc
  classical
  set wf := powFamilyWitness (n := n) (c := c) f.property
  set wg := powFamilyWitness (n := n) (c := c) g.property
  have hcircuits :
      (⟨wf.val, wf.property.1⟩ : {C : Circuit n // gateCount C ≤ n ^ c})
        = ⟨wg.val, wg.property.1⟩ := by
    apply encodeVector_injective (n := n) (m := n ^ c)
    simpa [powFamilyEncodingSubtype, wf, wg]
      using henc
  have hvals : wf.val = wg.val := congrArg Subtype.val hcircuits
  apply Subtype.eq
  ext x
  have hwf := wf.property.2 x
  have hwg := wg.property.2 x
  simpa [hwf, hwg, hvals]

/-- Helper lemma: `x ≤ 2^{log₂ x + 1}` for all natural numbers `x`. -/
lemma le_two_pow_log2_succ (x : ℕ) :
    x ≤ Nat.pow 2 (Nat.log2 x + 1) := by
  classical
  cases hx : x with
  | zero => simp
  | succ x =>
      have hb : 1 < 2 := by decide
      have hxlt : x.succ < 2 ^ (Nat.log2 x.succ).succ :=
        Nat.lt_pow_succ_log_self hb _
      have hxlt' : x.succ < Nat.succ (2 ^ (Nat.log2 x.succ + 1)) :=
        lt_trans hxlt (Nat.lt_succ_self _)
      exact Nat.le_of_lt_succ hxlt'

/-- Exponential domination of `A^L` by powers of two with logarithmic
exponents. -/
lemma pow_le_two_pow (A L : ℕ) :
    A ^ L ≤ Nat.pow 2 (L * (Nat.log2 A + 1)) := by
  classical
  induction L with
  | zero => simp
  | succ L ih =>
      have hbound := le_two_pow_log2_succ A
      have hmul :
          (A ^ L) * A ≤ Nat.pow 2 (L * (Nat.log2 A + 1)) *
            Nat.pow 2 (Nat.log2 A + 1) :=
        Nat.mul_le_mul ih hbound
      have : A ^ (L + 1) ≤ Nat.pow 2 ((L + 1) * (Nat.log2 A + 1)) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_add,
          Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
          Nat.add_mul] using hmul
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using this

/-- The size of the encoding target grows at most exponentially with the bound
`powFamilyEntropyBound`. -/
lemma encoding_card_le (n c : ℕ) :
    Fintype.card
        (Fin (encodingLength n c + 1) ×
          Vector (Fin (encodingAlphabet n c)) (encodingLength n c))
      ≤ Nat.pow 2 (powFamilyEntropyBound n c) := by
  classical
  set L := encodingLength n c
  set A := encodingAlphabet n c
  have hcard :
      Fintype.card (Fin (L + 1) × Vector (Fin A) L)
        = (L + 1) * A ^ L := by
    simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_vector]
  have hlen := le_two_pow_log2_succ (L + 1)
  have hpow := pow_le_two_pow A L
  have hprod :
      (L + 1) * A ^ L ≤
          Nat.pow 2 (Nat.log2 (L + 1) + 1 + L * (Nat.log2 A + 1)) := by
    have := Nat.mul_le_mul hlen hpow
    simpa [Nat.pow_add, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  simpa [powFamilyEntropyBound, encodingLength, encodingAlphabet, hcard]
    using hprod

/-- Cardinality bound for the family of size-`≤ n^c` circuits. -/
lemma powFamily_card_le {n c : ℕ} :
    (powFamily n c).card ≤ Nat.pow 2 (powFamilyEntropyBound n c) := by
  classical
  have hattach :
      (powFamily n c).attach.card ≤
        Fintype.card
          (Fin (encodingLength n c + 1) ×
            Vector (Fin (encodingAlphabet n c)) (encodingLength n c)) := by
    have hinj := powFamilyEncodingSubtype_injective (n := n) (c := c)
    have hcardImage :=
      (Finset.card_image_iff).mpr fun x hx y hy hxy =>
        Subtype.eq (hinj (Subtype.eq rfl ▸ hxy))
    have hbounded := Finset.card_le_univ
      (s := (powFamily n c).attach.image (powFamilyEncodingSubtype (n := n) (c := c)))
    simpa [powFamilyEncodingSubtype, hcardImage] using hbounded
  simpa [Finset.card_attach] using hattach.trans (encoding_card_le (n := n) (c := c))

/-- Collision-entropy bound for the polynomial-size circuit family. -/
lemma powFamily_H₂_le {n c : ℕ} :
    BoolFunc.H₂ (powFamily n c) ≤ powFamilyEntropyBound n c := by
  classical
  have hcard := powFamily_card_le (n := n) (c := c)
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hmonotone := Real.logb_le_logb (b := 2) hpos
  have hcast :
      ((powFamily n c).card : ℝ) ≤ (Nat.pow 2 (powFamilyEntropyBound n c) : ℝ) := by
    exact_mod_cast hcard
  have hlog := hmonotone hcast
  simpa [BoolFunc.H₂, Real.logb_pow, powFamilyEntropyBound, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul] using hlog

/-- Existence of a cover for the entire polynomial-size circuit family. -/
theorem powFamily_cover {n c : ℕ} (hn : 0 < n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ g ∈ powFamily n c, Subcube.monochromaticFor R g) ∧
      (∀ f ∈ powFamily n c, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2
        (3 * n + 11 * powFamilyEntropyBound n c + 2) := by
  classical
  rcases Bound.family_collision_entropy_lemma
      (F := powFamily n c) (h := powFamilyEntropyBound n c)
      (hH := powFamily_H₂_le (n := n) (c := c)) (hn_pos := hn) with
    ⟨Rset, hmono, hcover, hcard⟩
  refine ⟨Rset, hmono, hcover, ?_⟩
  have := Bound.mBound_le_two_pow_linear (n := n)
      (h := powFamilyEntropyBound n c)
  exact hcard.trans this

/-- Specialised cover for an individual member of `powFamily`. -/
theorem powFamily_cover_for_member {n c : ℕ} {f : BFunc n}
    (hf : f ∈ powFamily n c) (hn : 0 < n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2
        (3 * n + 11 * powFamilyEntropyBound n c + 2) := by
  classical
  rcases powFamily_cover (n := n) (c := c) hn with ⟨Rset, hmono, hcover, hcard⟩
  refine ⟨Rset.filter fun R => ∀ x, f x = true → x ∈ₛ R,
    ?_, ?_, ?_⟩
  · intro R hR x hx
    have hmem : R ∈ Rset := (Finset.mem_filter.mp hR).1
    have hmonoR := hmono R hmem f hf
    exact hmonoR hx
  · intro x hx
    rcases hcover f hf x hx with ⟨R, hR, hxR⟩
    refine ⟨R, ?_, hxR⟩
    have hcond : ∀ y, f y = true → y ∈ₛ R := by
      intro y hy
      have hmonoR := hmono R hR f hf
      have hx' := hmonoR hy
      have := Subcube.mem_monochromaticFor (R := R) (f := f) hy hmonoR
      simpa using this
    exact Finset.mem_filter.mpr ⟨hR, hcond⟩
  · have := Finset.card_filter_le (s := Rset)
      (p := fun R => ∀ x, f x = true → x ∈ₛ R)
    exact this.trans hcard

end Circuit
end Boolcube

