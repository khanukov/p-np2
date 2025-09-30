import Pnp2.Circuit.Family
import Pnp2.Circuit.Numeric
import Pnp2.family_entropy_cover
import Pnp2.bound
import Mathlib.Data.Nat.Log

noncomputable section

open Classical
open scoped BigOperators

namespace Boolcube
namespace Circuit
open Cover2

/-- The simple projection onto coordinate `i`.  We package it once to keep the
upcoming lemmas readable. -/
@[simp] def projection (n : ℕ) (i : Fin n) : BFunc n := fun x => x i

/-- The coordinate projection depends on the very coordinate it reads, hence it
belongs to the support. -/
lemma mem_support_projection {n : ℕ} (i : Fin n) :
    i ∈ BoolFunc.support (projection (n := n) i) := by
  classical
  -- Use the characterisation of the support via the Boolean flip on `i`.
  refine (BoolFunc.mem_support_iff (f := projection (n := n) i) (i := i)).2 ?_
  -- Choose the all-`false` vector and flip the `i`-th coordinate.
  refine ⟨fun _ => false, ?_⟩
  -- The projection evaluates to `false` on the base point and to `true` on the
  -- updated point, so the values differ.
  simp [projection, BoolFunc.Point.update]

/-- Every coordinate projection is implemented by the size-one circuit
`Circuit.var`.  Therefore the projection belongs to the polynomial circuit
family. -/
lemma projection_mem_powFamily {n c : ℕ} (i : Fin n) :
    projection (n := n) i ∈ powFamily n c := by
  classical
  -- The witnessing circuit is simply `Circuit.var i`.
  refine (mem_powFamily (n := n) (c := c)).2 ?_
  refine ⟨Circuit.var i, ?_, ?_⟩
  · -- One gate suffices, and `1 ≤ n^c` for any non-trivial `n`.
    have hn : 1 ≤ n := Nat.succ_le_of_lt i.is_lt
    have hpow : 1 ≤ n ^ c := Nat.one_le_pow_of_one_le hn _
    simpa [Circuit.gateCount]
  · -- Evaluation of `Circuit.var` is exactly the coordinate projection.
    intro x
    simp [projection, Circuit.eval]

/-- The union of supports of the polynomial circuit family covers every
coordinate: each coordinate projection lies in the family and contributes its
index. -/
lemma supportUnion_powFamily_eq_univ (n c : ℕ) :
    supportUnion (powFamily n c) = (Finset.univ : Finset (Fin n)) := by
  classical
  ext i; constructor
  · intro _; exact Finset.mem_univ _
  · intro _
    -- Witness the membership via the coordinate projection.
    have hmem : i ∈ BoolFunc.support (projection (n := n) i) :=
      mem_support_projection (n := n) i
    have hproj : projection (n := n) i ∈ powFamily n c :=
      projection_mem_powFamily (n := n) (c := c) i
    -- Unfold the definition of `supportUnion` to expose the existential.  The
    -- projection provides the required witness.
    simp [supportUnion, hproj, hmem]

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

/-- Every rectangle produced by the canonical cover for `powFamily` freezes all
coordinates.  Consequently both the left and the right enumeration budgets of
size `0` are satisfied for any choice of the cut `k`. -/
lemma coverFamily_powFamily_respects_budgets {n c k : ℕ} :
    ∀ R ∈ coverFamily (F := powFamily n c)
        (h := powFamilyEntropyBound n c)
        (powFamily_H₂_le (n := n) (c := c)),
      Subcube.respectsEnumerationBudgets (n := n) R k 0 0 := by
  classical
  intro R hR
  -- Rectangles of the canonical cover belong to `coverUniverse`.
  have hsubset :=
    buildCover_subset_coverUniverse (n := n)
      (F := powFamily n c) (h := powFamilyEntropyBound n c)
      (hH := powFamily_H₂_le (n := n) (c := c))
  have hRsubset : R ∈ coverUniverse (n := n) (powFamily n c) := by
    have hbuild : R ∈ buildCover (n := n) (powFamily n c)
        (powFamilyEntropyBound n c)
        (powFamily_H₂_le (n := n) (c := c)) := by
      simpa [coverFamily]
        using hR
    exact hsubset hbuild
  -- Unpack the definition of `coverUniverse`: each rectangle is obtained by
  -- freezing the full support of the family around some point `x`.
  rcases Finset.mem_image.mp hRsubset with ⟨x, -, rfl⟩
  -- For `powFamily` the support union is the entire set of coordinates.
  have hsupport := supportUnion_powFamily_eq_univ (n := n) (c := c)
  -- Compute the set of free left coordinates explicitly: the fix function is
  -- always `some`, hence no index survives the filter.
  have hleft_card :
      (Subcube.freeLeft (n := n)
          (Subcube.fromPoint (n := n) x Finset.univ) k).card = 0 := by
    refine Finset.card_eq_zero.mpr ?_
    intro i hi
    have : ((Subcube.fromPoint (n := n) x Finset.univ).fix i).isNone :=
      (Subcube.mem_freeLeft (R := Subcube.fromPoint (n := n) x Finset.univ)
        (k := k) (i := i)).1 hi |>.2
    -- Contradiction: every coordinate is fixed because we freeze `Finset.univ`.
    simpa [Subcube.fromPoint] using this
  -- Symmetric reasoning for the right block.
  have hright_card :
      (Subcube.freeRight (n := n)
          (Subcube.fromPoint (n := n) x Finset.univ) k).card = 0 := by
    refine Finset.card_eq_zero.mpr ?_
    intro i hi
    have : ((Subcube.fromPoint (n := n) x Finset.univ).fix i).isNone :=
      (Subcube.mem_freeRight (R := Subcube.fromPoint (n := n) x Finset.univ)
        (k := k) (i := i)).1 hi |>.2
    simpa [Subcube.fromPoint] using this
  -- Translate the equalities back to the rectangle currently under
  -- consideration and discharge the budget predicates.
  have hleft_card_R :
      (Subcube.freeLeft (n := n)
          (Subcube.fromPoint (n := n) x (supportUnion (powFamily n c))) k).card = 0 := by
    simpa [hsupport]
      using hleft_card
  have hright_card_R :
      (Subcube.freeRight (n := n)
          (Subcube.fromPoint (n := n) x (supportUnion (powFamily n c))) k).card = 0 := by
    simpa [hsupport]
      using hright_card
  refine ⟨?_, ?_⟩
  · -- Left budget.
    simpa [Subcube.respectsLeftBudget, hleft_card_R]
  · -- Right budget.
    simpa [Subcube.respectsRightBudget, hright_card_R]

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

/-- A refined version of `powFamily_cover_for_member` which packages the
double-exponential cardinality estimate obtained in
`powFamilyExponentBound_le_doubleExp`. -/
theorem powFamily_cover_for_member_doubleExp {n c : ℕ} {f : BFunc n}
    (hf : f ∈ powFamily n c) (hn : coverThreshold c ≤ n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (2 ^ n - 2 ^ (n / 2)) := by
  classical
  obtain ⟨_, htwo⟩ := coverThreshold_spec (c := c) (n := n) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) htwo
  obtain ⟨Rset, hmono, hcover, hcard⟩ :=
    powFamily_cover_for_member (n := n) (c := c) (f := f) hf hnpos
  refine ⟨Rset, hmono, hcover, ?_⟩
  have hbound := powFamilyExponentBound_le_doubleExp (n := n) (c := c) hn
  exact hcard.trans
    (Nat.pow_le_pow_of_le_left (by decide : 1 ≤ 2) hbound)

/-- Version of `powFamily_cover_for_member` that additionally records the
enumeration budgets: every rectangle in the cover fixes all coordinates and
therefore respects the trivial budgets `(0, 0)` regardless of the chosen
partition `k`. -/
theorem powFamily_cover_for_member_respects_budgets
    {n c : ℕ} {f : BFunc n}
    (hf : f ∈ powFamily n c) (hn : 0 < n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2
        (3 * n + 11 * powFamilyEntropyBound n c + 2) ∧
      (∀ k : ℕ, ∀ R ∈ Rset,
          Subcube.respectsEnumerationBudgets (n := n) R k 0 0) := by
  classical
  -- Start from the canonical cover for the whole family and filter it down to
  -- the rectangles relevant for `f`, exactly as in `powFamily_cover_for_member`.
  let hH := powFamily_H₂_le (n := n) (c := c)
  let R0 := coverFamily (F := powFamily n c)
      (h := powFamilyEntropyBound n c) hH
  let Rset := R0.filter fun R => ∀ x, f x = true → x ∈ₛ R
  have hmono :=
    coverFamily_pointwiseMono (n := n) (F := powFamily n c)
      (h := powFamilyEntropyBound n c) hH
  have hcover :=
    coverFamily_spec_cover (n := n) (F := powFamily n c)
      (h := powFamilyEntropyBound n c) hH
  have hcard :=
    coverFamily_card_le_mBound (n := n) (F := powFamily n c)
      (h := powFamilyEntropyBound n c) hH hn
  -- Every rectangle of the canonical family freezes all coordinates; the
  -- property holds uniformly for any choice of the split `k`.
  have hbudget :
      ∀ k : ℕ, ∀ R ∈ R0,
          Subcube.respectsEnumerationBudgets (n := n) R k 0 0 :=
    fun k => coverFamily_powFamily_respects_budgets (n := n) (c := c) (k := k)
  refine ⟨Rset, ?_, ?_, ?_, ?_⟩
  · -- Monochromaticity descends to the filtered cover.
    intro R hR x hx
    have hmem : R ∈ R0 := (Finset.mem_filter.mp hR).1
    exact hmono R hmem f hf x hx
  · -- Coverage persists after filtering thanks to the predicate itself.
    intro x hx
    rcases hcover f hf x hx with ⟨R, hR, hxR⟩
    refine ⟨R, ?_, hxR⟩
    have hcond : ∀ y, f y = true → y ∈ₛ R := by
      intro y hy
      have hmonoR := hmono R hR f hf
      have := Subcube.mem_monochromaticFor (R := R) (f := f) hy hmonoR
      simpa using this
    exact Finset.mem_filter.mpr ⟨hR, hcond⟩
  · -- Cardinality bound inherited from the whole family via `mBound`.
    have hcard_filtered : Rset.card ≤ R0.card := Finset.card_filter_le _ _
    have hbound := Bound.mBound_le_two_pow_linear
      (n := n) (h := powFamilyEntropyBound n c)
    exact hcard_filtered.trans (hcard.trans hbound)
  · -- Budgets: every rectangle in the canonical cover freezes all coordinates,
    -- hence the filtered cover inherits the property for every split `k`.
    intro k R hR
    have hmem : R ∈ R0 := (Finset.mem_filter.mp hR).1
    exact hbudget k R hmem

/--
**Small-circuit double-exponential cover (Lemma B‑5).**

If a Boolean function `f : 𝔹ⁿ → Bool` is computable by a circuit of size at most
`n^c`, then for every sufficiently large `n` (controlled by `coverThreshold c`)
there exists a family of rectangular subcubes with the following properties:

* every rectangle is monochromatic for `f` (colour `true` or `false`),
* every `1`-input of `f` lies in at least one rectangle,
* the number of rectangles is bounded by `2^{2^n - 2^{n/2}}` (choose `δ = 1/2`),
* every rectangle fixes **all** coordinates, hence respects the enumeration
  budgets on both halves of any partition of the variables.

The last item is stronger than the statement of Lemma B‑5: the construction
enforces zero free bits on either side, so enumeration terminates in constant
time.  We expose the guarantee with explicit budgets `(0, 0)` for later reuse.
-/
theorem smallCircuit_doubleExp_cover {n c : ℕ} {f : BFunc n}
    (hf : f ∈ powFamily n c) (hn : coverThreshold c ≤ n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (2 ^ n - 2 ^ (n / 2)) ∧
      (∀ k : ℕ, ∀ R ∈ Rset,
          Subcube.respectsEnumerationBudgets (n := n) R k 0 0) := by
  classical
  obtain ⟨_, htwo⟩ := coverThreshold_spec (c := c) (n := n) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) htwo
  -- Start from the canonical cover with explicit budget control.
  obtain ⟨Rset, hmono, hcover, hcard, hbud⟩ :=
    powFamily_cover_for_member_respects_budgets
      (n := n) (c := c) (f := f) hf hnpos
  -- Upgrade the polynomial exponent bound to the double-exponential form.
  have hdouble :
      Rset.card ≤ Nat.pow 2 (2 ^ n - 2 ^ (n / 2)) := by
    have hbound := powFamilyExponentBound_le_doubleExp (n := n) (c := c) hn
    exact hcard.trans
      (Nat.pow_le_pow_of_le_left (by decide : 1 ≤ 2) hbound)
  refine ⟨Rset, hmono, hcover, hdouble, ?_⟩
  intro k R hR
  exact hbud k R hR

end Circuit
end Boolcube

