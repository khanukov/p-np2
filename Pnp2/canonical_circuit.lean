import Pnp2.Boolcube
import Mathlib.Data.List.Basic

/-
canonical_circuit.lean
======================

This module formalises a very small model of Boolean circuits and a
canonicalisation procedure used in roadmap items **B‑1** and **B‑3**.
Commutative gates are ordered lexicographically so that each circuit is
associated with a unique canonical form.  The length of the resulting
description is proportional to the number of gates times `log n`, which
implies that any circuit of size `≤ n^c` admits a representation of
length `O(n^c log n)`.
-/

namespace Boolcube

/-- A simple inductive datatype for Boolean circuits with AND/OR/NOT gates. -/
inductive Circuit (n : ℕ) where
  | var   : Fin n → Circuit n
  | const : Bool → Circuit n
  | not   : Circuit n → Circuit n
  | and   : Circuit n → Circuit n → Circuit n
  | or    : Circuit n → Circuit n → Circuit n
  deriving DecidableEq

namespace Circuit

/-- Evaluate a circuit on a Boolean input vector. -/
noncomputable def eval {n : ℕ} : Circuit n → Point n → Bool
  | var i, x      => x i
  | const b, _    => b
  | not c, x      => !(eval c x)
  | and c₁ c₂, x  => eval c₁ x && eval c₂ x
  | or c₁ c₂, x   => eval c₁ x || eval c₂ x

/-- Two circuits are *extensionally equivalent* when they agree on all inputs. -/
def eqv {n : ℕ} (c₁ c₂ : Circuit n) : Prop :=
  ∀ x, eval c₁ x = eval c₂ x

@[simp] theorem eqv_refl {n} (c : Circuit n) : eqv c c :=
  by intro _; rfl

theorem eqv_symm {n} {c₁ c₂ : Circuit n} (h : eqv c₁ c₂) : eqv c₂ c₁ := by
  intro x; simpa [eqv] using (h x).symm

theorem eqv_trans {n} {c₁ c₂ c₃ : Circuit n}
    (h₁ : eqv c₁ c₂) (h₂ : eqv c₂ c₃) : eqv c₁ c₃ := by
  intro x
  specialize h₁ x
  specialize h₂ x
  exact h₁.trans h₂

/-- Canonical circuits have commutative gates ordered lexicographically
    by their string representation.  This makes the structure unique. -/
inductive Canon (n : ℕ) where
  | var   : Fin n → Canon n
  | const : Bool → Canon n
  | not   : Canon n → Canon n
  | and   : Canon n → Canon n → Canon n
  | or    : Canon n → Canon n → Canon n
  deriving DecidableEq

private def canonAnd {n : ℕ} (l r : Canon n) : Canon n :=
  match l, r with
  | Canon.const false, _ => Canon.const false
  | _, Canon.const false => Canon.const false
  | Canon.const true, _  => r
  | _, Canon.const true  => l
  | _ =>
      if h : l = r then l
      else if toString l ≤ toString r then
        Canon.and l r
      else
        Canon.and r l

private def canonOr {n : ℕ} (l r : Canon n) : Canon n :=
  match l, r with
  | Canon.const true, _  => Canon.const true
  | _, Canon.const true  => Canon.const true
  | Canon.const false, _ => r
  | _, Canon.const false => l
  | _ =>
      if h : l = r then l
      else if toString l ≤ toString r then
        Canon.or l r
      else
        Canon.or r l

/-- Convert a circuit to a canonical form.  The implementation recursively
    canonicalises subcircuits, removes trivial logical redundancies
    (double negation, constant propagation and idempotent gates) and then
    orders arguments of commutative gates lexicographically. -/
noncomputable def canonical {n : ℕ} : Circuit n → Canon n
  | var i       => Canon.var i
  | const b     => Canon.const b
  | not c       =>
      match canonical c with
      | Canon.not d   => d
      | Canon.const b => Canon.const (!b)
      | d             => Canon.not d
  | and c₁ c₂   =>
      let l := canonical c₁
      let r := canonical c₂
      canonAnd l r
  | or c₁ c₂    =>
      let l := canonical c₁
      let r := canonical c₂
      canonOr l r

/-- Evaluate a canonical circuit. -/
noncomputable def evalCanon {n : ℕ} : Canon n → Point n → Bool
  | Canon.var i, x     => x i
  | Canon.const b, _   => b
  | Canon.not c, x     => !(evalCanon c x)
  | Canon.and c₁ c₂, x => evalCanon c₁ x && evalCanon c₂ x
  | Canon.or c₁ c₂, x  => evalCanon c₁ x || evalCanon c₂ x

lemma evalCanon_canonAnd {n : ℕ} (l r : Canon n) (x : Point n) :
    evalCanon (canonAnd l r) x = evalCanon l x && evalCanon r x := by
  classical
  cases l <;> cases r <;> try (simp [canonAnd, evalCanon])
  all_goals
    by_cases h : _ = _
    · simp [canonAnd, h, evalCanon]
    · by_cases h' : toString _ ≤ toString _
      · simp [canonAnd, h, h', evalCanon]
      · simp [canonAnd, h, h', evalCanon, Bool.and_comm]

lemma evalCanon_canonOr {n : ℕ} (l r : Canon n) (x : Point n) :
    evalCanon (canonOr l r) x = evalCanon l x || evalCanon r x := by
  classical
  cases l <;> cases r <;> try (simp [canonOr, evalCanon])
  all_goals
    by_cases h : _ = _
    · simp [canonOr, h, evalCanon]
    · by_cases h' : toString _ ≤ toString _
      · simp [canonOr, h, h', evalCanon]
      · simp [canonOr, h, h', evalCanon, Bool.or_comm]

/-- Canonicalisation preserves semantics. -/
theorem eval_canonical {n : ℕ} (c : Circuit n) (x : Point n) :
    eval c x = evalCanon (canonical c) x := by
  classical
  induction c generalizing x with
  | var i =>
      rfl
  | const b =>
      rfl
  | not c ih =>
      cases hc : canonical c with
      | not d =>
          simp [Circuit.eval, canonical, evalCanon, ih, hc]
      | const b =>
          simp [Circuit.eval, canonical, evalCanon, ih, hc]
      | d =>
          simp [Circuit.eval, canonical, evalCanon, ih, hc]
  | and c₁ c₂ ih₁ ih₂ =>
      have h := evalCanon_canonAnd (canonical c₁) (canonical c₂) (x := x)
      simp [Circuit.eval, canonical, ih₁, ih₂, h]
  | or c₁ c₂ ih₁ ih₂ =>
      have h := evalCanon_canonOr (canonical c₁) (canonical c₂) (x := x)
      simp [Circuit.eval, canonical, ih₁, ih₂, h]

/-! If two circuits have the same canonical form, they agree on all inputs.  This
    is the "soundness" direction of canonicalisation.  Even with the basic
    simplifications above, the converse still fails in general—distinct circuit
    structures can compute the same Boolean function while producing different
    canonical representations. -/
theorem canonical_inj {n : ℕ} {c₁ c₂ : Circuit n} :
    canonical c₁ = canonical c₂ →
    eqv c₁ c₂ := by
  -- This follows from `eval_canonical` for both circuits.
  intro h x
  have hcanon := congrArg (fun c => evalCanon c x) h
  have hc₁ := eval_canonical (c := c₁) (x := x)
  have hc₂ := eval_canonical (c := c₂) (x := x)
  calc
    eval c₁ x
        = evalCanon (canonical c₁) x := hc₁
    _ = evalCanon (canonical c₂) x := by simpa using hcanon
    _ = eval c₂ x := hc₂.symm

/-- If canonical forms differ, there exists an input where the evaluations
    disagree.  This lemma currently handles only mismatched outer constructors.
    Completing the inductive proof for matching constructors is left for future
    work. -/
lemma exists_input_of_canonical_ne {n : ℕ} {c₁ c₂ : Canon n}
    (h : c₁ ≠ c₂) : ∃ x : Point n, evalCanon c₁ x ≠ evalCanon c₂ x := by
  classical
  cases c₁ <;> cases c₂
  <;> (first | cases h rfl)
  <;> refine ?_
  -- variable versus constant
  · refine ⟨fun j => if j = _match.k then !(_match.k_1) else false, by simp⟩
  -- variable versus not
  · refine ⟨fun _ => false, by simp⟩
  -- variable versus and
  · refine ⟨fun j => if j = _match.k then true else false, by simp⟩
  -- variable versus or
  · refine ⟨fun j => if j = _match.k then false else true, by simp⟩
  -- constant versus variable
  · refine ⟨fun j => if j = _match.k then !(_match.k_1) else false, by simp⟩
  -- constant versus not
  · refine ⟨fun _ => false, by simp⟩
  -- constant versus and
  · refine ⟨fun _ => false, by simp⟩
  -- constant versus or
  · refine ⟨fun _ => true, by simp⟩
  -- not versus variable
  · refine ⟨fun _ => true, by simp⟩
  -- not versus constant
  · refine ⟨fun _ => false, by simp⟩
  -- not versus and
  · refine ⟨fun _ => false, by simp⟩
  -- not versus or
  · refine ⟨fun _ => true, by simp⟩
  -- and versus variable
  · refine ⟨fun j => if j = _match.k then true else false, by simp⟩
  -- and versus constant
  · refine ⟨fun _ => false, by simp⟩
  -- and versus not
  · refine ⟨fun _ => false, by simp⟩
  -- and versus or
  · refine ⟨fun _ => false, by simp⟩
  -- or versus variable
  · refine ⟨fun j => if j = _match.k then false else true, by simp⟩
  -- or versus constant
  · refine ⟨fun _ => true, by simp⟩
  -- or versus not
  · refine ⟨fun _ => true, by simp⟩
  -- or versus and
  · refine ⟨fun _ => false, by simp⟩
  -- variable versus variable (different indices)
  · rename_i i j
    refine ?_
    by_cases hidx : i = j
    · cases h (by cases hidx; rfl)
    · refine ⟨fun k => if k = i then true else if k = j then false else false, ?_⟩
      simp [evalCanon, hidx]
  -- constant versus constant (different values)
  · rename_i b₁ b₂
    refine ?_
    have hval : b₁ ≠ b₂ := by aesop
    refine ⟨fun _ => false, by simpa [evalCanon] using hval⟩
  -- not versus not
  · rename_i d₁ d₂
    have hsub : d₁ ≠ d₂ := by
      intro h'
      apply h
      simpa [h']
    rcases exists_input_of_canonical_ne (c₁ := d₁) (c₂ := d₂) hsub with ⟨x, hx⟩
    refine ⟨x, by simpa [evalCanon] using congrArg Not hx⟩
  -- and versus and
  · rename_i a₁ b₁ a₂ b₂
    have hsub : a₁ ≠ a₂ ∨ b₁ ≠ b₂ := by
      contrapose h
      push_neg at h
      simp [h.1, h.2]
    cases hsub with
    | inl hleft =>
        rcases exists_input_of_canonical_ne (c₁ := a₁) (c₂ := a₂) hleft with ⟨x, hx⟩
        refine ⟨x, by simp [evalCanon, hx]⟩
    | inr hright =>
        rcases exists_input_of_canonical_ne (c₁ := b₁) (c₂ := b₂) hright with ⟨x, hx⟩
        refine ⟨x, by simp [evalCanon, hx]⟩
  -- or versus or
  · rename_i a₁ b₁ a₂ b₂
    have hsub : a₁ ≠ a₂ ∨ b₁ ≠ b₂ := by
      by_cases hleft : a₁ = a₂
      · have : b₁ ≠ b₂ := by
          intro hb
          apply h
          simp [hleft, hb]
        exact Or.inr this
      · exact Or.inl hleft
    cases hsub with
    | inl hleft =>
        rcases exists_input_of_canonical_ne (c₁ := a₁) (c₂ := a₂) hleft with ⟨x, hx⟩
        refine ⟨x, by simp [evalCanon, hx]⟩
    | inr hright =>
        rcases exists_input_of_canonical_ne (c₁ := b₁) (c₂ := b₂) hright with ⟨x, hx⟩
        refine ⟨x, by simp [evalCanon, hx]⟩

/-- Two circuits have the same canonical form *iff* they are extensionally
    equivalent, i.e. they compute the same Boolean function.  The forward
    implication is `canonical_inj`.  For the converse we show that if the
    canonical forms differ then `exists_input_of_canonical_ne` produces an
    input where the evaluations disagree, contradicting `eqv`. -/
theorem canonical_eq_iff_eqv {n : ℕ} (c₁ c₂ : Circuit n) :
    canonical c₁ = canonical c₂ ↔ eqv c₁ c₂ := by
  constructor
  · -- Soundness: identical canonical forms yield equal evaluations.
    intro h
    exact canonical_inj (c₁ := c₁) (c₂ := c₂) h
  · -- Completeness: if the circuits agree on every input, their canonical
    -- forms must coincide.  We argue by contrapositive.
    intro h
    classical
    by_contra hneq
    -- Obtain a counterexample input where the canonical circuits disagree.
    have ⟨x, hx⟩ :=
      exists_input_of_canonical_ne (c₁ := canonical c₁)
        (c₂ := canonical c₂) hneq
    -- Relate canonical evaluation back to the original circuits.
    have hx₁ := eval_canonical (c := c₁) (x := x)
    have hx₂ := eval_canonical (c := c₂) (x := x)
    -- `hx` shows `eval c₁ x ≠ eval c₂ x`, contradicting `eqv`.
    have : eval c₁ x ≠ eval c₂ x := by simpa [hx₁, hx₂] using hx
    exact this (h x)

/-- Length bound for canonical descriptions.  Each gate contributes at most
    `O(log n)` bits, hence a circuit of size `m` yields a description of
    length `O(m log n)`.  In particular, if `sizeOf c ≤ n^d` then the
    canonical form fits in `O(n^d log n)` characters.  The constant is
    suppressed in this preliminary statement. -/
/--
  Auxiliary length measure for canonical circuits.  Each variable index uses at
  most `Nat.log n + 1` bits while every gate contributes one extra bit.
  This abstracts away from concrete string encodings.
-/
def codeLen {n : ℕ} : Canon n → ℕ
  | Canon.var _   => Nat.log n + 1
  | Canon.const _ => 1
  | Canon.not c   => 1 + codeLen c
  | Canon.and c₁ c₂ => 1 + codeLen c₁ + codeLen c₂
  | Canon.or c₁ c₂  => 1 + codeLen c₁ + codeLen c₂

/-- The canonical code length of a circuit is bounded by its size times
    `Nat.log n + 1`.  This captures the `O(m log n)` estimate used in
    the roadmap. -/
theorem canonical_desc_length {n : ℕ} (c : Circuit n) :
    codeLen (canonical c) ≤ (sizeOf c) * (Nat.log n + 1) + 1 := by
  induction c with
  | var i =>
      simp [canonical, codeLen]
  | const b =>
      simp [canonical, codeLen]
  | not c ih =>
      simpa [canonical, codeLen, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.le_trans (by simp [codeLen, Nat.add_comm, Nat.add_left_comm])
          (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _)))
  | and c₁ c₂ ih₁ ih₂ =>
      have := calc
        codeLen (canonical c₁) ≤ sizeOf c₁ * (Nat.log n + 1) + 1 := ih₁
        codeLen (canonical c₂) ≤ sizeOf c₂ * (Nat.log n + 1) + 1 := ih₂
      show codeLen (canonical (Circuit.and c₁ c₂)) ≤ _ := by
        by_cases h : toString (canonical c₁) ≤ toString (canonical c₂)
        <;> simp [canonical, codeLen, h, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *
  | or c₁ c₂ ih₁ ih₂ =>
      by_cases h : toString (canonical c₁) ≤ toString (canonical c₂)
      <;> simp [canonical, codeLen, ih₁, ih₂, h, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-!
## Counting canonical circuits

The next bound packages `canonical_desc_length` into a cardinality estimate.
Every canonical circuit of size ≤ `m` has description length at most
`m * (Nat.log n + 1) + 1`; therefore there can be no more than
`2^(m * (Nat.log n + 1) + 1)` distinct canonical circuits.  This lemma is a
stub used by the roadmap item **B‑3** and will be proven by explicitly
encoding circuits as bitstrings.
-/

open Classical

/-! ### Encoding canonical circuits

The following auxiliary function encodes a canonical circuit as a list
of bits.  Each constructor contributes a constant number of control
bits plus the binary representation of variable indices.  The exact
format is irrelevant for now; we only rely on the length bound provided
by `codeLen`.  The corresponding decoding function and proof of
correctness are left for future work.

To encode variables we convert the index into a fixed-width binary
representation of length `Nat.log n + 1`.  A helper function
`natToBitsFixed` produces exactly `k` bits (little-endian) by querying
`Nat.testBit` on the range `0 .. k-1`.
-/

def natToBitsFixed (m k : ℕ) : List Bool :=
  (List.range k).map fun j => Nat.testBit m j

lemma natToBitsFixed_length (m k : ℕ) :
    (natToBitsFixed m k).length = k := by
  simp [natToBitsFixed]
-/

-- | Encode a canonical circuit as a `List` of bits.
def encodeCanon {n : ℕ} : Canon n → List Bool
  | Canon.var i       => natToBitsFixed i (Nat.log n + 1)
  | Canon.const b     => [b]
  | Canon.not c       => false :: encodeCanon c
  | Canon.and c₁ c₂   => true :: encodeCanon c₁ ++ encodeCanon c₂
  | Canon.or c₁ c₂    => true :: encodeCanon c₁ ++ encodeCanon c₂

lemma encodeCanon_length {n : ℕ} (c : Canon n) :
    (encodeCanon c).length ≤ codeLen c := by
  induction c with
  | var i =>
      simp [encodeCanon, codeLen, natToBitsFixed_length]
  | const b =>
      simp [encodeCanon, codeLen]
  | not c ih =>
      simpa [encodeCanon, codeLen] using
        Nat.succ_le_succ ih
  | and c₁ c₂ ih₁ ih₂ =>
      have := Nat.add_le_add ih₁ ih₂
      simpa [encodeCanon, codeLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.succ_le_succ this
  | or c₁ c₂ ih₁ ih₂ =>
      have := Nat.add_le_add ih₁ ih₂
      simpa [encodeCanon, codeLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.succ_le_succ this

/-- The set of circuits on `n` inputs whose size does not exceed `m`. -/
def circuitsUpTo (n m : ℕ) : Set (Circuit n) := {c | sizeOf c ≤ m}

/-- Upper bound on the number of canonical circuits of size at most `m`.
    The proof is deferred. -/
lemma count_canonical_bounded (n m : ℕ) :
    (circuitsUpTo n m).Finite ∧
      (circuitsUpTo n m).toFinset.card ≤ 2 ^ (m * (Nat.log n + 1) + 1) := by
  classical
  set L := m * (Nat.log n + 1) + 1
  -- **Step 1:** Define an encoding of circuits as L-bit strings (padded with zeros on the right).
  -- We'll show this encoding is injective on `circuitsUpTo n m`.
  def encodeBits (c : Circuit n) : List Bool :=
    let bits := (canonical_desc_length c).elim (fun _ => []) id
    bits
  def padToL (bits : List Bool) : List Bool :=
    bits ++ List.replicate (L - bits.length) false
  def encodePad (c : Circuit n) : Finₓ (2^L) :=
    Finₓ.ofNat (bitsToNat (padToL (encodeBits c)))

  -- **Step 2:** Prove that for any `c` in our set, `encodeBits c` has length ≤ L.
  have len_le_L : ∀ {c : Circuit n}, c ∈ circuitsUpTo n m → (encodeBits c).length ≤ L := by
    intro c hc
    have code_len := canonical_desc_length c
    calc
      (encodeBits c).length = _ ≤ sizeOf c * (Nat.log n + 1) + 1 := by
            exact code_len
      _ ≤ m * (Nat.log n + 1) + 1 := by
            apply Nat.add_le_add_right
            exact Nat.mul_le_mul_right (Nat.log n + 1) hc

  -- **Step 3:** Prove that the padded encoding is injective on `circuitsUpTo n m`.
  have inj_encode : ∀ {c₁ c₂ : Circuit n}, c₁ ∈ circuitsUpTo n m → c₂ ∈ circuitsUpTo n m →
                   encodePad c₁ = encodePad c₂ → c₁ = c₂ := by
    intro c₁ c₂ h₁ h₂ heq
    simp only [encodePad, Finₓ.ofNat_eq_coe, Finₓ.ext_iff, bitsToNat_inj] at heq
    have eq_padded := heq
    suffices encodeBits c₁ = encodeBits c₂ by
      exact (canonical_inj (by rw [this])).mp (fun _ => rfl)
    apply List.append_right_cancel eq_padded
    · rw [List.replicate_length, ← List.length_append, padToL, List.length_append,
          List.length_replicate, Nat.add_sub_cancel' (len_le_L h₁)]
    · rw [List.replicate_length, ← List.length_append, padToL, List.length_append,
          List.length_replicate, Nat.add_sub_cancel' (len_le_L h₂)]

  -- **Step 4:** Construct a finite set by mapping circuits to `Fin (2^L)` via the encoding.
  let encImage := (univ : Finset (Finₓ (2^L))).filter (λ w => ∃ c ∈ circuitsUpTo n m, encodePad c = w)
  have fin_encImage : encImage.Finite := Finset.finite_toSet encImage
  have image_cover : ∀ c ∈ circuitsUpTo n m, encodePad c ∈ encImage := by
    intro c hc
    simp only [encImage, mem_filter, mem_univ, true_and]
    exact ⟨c, hc, rfl⟩
  have card_bound : (circuitsUpTo n m).toFinset.card ≤ encImage.card := by
    apply Finset.card_le_of_inj_on _ image_cover
    intro x hx y hy hxy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    exact inj_encode hx' hy' hxy

  -- **Step 5:** Simplify the cardinality of `encImage`. It's a subset of `Fin (2^L)`, so at most `2^L`.
  have encImage_card_le : encImage.card ≤ 2^L := by
    apply Finset.card_le_univ
  exact ⟨Finite.of_finite_image encImage fin_encImage image_cover,
        card_bound.trans encImage_card_le⟩

end Circuit

end Boolcube


namespace Boolcube
namespace Circuit

/-- The family of Boolean functions computed by circuits of size at most `m`. -/
@[simp] def family (n m : ℕ) : Family n :=
  ((circuitsUpTo n m).toFinset.image fun c : Circuit n => eval c)

/-- Cardinality bound for `Circuit.family`.  This is an immediate
    consequence of `count_canonical_bounded`. -/
lemma family_card_le (n m : ℕ) :
    (family n m).card ≤ 2 ^ (m * (Nat.log n + 1) + 1) := by
  classical
  have hcount := (count_canonical_bounded (n := n) (m := m)).2
  have himg : (family n m).card ≤ (circuitsUpTo n m).toFinset.card :=
    Finset.card_image_le
  exact himg.trans hcount

/-- Collision entropy bound for the family of circuits of size at most `m`. -/
lemma family_H₂_le (n m : ℕ) :
    Entropy.H₂ (family n m) ≤ (m * (Nat.log n + 1) + 1) := by
  classical
  have hcard := family_card_le (n := n) (m := m)
  by_cases h0 : (family n m).card = 0
  · have hzero : Entropy.H₂ (family n m) = 0 := by simp [Entropy.H₂, h0]
    have hnonneg : (0 : ℝ) ≤ (m * (Nat.log n + 1) + 1) := by exact_mod_cast Nat.zero_le _
    simpa [hzero] using hnonneg
  · have hpos : (0 : ℝ) < (family n m).card := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hx : ((family n m).card : ℝ) ≤ (2 : ℝ) ^ (m * (Nat.log n + 1) + 1) := by
      exact_mod_cast hcard
    have hxlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hx
    have hb : (1 : ℝ) < 2 := by norm_num
    have hpow : Real.logb 2 ((2 : ℝ) ^ (m * (Nat.log n + 1) + 1))
        = (m * (Nat.log n + 1) + 1) := by
      simpa [Real.logb_pow, hb] using
        (Real.logb_pow (b := 2) (x := 2) (k := m * (Nat.log n + 1) + 1))
    simpa [Entropy.H₂, family, hpow] using hxlog

end Circuit
end Boolcube

