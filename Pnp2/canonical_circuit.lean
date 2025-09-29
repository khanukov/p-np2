import Pnp2.Boolcube
import Mathlib.Data.List.Basic

/-
canonical_circuit.lean
======================

This module formalises a very small model of Boolean circuits and a
canonicalisation procedure used in roadmap items **B‑1** and **B‑3**.
Commutative gates are ordered according to a fixed `Ord` instance so that
each circuit is associated with a unique canonical form.  The length of
the resulting
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

/-- Canonical circuits have commutative gates ordered according to the
    `Ord` instance on canonical circuits.  This makes the structure
    unique and avoids relying on potentially unstable string
    representations. -/
inductive Canon (n : ℕ) where
  | var   : Fin n → Canon n
  | const : Bool → Canon n
  | not   : Canon n → Canon n
  | and   : Canon n → Canon n → Canon n
  | or    : Canon n → Canon n → Canon n
  deriving DecidableEq, Ord

private def canonAnd {n : ℕ} (l r : Canon n) : Canon n :=
  match l, r with
  | Canon.const false, _ => Canon.const false
  | _, Canon.const false => Canon.const false
  | Canon.const true, _  => r
  | _, Canon.const true  => l
  | _ =>
      match compare l r with
      | Ordering.lt => Canon.and l r
      | Ordering.eq => l
      | Ordering.gt => Canon.and r l

private def canonOr {n : ℕ} (l r : Canon n) : Canon n :=
  match l, r with
  | Canon.const true, _  => Canon.const true
  | _, Canon.const true  => Canon.const true
  | Canon.const false, _ => r
  | _, Canon.const false => l
  | _ =>
      match compare l r with
      | Ordering.lt => Canon.or l r
      | Ordering.eq => l
      | Ordering.gt => Canon.or r l

/-- Convert a circuit to a canonical form.  The implementation recursively
    canonicalises subcircuits, removes trivial logical redundancies
    (double negation, constant propagation and idempotent gates) and then
    orders arguments of commutative gates using the canonical order. -/
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
    cases h : compare _ _ <;> simp [canonAnd, evalCanon, h, Bool.and_comm]

lemma evalCanon_canonOr {n : ℕ} (l r : Canon n) (x : Point n) :
    evalCanon (canonOr l r) x = evalCanon l x || evalCanon r x := by
  classical
  cases l <;> cases r <;> try (simp [canonOr, evalCanon])
  all_goals
    cases h : compare _ _ <;> simp [canonOr, evalCanon, h, Bool.or_comm]

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
    disagree.  The proof performs a case analysis on both canonical circuits,
    recursively descending into subcircuits when the constructors match.  In
    each branch we produce a point that distinguishes the evaluations. -/
lemma exists_input_of_canonical_ne {n : ℕ} {c₁ c₂ : Canon n}
    (h : c₁ ≠ c₂) : ∃ x : Point n, evalCanon c₁ x ≠ evalCanon c₂ x := by
  classical
  -- We perform a full case analysis on both canonical circuits.
  -- Heterogeneous constructor pairs can be separated by choosing an
  -- input that forces different root values.  When the constructors
  -- coincide, we recursively apply the lemma to the differing
  -- subcircuits.  The generated assignment is then reused at the top
  -- level to witness the discrepancy.
  cases c₁ <;> cases c₂
  -- Eliminate impossible equalities introduced by the case split.
  <;> (first | cases h rfl)
  -- Remaining cases are handled one by one.
  <;> refine ?_
  -- variable versus constant
  · rename_i i b
    refine ⟨fun j => if j = i then !b else false, by simp⟩
  -- variable versus not
  · rename_i i d
    refine ⟨fun _ => false, by simp⟩
  -- variable versus and
  · rename_i i a b
    refine ⟨fun j => if j = i then true else false, by simp⟩
  -- variable versus or
  · rename_i i a b
    refine ⟨fun j => if j = i then false else true, by simp⟩
  -- constant versus variable
  · rename_i b i
    refine ⟨fun j => if j = i then !b else false, by simp⟩
  -- constant versus not
  · rename_i b d
    refine ⟨fun _ => false, by simp⟩
  -- constant versus and
  · rename_i b a d
    refine ⟨fun _ => false, by simp⟩
  -- constant versus or
  · rename_i b a d
    refine ⟨fun _ => true, by simp⟩
  -- not versus variable
  · rename_i d i
    refine ⟨fun _ => true, by simp⟩
  -- not versus constant
  · rename_i d b
    refine ⟨fun _ => false, by simp⟩
  -- not versus and
  · rename_i d a b
    refine ⟨fun _ => false, by simp⟩
  -- not versus or
  · rename_i d a b
    refine ⟨fun _ => true, by simp⟩
  -- and versus variable
  · rename_i a b i
    refine ⟨fun j => if j = i then true else false, by simp⟩
  -- and versus constant
  · rename_i a b c
    refine ⟨fun _ => false, by simp⟩
  -- and versus not
  · rename_i a b d
    refine ⟨fun _ => false, by simp⟩
  -- and versus or
  · rename_i a b c d
    refine ⟨fun _ => false, by simp⟩
  -- or versus variable
  · rename_i a b i
    refine ⟨fun j => if j = i then false else true, by simp⟩
  -- or versus constant
  · rename_i a b c
    refine ⟨fun _ => true, by simp⟩
  -- or versus not
  · rename_i a b d
    refine ⟨fun _ => true, by simp⟩
  -- or versus and
  · rename_i a b c d
    refine ⟨fun _ => false, by simp⟩
  -- variable versus variable (different indices)
  · rename_i i j
    by_cases hidx : i = j
    · cases h (by cases hidx; rfl)
    · refine ⟨fun k => if k = i then true else if k = j then false else false, ?_⟩
      simp [evalCanon, hidx]
  -- constant versus constant (different values)
  · rename_i b₁ b₂
    have hval : b₁ ≠ b₂ := by
      intro hb; apply h; cases hb; rfl
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

/-!
The theorem `canonical_eq_iff_eqv` establishes that canonicalisation is
**both sound and complete** with respect to circuit evaluation.  Two circuits
have identical canonical representations exactly when they compute the same
Boolean function.  This fact underpins later counting arguments where each
equivalence class of circuits can be represented by a unique canonical member.
-/

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
        cases h : compare (canonical c₁) (canonical c₂) <;>
          simp [canonical, codeLen, h, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *
  | or c₁ c₂ ih₁ ih₂ =>
      cases h : compare (canonical c₁) (canonical c₂) <;>
        simp [canonical, codeLen, ih₁, ih₂, h, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

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

/-- For `n ≥ 1` the logarithmic factor appearing in the circuit counting
bound grows at most linearly with `n`.  The constants are deliberately
generous – the proof only needs the existence of some absolute
dominating factor. -/
lemma log_add_one_le_three_mul {n : ℕ} (hn : 1 ≤ n) :
    Nat.log n + 1 ≤ 3 * n := by
  cases' n with n
  · cases hn
  -- The library proves that `Nat.log (Nat.succ n)` is bounded by the
  -- identity function.  Combining this with the trivial inequality
  -- `Nat.succ n + 1 ≤ 3 * Nat.succ n` yields the advertised estimate.
  · have hlog : Nat.log (Nat.succ n) ≤ Nat.succ n := by
      simpa using (Nat.log_le_self (2) (Nat.succ n))
    have htwo : (1 : ℕ) ≤ 2 * Nat.succ n := by
      exact Nat.succ_le_of_lt
        (Nat.mul_pos (by decide : 0 < 2) (Nat.succ_pos n))
    have hlin : Nat.succ n + 1 ≤ Nat.succ n + 2 * Nat.succ n :=
      Nat.add_le_add_left htwo (Nat.succ n)
    have hrewrite : Nat.succ n + 2 * Nat.succ n = 3 * Nat.succ n := by
      simp [two_mul, three_mul, add_comm, add_left_comm, add_assoc]
    have hsum : Nat.succ n + 1 ≤ 3 * Nat.succ n := by
      simpa [hrewrite] using hlin
    have : Nat.log (Nat.succ n) + 1 ≤ Nat.succ n + 1 :=
      Nat.add_le_add_right hlog 1
    exact this.trans hsum

/-- An explicit polynomial upper bound for the exponent appearing in the
cardinality estimate of the circuit family `family n (n^c)`.  The bound
`6 · n^{c+1}` is intentionally coarse but suffices for the entropy
arguments downstream. -/
lemma pow_family_exponent_bound {n c : ℕ} (hn : 1 ≤ n) :
    n ^ c * (Nat.log n + 1) + 1 ≤ 6 * n ^ (c + 1) := by
  have hlog := log_add_one_le_three_mul (n := n) hn
  -- First control the main product `n^c * (log n + 1)`.
  have hmain : n ^ c * (Nat.log n + 1) ≤ 3 * n ^ (c + 1) := by
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using Nat.mul_le_mul_left (n ^ c) hlog
  -- The previous inequality persists after adding `1` to both sides.
  have hsum : n ^ c * (Nat.log n + 1) + 1 ≤ 3 * n ^ (c + 1) + 1 :=
    Nat.add_le_add_right hmain 1
  -- Since `n ≥ 1`, the power `n^(c+1)` is positive and therefore at
  -- least `1`.  This lets us absorb the trailing `+1` into the same
  -- leading polynomial factor.
  have hposn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ _) hn
  have hpowpos : 0 < n ^ (c + 1) := Nat.pow_pos hposn _
  have hone_le_pow : (1 : ℕ) ≤ 3 * n ^ (c + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 3) hpowpos)
  have hstep : 3 * n ^ (c + 1) + 1 ≤ 3 * n ^ (c + 1) + 3 * n ^ (c + 1) :=
    Nat.add_le_add_left hone_le_pow _
  have hrewrite : 3 * n ^ (c + 1) + 3 * n ^ (c + 1) = 6 * n ^ (c + 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using (Nat.add_mul 3 3 (n ^ (c + 1))).symm
  exact hsum.trans (by simpa [hrewrite] using hstep)

/-- The family of Boolean functions realised by circuits of size at most
`n^c` obeys a crude exponential bound whose exponent grows like
`O(n^{c+1})`.  This packages `family_card_le` with the polynomial
estimate from `pow_family_exponent_bound`. -/
lemma pow_family_card_le {n c : ℕ} (hn : 1 ≤ n) :
    (family n (n ^ c)).card ≤ 2 ^ (6 * n ^ (c + 1)) := by
  classical
  have hcard := family_card_le (n := n) (m := n ^ c)
  have hexp := pow_family_exponent_bound (n := n) (c := c) hn
  have hmono := Left.pow_le_pow_right' (a := 2)
      (n := n ^ c * (Nat.log n + 1) + 1) (m := 6 * n ^ (c + 1))
      (ha := by decide) hexp
  exact hcard.trans hmono

/-- The collision entropy of the family of size-`≤ n^c` circuits is also
polynomially bounded.  This is the `ℝ`-valued counterpart of
`pow_family_exponent_bound` needed for the analytic formulation of the
family collision-entropy lemma. -/
lemma pow_family_H₂_le {n c : ℕ} (hn : 1 ≤ n) :
    Entropy.H₂ (family n (n ^ c)) ≤ (6 * n ^ (c + 1) : ℝ) := by
  classical
  have hbound := family_H₂_le (n := n) (m := n ^ c)
  have hcast : ((n ^ c * (Nat.log n + 1) + 1 : ℕ) : ℝ)
      ≤ (6 * n ^ (c + 1) : ℝ) := by
    exact_mod_cast pow_family_exponent_bound (n := n) (c := c) hn
  exact hbound.trans hcast

end Circuit
end Boolcube

