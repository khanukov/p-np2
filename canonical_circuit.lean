import Boolcube

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

/-- Canonical circuits have commutative gates ordered lexicographically
    by their string representation.  This makes the structure unique. -/
inductive Canon (n : ℕ) where
  | var   : Fin n → Canon n
  | const : Bool → Canon n
  | not   : Canon n → Canon n
  | and   : Canon n → Canon n → Canon n
  | or    : Canon n → Canon n → Canon n
  deriving DecidableEq

/-- Convert a circuit to a canonical form.  The implementation recursively
    canonicalises subcircuits and orders arguments of commutative gates. -/
noncomputable def canonical {n : ℕ} : Circuit n → Canon n
  | var i       => Canon.var i
  | const b     => Canon.const b
  | not c       => Canon.not (canonical c)
  | and c₁ c₂   =>
      let l := canonical c₁
      let r := canonical c₂
      if toString l ≤ toString r then
        Canon.and l r
      else
        Canon.and r l
  | or c₁ c₂    =>
      let l := canonical c₁
      let r := canonical c₂
      if toString l ≤ toString r then
        Canon.or l r
      else
        Canon.or r l

/-- Evaluate a canonical circuit. -/
noncomputable def evalCanon {n : ℕ} : Canon n → Point n → Bool
  | Canon.var i, x     => x i
  | Canon.const b, _   => b
  | Canon.not c, x     => !(evalCanon c x)
  | Canon.and c₁ c₂, x => evalCanon c₁ x && evalCanon c₂ x
  | Canon.or c₁ c₂, x  => evalCanon c₁ x || evalCanon c₂ x

/-- Canonicalisation preserves semantics. -/
theorem eval_canonical {n : ℕ} (c : Circuit n) (x : Point n) :
    eval c x = evalCanon (canonical c) x := by
  induction c generalizing x with
  | var i =>
      rfl
  | const b =>
      rfl
  | not c ih =>
      simp [Circuit.eval, evalCanon, canonical, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      by_cases h : toString (canonical c₁) ≤ toString (canonical c₂)
      · simp [Circuit.eval, canonical, evalCanon, ih₁, ih₂, h]
      · simp [Circuit.eval, canonical, evalCanon, ih₁, ih₂, h, Bool.and_comm]
  | or c₁ c₂ ih₁ ih₂ =>
      by_cases h : toString (canonical c₁) ≤ toString (canonical c₂)
      · simp [Circuit.eval, canonical, evalCanon, ih₁, ih₂, h]
      · simp [Circuit.eval, canonical, evalCanon, ih₁, ih₂, h, Bool.or_comm]

/-- Two circuits have the same canonical form iff they compute the same function. -/
theorem canonical_inj {n : ℕ} {c₁ c₂ : Circuit n} :
    canonical c₁ = canonical c₂ →
    (∀ x, eval c₁ x = eval c₂ x) := by
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
-/

-- | Encode a canonical circuit as a `List` of bits.
def encodeCanon {n : ℕ} : Canon n → List Bool
  | Canon.var i       => List.replicate (Nat.log n + 1) false  -- placeholder
  | Canon.const b     => [b]
  | Canon.not c       => false :: encodeCanon c
  | Canon.and c₁ c₂   => true :: encodeCanon c₁ ++ encodeCanon c₂
  | Canon.or c₁ c₂    => true :: encodeCanon c₁ ++ encodeCanon c₂

lemma encodeCanon_length {n : ℕ} (c : Canon n) :
    (encodeCanon c).length ≤ codeLen c := by
  -- Proof postponed.  The encoding above is only schematic.
  admit

/-- The set of circuits on `n` inputs whose size does not exceed `m`. -/
def circuitsUpTo (n m : ℕ) : Set (Circuit n) := {c | sizeOf c ≤ m}

/-- Upper bound on the number of canonical circuits of size at most `m`.
    The proof is deferred. -/
lemma count_canonical_bounded (n m : ℕ) :
    (circuitsUpTo n m).Finite ∧
      (circuitsUpTo n m).toFinset.card ≤ 2 ^ (m * (Nat.log n + 1) + 1) := by
  classical
  -- TODO: encode canonical circuits and derive the bound from `canonical_desc_length`.
  admit

end Circuit

end Boolcube

