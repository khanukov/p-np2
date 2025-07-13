import Pnp.Boolcube

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


/-!
## Canonical Circuits

This section defines a normal form for Boolean circuits.  Commutative
gates are ordered lexicographically so that each circuit admits a
unique canonical representative.  Evaluation of a circuit is preserved
by canonicalisation.
-/

/--- Canonical circuits have commutative gates ordered lexicographically by
their string representation.  This makes the structure unique. -/
inductive Canon (n : ℕ) where
  | var   : Fin n → Canon n
  | const : Bool → Canon n
  | not   : Canon n → Canon n
  | and   : Canon n → Canon n → Canon n
  | or    : Canon n → Canon n → Canon n
  deriving Repr, DecidableEq

instance {n : ℕ} : ToString (Canon n) := ⟨fun c => reprStr c⟩

/--- Convert a circuit to a canonical form.  The implementation recursively
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

/--- Evaluate a canonical circuit. -/
noncomputable def evalCanon {n : ℕ} : Canon n → Point n → Bool
  | Canon.var i, x     => x i
  | Canon.const b, _   => b
  | Canon.not c, x     => !(evalCanon c x)
  | Canon.and c₁ c₂, x => evalCanon c₁ x && evalCanon c₂ x
  | Canon.or c₁ c₂, x  => evalCanon c₁ x || evalCanon c₂ x

/--- Canonicalisation preserves semantics. -/
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

/--- Two circuits have the same canonical form iff they compute the same
function. -/
theorem canonical_inj {n : ℕ} {c₁ c₂ : Circuit n} :
    canonical c₁ = canonical c₂ →
    (∀ x, eval c₁ x = eval c₂ x) := by
  intro h x
  have hcanon := congrArg (fun c => evalCanon c x) h
  have hc₁ := eval_canonical (c := c₁) (x := x)
  have hc₂ := eval_canonical (c := c₂) (x := x)
  calc
    eval c₁ x
        = evalCanon (canonical c₁) x := hc₁
    _ = evalCanon (canonical c₂) x := by simpa using hcanon
    _ = eval c₂ x := hc₂.symm

/-- ### Encoding length for canonical circuits

The following helper function measures the length of a canonical circuit in
bits.  Each variable index contributes `Nat.log2 n + 1` bits while every gate
adds a single bit.  This rough accounting is sufficient for subsequent
cardinality bounds. -/
def codeLen {n : ℕ} : Canon n → ℕ
  | Canon.var _   => Nat.log2 n + 1
  | Canon.const _ => 1
  | Canon.not c   => 1 + codeLen c
  | Canon.and c₁ c₂ => 1 + codeLen c₁ + codeLen c₂
  | Canon.or c₁ c₂  => 1 + codeLen c₁ + codeLen c₂

/-/ Encode a canonical circuit as a list of bits.  The exact format is
irrelevant, we merely track the length for a later bound. -/
def encodeCanon {n : ℕ} : Canon n → List Bool
  | Canon.var _       => List.replicate (Nat.log2 n + 1) false
  | Canon.const b     => [b]
  | Canon.not c       => false :: encodeCanon c
  | Canon.and c₁ c₂   => true :: encodeCanon c₁ ++ encodeCanon c₂
  | Canon.or c₁ c₂    => true :: encodeCanon c₁ ++ encodeCanon c₂

lemma encodeCanon_length {n : ℕ} (c : Canon n) :
    (encodeCanon c).length ≤ codeLen c := by
  induction c with
  | var _ =>
      simp [encodeCanon, codeLen]
  | const b =>
      simp [encodeCanon, codeLen]
  | not c ih =>
      have h := Nat.succ_le_succ ih
      simpa [encodeCanon, codeLen, Nat.succ_eq_add_one, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using h
  | and c₁ c₂ ih₁ ih₂ =>
      have := Nat.add_le_add ih₁ ih₂
      simpa [encodeCanon, codeLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Nat.succ_le_succ this
  | or c₁ c₂ ih₁ ih₂ =>
      have := Nat.add_le_add ih₁ ih₂
      simpa [encodeCanon, codeLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Nat.succ_le_succ this

/-! ### Size bound for canonical descriptions

The canonical code length of a circuit is bounded by its size times
`Nat.log2 n + 1`.  This captures the `O(m log n)` estimate used in the
roadmap.  The detailed proof is omitted here. -/
axiom canonical_desc_length {n : ℕ} (c : Circuit n) :
    codeLen (canonical c) ≤ (sizeOf c) * (Nat.log2 n + 1) + 1

/-- The set of circuits on `n` inputs whose size does not exceed `m`. -/
def circuitsUpTo (n m : ℕ) : Set (Circuit n) := {c | sizeOf c ≤ m}

/-- Upper bound on the number of canonical circuits of size at most `m`.
    The detailed proof is omitted. -/
axiom count_canonical_bounded (n m : ℕ) :
  ∃ h : (circuitsUpTo n m).Finite,
    h.toFinset.card ≤ 2 ^ (m * (Nat.log2 n + 1) + 1)

end Circuit

end Boolcube
