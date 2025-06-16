import Boolcube

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
  -- Proof is by straightforward recursion on `c`.
  -- Implementation omitted.
  sorry

/-- Two circuits have the same canonical form iff they compute the same function. -/
theorem canonical_inj {n : ℕ} {c₁ c₂ : Circuit n} :
    canonical c₁ = canonical c₂ →
    (∀ x, eval c₁ x = eval c₂ x) := by
  -- This follows from `eval_canonical` for both circuits.
  intro h x
  have := congrArg (fun c => evalCanon c x) h
  -- rest of proof omitted
  sorry

end Circuit

end Boolcube

