import Core.BooleanBasics

/-!
  pnp3/AC0/MultiSwitching/Atoms.lean

  Atom interface for functional CNF/DNF layers.
  An atom is a Boolean function equipped with a canonical strategy
  for branching on input bits under a restriction.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-- Atom with a canonical branching strategy under restrictions. -/
structure Atom (n : Nat) where
  eval : Core.BitVec n → Bool
  /-- If decided under ρ, return its constant value. -/
  decide : Restriction n → Option Bool
  /-- If not decided, choose the next variable to branch on. -/
  nextVar : Restriction n → Option (Fin n)
  /-- Soundness: decided value agrees with evaluation under `override`. -/
  decide_sound :
    ∀ {ρ : Restriction n} {b : Bool},
      decide ρ = some b → ∀ x, eval (ρ.override x) = b
  /-- If `nextVar` is provided, that variable is still free in `ρ`. -/
  nextVar_free :
    ∀ {ρ : Restriction n} {i : Fin n},
      nextVar ρ = some i → ρ.mask i = none
  /-- Progress: if `decide` is `none`, then `nextVar` is defined. -/
  nextVar_of_undecided :
    ∀ {ρ : Restriction n}, decide ρ = none → ∃ i, nextVar ρ = some i

/-- Literal over atoms with optional negation. -/
structure AtomLit (n : Nat) where
  atom : Atom n
  neg : Bool

namespace AtomLit

@[simp] def eval {n : Nat} (ℓ : AtomLit n) (x : Core.BitVec n) : Bool :=
  if ℓ.neg then !(ℓ.atom.eval x) else ℓ.atom.eval x

/-- Negation of an atom literal (flip the sign). -/
@[simp] def negLit {n : Nat} (ℓ : AtomLit n) : AtomLit n :=
  { atom := ℓ.atom, neg := !ℓ.neg }

@[simp] lemma eval_negLit {n : Nat} (ℓ : AtomLit n) (x : Core.BitVec n) :
    eval (negLit ℓ) x = ! eval ℓ x := by
  cases h : ℓ.neg <;> simp [eval, negLit, h]

/-- Decide literal under restriction if atom is decided. -/
@[simp] def decide {n : Nat} (ℓ : AtomLit n) (ρ : Restriction n) : Option Bool :=
  match ℓ.atom.decide ρ with
  | none => none
  | some b => some (if ℓ.neg then !b else b)

lemma decide_sound {n : Nat} {ℓ : AtomLit n} {ρ : Restriction n} {b : Bool} :
    decide (n := n) ℓ ρ = some b → ∀ x, eval ℓ (ρ.override x) = b := by
  intro hdec x
  cases h : ℓ.atom.decide ρ with
  | none =>
      simp [decide, h] at hdec
  | some b0 =>
      have hdec' : (if ℓ.neg then !b0 else b0) = b := by
        simpa [decide, h] using hdec
      have hsound := ℓ.atom.decide_sound (ρ := ρ) (b := b0) h
      have hval : ℓ.atom.eval (ρ.override x) = b0 := hsound x
      cases ℓ.neg <;> simp [eval, hval, hdec']

lemma decide_isConstantOn {n : Nat} {ℓ : AtomLit n} {ρ : Restriction n} {b : Bool} :
    decide (n := n) ℓ ρ = some b → ρ.isConstantOn (eval ℓ) = true := by
  intro hdec
  apply (Restriction.isConstantOn_iff (ρ := ρ) (f := eval ℓ)).2
  intro x y
  unfold Restriction.restrict
  have hx := decide_sound (n := n) (ℓ := ℓ) (ρ := ρ) (b := b) hdec x
  have hy := decide_sound (n := n) (ℓ := ℓ) (ρ := ρ) (b := b) hdec y
  calc
    eval ℓ (ρ.override x) = b := hx
    _ = eval ℓ (ρ.override y) := hy.symm

lemma nextVar_of_undecided {n : Nat} {ℓ : AtomLit n} {ρ : Restriction n} :
    decide (n := n) ℓ ρ = none → ∃ i, ℓ.atom.nextVar ρ = some i := by
  intro hdec
  -- decision for literal is none iff atom is undecided
  cases h : ℓ.atom.decide ρ with
  | none =>
      exact ℓ.atom.nextVar_of_undecided (ρ := ρ) h
  | some b =>
      simp [decide, h] at hdec

end AtomLit

namespace Atom

lemma decide_isConstantOn {n : Nat} {a : Atom n} {ρ : Restriction n} {b : Bool} :
    a.decide ρ = some b → ρ.isConstantOn a.eval = true := by
  intro hdec
  apply (Restriction.isConstantOn_iff (ρ := ρ) (f := a.eval)).2
  intro x y
  unfold Restriction.restrict
  have hx := a.decide_sound (ρ := ρ) (b := b) hdec x
  have hy := a.decide_sound (ρ := ρ) (b := b) hdec y
  calc
    a.eval (ρ.override x) = b := hx
    _ = a.eval (ρ.override y) := hy.symm

end Atom

end MultiSwitching
end AC0
end Pnp3
