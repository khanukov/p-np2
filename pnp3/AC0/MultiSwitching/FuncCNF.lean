import AC0.MultiSwitching.Atoms
import Core.SAL_Core

/-!
  pnp3/AC0/MultiSwitching/FuncCNF.lean

  CNF/DNF built from atoms (functions with a branching strategy).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-- Clause over atom-literals. -/
structure FuncClause (n : Nat) where
  lits : List (AtomLit n)

/-- CNF as a list of clauses. -/
structure FuncCNF (n : Nat) where
  clauses : List (FuncClause n)

/-- Term over atom-literals. -/
structure FuncTerm (n : Nat) where
  lits : List (AtomLit n)

/-- DNF as a list of terms. -/
structure FuncDNF (n : Nat) where
  terms : List (FuncTerm n)

namespace FuncClause

@[simp] lemma list_any_eq_true_of_exists {α : Type _} (p : α → Bool) :
    ∀ xs : List α, (∃ x ∈ xs, p x = true) → xs.any p = true
  | [], h => by
      rcases h with ⟨x, hx, _⟩
      cases hx
  | x :: xs, h => by
      rcases h with ⟨y, hy, hytrue⟩
      have hy' : y = x ∨ y ∈ xs := by
        simpa using hy
      cases hy' with
      | inl hxy =>
          subst hxy
          simp [List.any, hytrue]
      | inr hyxs =>
          have htail : xs.any p = true := list_any_eq_true_of_exists p xs ⟨y, hyxs, hytrue⟩
          simp [List.any, htail]

@[simp] lemma list_any_eq_false_of_forall {α : Type _} (p : α → Bool) :
    ∀ xs : List α, (∀ x ∈ xs, p x = false) → xs.any p = false
  | [], _ => by simp [List.any]
  | x :: xs, h => by
      have hx : p x = false := h x (by simp)
      have hxs : xs.any p = false := by
        apply list_any_eq_false_of_forall p xs
        intro y hy
        exact h y (by simp [hy])
      simp [List.any, hx, hxs]

@[simp] def eval {n : Nat} (C : FuncClause n) (x : Core.BitVec n) : Bool :=
  C.lits.any (fun ℓ => AtomLit.eval ℓ x)

/-- Decide clause if all literals are decided. -/
@[simp] def decide {n : Nat} (C : FuncClause n) (ρ : Restriction n) : Option Bool :=
  if _hsat : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some true then
    some true
  else if _hfalse : ∀ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some false then
    some false
  else
    none

lemma decide_sound {n : Nat} {C : FuncClause n} {ρ : Restriction n} {b : Bool} :
    decide C ρ = some b → ∀ x, eval C (ρ.override x) = b := by
  intro hdec x
  by_cases hsat : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some true
  · cases b with
    | false =>
        simp [FuncClause.decide, hsat, -AtomLit.decide] at hdec
    | true =>
        rcases hsat with ⟨ℓ, hℓ, hℓdec⟩
        have hℓval := AtomLit.decide_sound (ℓ := ℓ) (ρ := ρ) (b := true) hℓdec x
        have hany :
            C.lits.any (fun ℓ => AtomLit.eval ℓ (ρ.override x)) = true := by
          apply list_any_eq_true_of_exists (p := fun ℓ => AtomLit.eval ℓ (ρ.override x)) C.lits
          exact ⟨ℓ, hℓ, by simpa using hℓval⟩
        simpa [FuncClause.eval] using hany
  · by_cases hfalse : ∀ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some false
    · cases b with
      | true =>
          simp [FuncClause.decide, hsat, -AtomLit.decide] at hdec
      | false =>
          have hall :
              C.lits.any (fun ℓ => AtomLit.eval ℓ (ρ.override x)) = false := by
            apply list_any_eq_false_of_forall (p := fun ℓ => AtomLit.eval ℓ (ρ.override x)) C.lits
            intro ℓ hℓ
            have hℓdec := hfalse ℓ hℓ
            have hℓval := AtomLit.decide_sound (ℓ := ℓ) (ρ := ρ) (b := false) hℓdec x
            simpa using hℓval
          simpa [FuncClause.eval] using hall
    · simp [FuncClause.decide, hsat, hfalse, -AtomLit.decide] at hdec

end FuncClause

namespace FuncCNF

@[simp] def eval {n : Nat} (F : FuncCNF n) (x : Core.BitVec n) : Bool :=
  F.clauses.all (fun C => FuncClause.eval C x)

end FuncCNF

namespace FuncTerm

@[simp] def eval {n : Nat} (T : FuncTerm n) (x : Core.BitVec n) : Bool :=
  T.lits.all (fun ℓ => AtomLit.eval ℓ x)

end FuncTerm

namespace FuncDNF

@[simp] def eval {n : Nat} (F : FuncDNF n) (x : Core.BitVec n) : Bool :=
  F.terms.any (fun T => FuncTerm.eval T x)

end FuncDNF

/-!
  Family evaluation for lists of FuncCNF.
-/

@[simp] def evalFamilyFuncCNF {n : Nat} (Fs : List (FuncCNF n)) : Core.Family n :=
  Fs.map (fun F => FuncCNF.eval (n := n) F)

lemma mem_evalFamilyFuncCNF_iff {n : Nat} {Fs : List (FuncCNF n)} {f : Core.BitVec n → Bool} :
    f ∈ evalFamilyFuncCNF (n := n) Fs ↔ ∃ F ∈ Fs, f = FuncCNF.eval (n := n) F := by
  constructor
  · intro hf
    rcases List.mem_map.1 hf with ⟨F, hF, rfl⟩
    exact ⟨F, hF, rfl⟩
  · intro hf
    rcases hf with ⟨F, hF, rfl⟩
    exact List.mem_map.2 ⟨F, hF, rfl⟩

end MultiSwitching
end AC0
end Pnp3
