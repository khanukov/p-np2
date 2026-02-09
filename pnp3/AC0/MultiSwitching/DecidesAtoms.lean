import AC0.MultiSwitching.FuncCNF
import AC0.MultiSwitching.Decides

/-!
  pnp3/AC0/MultiSwitching/DecidesAtoms.lean

  Decidability predicates for FuncCNF/FuncDNF on atoms.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-- Atom is decided under restriction if its `decide` returns a value. -/
@[simp] def DecidesAtomOn {n : Nat} (ρ : Restriction n) (a : Atom n) : Prop :=
  ∃ b, a.decide ρ = some b

/-- Literal is decided under restriction if underlying atom is. -/
@[simp] def DecidesLitOnAtom {n : Nat} (ρ : Restriction n) (ℓ : AtomLit n) : Prop :=
  ∃ b, AtomLit.decide ℓ ρ = some b

/-- Clause is decided under restriction if `FuncClause.decide` returns a value. -/
@[simp] def DecidesClauseOnAtom {n : Nat} (ρ : Restriction n) (C : FuncClause n) : Prop :=
  ∃ b, FuncClause.decide C ρ = some b

/-- CNF is decided under restriction if all clauses are decided. -/
@[simp] def DecidesCNFOnAtom {n : Nat} (ρ : Restriction n) (F : FuncCNF n) : Prop :=
  ∀ C ∈ F.clauses, DecidesClauseOnAtom (ρ := ρ) C

/-- DNF is decided under restriction if all terms are decided. -/
@[simp] def DecidesDNFOnAtom {n : Nat} (ρ : Restriction n) (F : FuncDNF n) : Prop :=
  ∀ T ∈ F.terms, ∀ ℓ ∈ T.lits, DecidesLitOnAtom (ρ := ρ) ℓ

/-- Family decided under restriction if all formulas decided. -/
@[simp] def DecidesFamilyOnAtom {n : Nat} (ρ : Restriction n) (F : List (FuncCNF n)) : Prop :=
  ∀ G ∈ F, DecidesCNFOnAtom (ρ := ρ) G

@[simp] def evalFamilyRestrictFuncCNF
    {n : Nat} (ρ : Restriction n) (Fs : List (FuncCNF n)) : Core.Family n :=
  restrictFamily (ρ := ρ) (F := evalFamilyFuncCNF (n := n) Fs)

lemma mem_evalFamilyRestrictFuncCNF_iff
    {n : Nat} {ρ : Restriction n} {Fs : List (FuncCNF n)}
    {f : Core.BitVec n → Bool} :
    f ∈ evalFamilyRestrictFuncCNF (ρ := ρ) (Fs := Fs) ↔
      ∃ g ∈ evalFamilyFuncCNF (n := n) Fs, f = restrictFun ρ g := by
  classical
  unfold evalFamilyRestrictFuncCNF restrictFamily
  constructor
  · intro hf
    rcases List.mem_map.1 hf with ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact List.mem_map.2 ⟨g, hg, rfl⟩

lemma decidesCNFOnAtom_isConstantOn
    {n : Nat} {ρ : Restriction n} {F : FuncCNF n}
    (hdec : DecidesCNFOnAtom (ρ := ρ) F) :
    ρ.isConstantOn (FuncCNF.eval F) = true := by
  apply (Restriction.isConstantOn_iff (ρ := ρ) (f := FuncCNF.eval F)).2
  intro x y
  unfold Restriction.restrict
  cases F with
  | mk clauses =>
      revert hdec
      induction clauses with
      | nil =>
          intro hdec
          simp [FuncCNF.eval]
      | cons C Cs ih =>
          intro hdec
          have hdecC : DecidesClauseOnAtom (ρ := ρ) C := hdec C (by simp)
          have hdecCs : ∀ C ∈ Cs, DecidesClauseOnAtom (ρ := ρ) C := by
            intro C hC
            exact hdec C (by simp [hC])
          rcases hdecC with ⟨b, hb⟩
          have hconstC : ∀ x, FuncClause.eval C (ρ.override x) = b := by
            exact FuncClause.decide_sound (C := C) (ρ := ρ) (b := b) hb
          have ih' := ih hdecCs
          have h1 :
              FuncClause.eval C (ρ.override x) =
                FuncClause.eval C (ρ.override y) := by
            calc
              FuncClause.eval C (ρ.override x) = b := hconstC x
              _ = FuncClause.eval C (ρ.override y) := (hconstC y).symm
          have h2 :
              FuncCNF.eval { clauses := Cs } (ρ.override x) =
                FuncCNF.eval { clauses := Cs } (ρ.override y) := ih'
          have h1' :
              C.lits.any (fun ℓ => AtomLit.eval ℓ (ρ.override x)) =
                C.lits.any (fun ℓ => AtomLit.eval ℓ (ρ.override y)) := by
            simpa [FuncClause.eval] using h1
          have h2' :
              Cs.all (fun C => FuncClause.eval C (ρ.override x)) =
                Cs.all (fun C => FuncClause.eval C (ρ.override y)) := by
            simpa [FuncCNF.eval] using h2
          have h1'' :
              (C.lits.any fun ℓ =>
                if ℓ.neg = true then !ℓ.atom.eval (ρ.override x) else ℓ.atom.eval (ρ.override x)) =
              (C.lits.any fun ℓ =>
                if ℓ.neg = true then !ℓ.atom.eval (ρ.override y) else ℓ.atom.eval (ρ.override y)) := by
            simpa [AtomLit.eval] using h1'
          have h2'' :
              (Cs.all fun C =>
                C.lits.any fun ℓ =>
                  if ℓ.neg = true then !ℓ.atom.eval (ρ.override x) else ℓ.atom.eval (ρ.override x)) =
              (Cs.all fun C =>
                C.lits.any fun ℓ =>
                  if ℓ.neg = true then !ℓ.atom.eval (ρ.override y) else ℓ.atom.eval (ρ.override y)) := by
            simpa [AtomLit.eval] using h2'
          simp [FuncCNF.eval, h1'', h2'']

end MultiSwitching
end AC0
end Pnp3
