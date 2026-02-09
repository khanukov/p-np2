import Core.BooleanBasics
import Core.PDT
import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.Atoms

/-!
  pnp3/AC0/MultiSwitching/IHInterface.lean

  Minimal interface for IH-driven atoms.
  This file only fixes the data/axioms needed to later build
  `Atom` values from IH witnesses without creating import cycles.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-!
  Deciding trees for atoms.
  We derive `decide`/`nextVar` from the tree, avoiding ad‑hoc choice.
-/

/-- Follow the tree using fixed bits of `ρ` until a free variable appears. -/
def nextVarFromTree {n : Nat} (t : PDT n) (ρ : Restriction n) : Option (Fin n) :=
  match t with
  | .leaf _ => none
  | .node i t0 t1 =>
      match ρ.mask i with
      | none => some i
      | some false => nextVarFromTree t0 ρ
      | some true => nextVarFromTree t1 ρ

/-- Follow the tree using fixed bits of `ρ` until a leaf is reached. -/
def leafOfRestriction {n : Nat} (t : PDT n) (ρ : Restriction n) : Option (Subcube n) :=
  match t with
  | .leaf β => some β
  | .node i t0 t1 =>
      match ρ.mask i with
      | none => none
      | some false => leafOfRestriction t0 ρ
      | some true => leafOfRestriction t1 ρ

instance decidableSubcubeRefines {n : Nat} (β γ : Subcube n) :
    Decidable (subcubeRefines β γ) := by
  unfold subcubeRefines
  exact inferInstance

def leafOfRestrictionConsistent {n : Nat} (t : PDT n) (ρ : Restriction n) :
    Option (Subcube n) :=
  match t with
  | .leaf β =>
      if subcubeRefines β ρ.mask then some β else none
  | .node i t0 t1 =>
      match ρ.mask i with
      | none => none
      | some false => leafOfRestrictionConsistent t0 ρ
      | some true => leafOfRestrictionConsistent t1 ρ

lemma leafOfRestrictionConsistent_refines {n : Nat} (t : PDT n) (ρ : Restriction n)
    {β : Subcube n} :
    leafOfRestrictionConsistent t ρ = some β → subcubeRefines β ρ.mask := by
  revert ρ
  induction t with
  | leaf β0 =>
      intro ρ h
      simp [leafOfRestrictionConsistent] at h
      rcases h with ⟨href, rfl⟩
      exact href
  | node i t0 t1 ih0 ih1 =>
      intro ρ h
      cases hmask : ρ.mask i with
      | none =>
          simp [leafOfRestrictionConsistent, hmask] at h
      | some b =>
          cases b with
          | false =>
              simp [leafOfRestrictionConsistent, hmask] at h
              exact ih0 (ρ := ρ) h
          | true =>
              simp [leafOfRestrictionConsistent, hmask] at h
              exact ih1 (ρ := ρ) h

lemma subcubeRefines_mem_of_mem {n : Nat} {β γ : Subcube n} {x : Core.BitVec n} :
    subcubeRefines β γ → mem β x → mem γ x := by
  intro href hmem
  apply (mem_iff (β := γ) (x := x)).2
  intro i b hγ
  have hβ : β i = some b := href i b hγ
  exact (mem_iff (β := β) (x := x)).1 hmem i b hβ

structure DecidingTreeWitness (n : Nat) (f : Core.BitVec n → Bool) where
  /-- Decision tree. -/
  tree : PDT n
  /-- Leaf value when the tree decides. -/
  leafValue : Subcube n → Bool
  /-- If we reach a leaf by following `ρ`, it is indeed a leaf of `tree`. -/
  leafOfRestriction_mem :
    ∀ {ρ : Restriction n} {β : Subcube n},
      leafOfRestriction tree ρ = some β → β ∈ PDT.leaves tree
  /-- Soundness on each leaf subcube. -/
  leafValue_sound :
    ∀ {β : Subcube n}, β ∈ PDT.leaves tree →
      ∀ x, mem β x → f x = leafValue β
  /-- If `ρ` follows the tree to `β`, then `β` covers all `x` compatible with `ρ`. -/
  leaf_covers :
    ∀ {ρ : Restriction n} {β : Subcube n},
      leafOfRestriction tree ρ = some β →
      ∀ x, mem ρ.mask x → mem β x

def DecidingTreeWitness.neg {n : Nat} {f : Core.BitVec n → Bool} :
    DecidingTreeWitness n f → DecidingTreeWitness n (fun x => ! f x)
  | W =>
    { tree := W.tree
      leafValue := fun β => ! W.leafValue β
      leafOfRestriction_mem := W.leafOfRestriction_mem
      leafValue_sound := by
        intro β hβ x hx
        have h := W.leafValue_sound (β := β) hβ x hx
        simp [h]
      leaf_covers := W.leaf_covers }

def DecidingTreeWitness.cast {n : Nat} {f g : Core.BitVec n → Bool} (h : f = g) :
    DecidingTreeWitness n f → DecidingTreeWitness n g
  | W => by
      cases h
      exact W

def decideFromTree {n : Nat} {f : Core.BitVec n → Bool}
    (W : DecidingTreeWitness n f) (ρ : Restriction n) : Option Bool :=
  Option.map W.leafValue (leafOfRestriction W.tree ρ)

lemma decideFromTree_sound {n : Nat} {f : Core.BitVec n → Bool}
    (W : DecidingTreeWitness n f) {ρ : Restriction n} {b : Bool} :
    decideFromTree W ρ = some b →
      ∀ x, mem ρ.mask x → f x = b := by
  intro hdec x hx
  unfold decideFromTree at hdec
  cases hleaf : leafOfRestriction W.tree ρ with
  | none =>
      simp [hleaf] at hdec
  | some β =>
      have hb' : W.leafValue β = b := by
        simpa [hleaf] using hdec
      have hb : b = W.leafValue β := hb'.symm
      subst hb
      have hmem : mem β x :=
        W.leaf_covers (ρ := ρ) (β := β) hleaf x hx
      have hleafmem : β ∈ PDT.leaves W.tree :=
        W.leafOfRestriction_mem (ρ := ρ) (β := β) hleaf
      exact W.leafValue_sound (β := β) hleafmem x hmem

lemma nextVarFromTree_free {n : Nat} (t : PDT n) {ρ : Restriction n} {i : Fin n} :
    nextVarFromTree t ρ = some i → ρ.mask i = none := by
  revert ρ
  induction t with
  | leaf β =>
      intro ρ h
      cases h
  | node j t0 t1 ih0 ih1 =>
      intro ρ h
      cases hmask : ρ.mask j with
      | none =>
          simp [nextVarFromTree, hmask] at h
          cases h
          simpa [hmask]
      | some b =>
          cases b with
          | false =>
              simp [nextVarFromTree, hmask] at h
              exact ih0 (ρ := ρ) h
          | true =>
              simp [nextVarFromTree, hmask] at h
              exact ih1 (ρ := ρ) h

lemma nextVarFromTree_of_undecided {n : Nat} {t : PDT n} {ρ : Restriction n} :
    leafOfRestriction t ρ = none → ∃ i, nextVarFromTree t ρ = some i := by
  revert ρ
  induction t with
  | leaf β =>
      intro ρ h
      simp [leafOfRestriction] at h
  | node j t0 t1 ih0 ih1 =>
      intro ρ h
      cases hmask : ρ.mask j with
      | none =>
          refine ⟨j, ?_⟩
          simp [nextVarFromTree, hmask]
      | some b =>
          cases b with
          | false =>
              simp [leafOfRestriction, nextVarFromTree, hmask] at h ⊢
              exact ih0 (ρ := ρ) h
          | true =>
              simp [leafOfRestriction, nextVarFromTree, hmask] at h ⊢
              exact ih1 (ρ := ρ) h

structure AtomTailWitness (n : Nat) where
  /-- The atom's semantics. -/
  eval : Core.BitVec n → Bool
  /-- IH deciding tree witness. -/
  W : DecidingTreeWitness n eval

def AtomTailWitness.ofDecidingTree {n : Nat} {f : Core.BitVec n → Bool} :
    DecidingTreeWitness n f → AtomTailWitness n
  | W => { eval := f, W := W }

def AtomTailWitness.decide {n : Nat} (A : AtomTailWitness n) (ρ : Restriction n) :
    Option Bool :=
  decideFromTree A.W ρ

def AtomTailWitness.nextVar {n : Nat} (A : AtomTailWitness n) (ρ : Restriction n) :
    Option (Fin n) :=
  nextVarFromTree A.W.tree ρ

lemma AtomTailWitness.decide_sound {n : Nat} {A : AtomTailWitness n}
    {ρ : Restriction n} {b : Bool} :
    A.decide ρ = some b → ∀ x, A.eval (ρ.override x) = b := by
  intro hdec x
  have hsound := decideFromTree_sound (W := A.W) (ρ := ρ) (b := b) hdec
  have hmem : mem ρ.mask (ρ.override x) := ρ.override_mem x
  simpa [Restriction.restrict] using hsound (ρ.override x) hmem

lemma AtomTailWitness.nextVar_free {n : Nat} {A : AtomTailWitness n}
    {ρ : Restriction n} {i : Fin n} :
    A.nextVar ρ = some i → ρ.mask i = none := by
  intro h
  exact nextVarFromTree_free (t := A.W.tree) (ρ := ρ) h

lemma AtomTailWitness.nextVar_of_undecided {n : Nat} {A : AtomTailWitness n}
    {ρ : Restriction n} :
    A.decide ρ = none → ∃ i, A.nextVar ρ = some i := by
  intro hdec
  unfold AtomTailWitness.decide decideFromTree at hdec
  have hleaf : leafOfRestriction A.W.tree ρ = none := by
    cases hleaf : leafOfRestriction A.W.tree ρ with
    | none => rfl
    | some β => simp [hleaf, Option.map] at hdec
  exact nextVarFromTree_of_undecided (t := A.W.tree) (ρ := ρ) hleaf

def AtomTailWitness.toAtom {n : Nat} (A : AtomTailWitness n) : Atom n :=
  { eval := A.eval
    decide := A.decide
    nextVar := A.nextVar
    decide_sound := A.decide_sound
    nextVar_free := A.nextVar_free
    nextVar_of_undecided := A.nextVar_of_undecided }

end MultiSwitching
end AC0
end Pnp3
