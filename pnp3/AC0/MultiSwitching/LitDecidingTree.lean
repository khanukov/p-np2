import AC0.MultiSwitching.IHInterface
import AC0.AC0LitFormula

/-!
  pnp3/AC0/MultiSwitching/LitDecidingTree.lean

  Proved decision trees for literal functions (base case of multi-switching).

  For each literal type (positive literal `x_i`, negative literal `¬x_i`,
  and Boolean constant), we construct a `DecidingTreeWitness` with no axioms.
  These are the base cases for the depth-0 induction in multi-switching.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-! ### Helper: subcube with one fixed bit -/

/-- Subcube fixing only bit `i` to value `b`, all other bits free. -/
def singleBitSubcube {n : Nat} (i : Fin n) (b : Bool) : Subcube n :=
  fun j => if j = i then some b else none

/-- The all-free subcube (no bits fixed). -/
def freeSubcube (n : Nat) : Subcube n := fun _ => none

/-! ### Constant literal decision tree -/

/-- Decision tree for a constant function `fun _ => b`: a single leaf. -/
def constLitDecidingTree (n : Nat) (b : Bool) :
    DecidingTreeWitness n (fun _ => b) where
  tree := PDT.leaf (freeSubcube n)
  leafValue := fun _ => b
  leafOfRestriction_mem := by
    intro ρ β h
    simp [leafOfRestriction] at h
    subst h
    simp [PDT.leaves]
  leafValue_sound := by
    intro β _ x _
    rfl
  leaf_covers := by
    intro ρ β h x hmem
    simp [leafOfRestriction] at h
    subst h
    rw [mem_iff]
    intro i b' hb'
    simp [freeSubcube] at hb'

/-! ### Positive literal decision tree -/

private lemma singleBitSubcube_self {n : Nat} (i : Fin n) (b : Bool) :
    singleBitSubcube i b i = some b := by
  simp [singleBitSubcube]

private lemma mem_singleBitSubcube_val {n : Nat} (i : Fin n) (b : Bool)
    (x : Core.BitVec n) (hmem : mem (singleBitSubcube i b) x) :
    x i = b := by
  rw [mem_iff] at hmem
  exact hmem i b (singleBitSubcube_self i b)

/-- Decision tree for `fun x => x i`: branch on variable `i`. -/
def posLitDecidingTree (n : Nat) (i : Fin n) :
    DecidingTreeWitness n (fun x => x i) where
  tree := PDT.node i
      (PDT.leaf (singleBitSubcube i false))
      (PDT.leaf (singleBitSubcube i true))
  leafValue := fun β =>
    match β i with
    | some true => true
    | some false => false
    | none => false
  leafOfRestriction_mem := by
    intro ρ β h
    simp only [leafOfRestriction] at h
    cases hmask : ρ.mask i with
    | none => simp [hmask] at h
    | some b =>
      cases b with
      | false =>
        simp [hmask] at h
        subst h; simp [PDT.leaves]
      | true =>
        simp [hmask] at h
        subst h; simp [PDT.leaves]
  leafValue_sound := by
    intro β hβ x hmem
    simp [PDT.leaves] at hβ
    rcases hβ with rfl | rfl
    · -- β = singleBitSubcube i false
      have hxi := mem_singleBitSubcube_val i false x hmem
      simp [singleBitSubcube_self, hxi]
    · -- β = singleBitSubcube i true
      have hxi := mem_singleBitSubcube_val i true x hmem
      simp [singleBitSubcube_self, hxi]
  leaf_covers := by
    intro ρ β h x hmem
    simp only [leafOfRestriction] at h
    cases hmask : ρ.mask i with
    | none => simp [hmask] at h
    | some b =>
      cases b with
      | false =>
        simp [hmask] at h
        subst h
        rw [mem_iff]
        intro j b' hj
        unfold singleBitSubcube at hj
        by_cases hji : j = i
        · subst hji; simp at hj; subst hj
          exact (mem_iff ρ.mask x).mp hmem _ _ hmask
        · simp [hji] at hj
      | true =>
        simp [hmask] at h
        subst h
        rw [mem_iff]
        intro j b' hj
        unfold singleBitSubcube at hj
        by_cases hji : j = i
        · subst hji; simp at hj; subst hj
          exact (mem_iff ρ.mask x).mp hmem _ _ hmask
        · simp [hji] at hj

/-! ### Negative literal decision tree -/

/-- Decision tree for `fun x => !(x i)`: negate the positive literal tree. -/
def negLitDecidingTree (n : Nat) (i : Fin n) :
    DecidingTreeWitness n (fun x => !(x i)) :=
  DecidingTreeWitness.neg (posLitDecidingTree n i)

/-! ### AC0LitFormula base case: decision tree for any depth-0 formula -/

/-- Decision tree witness for any depth-0 `AC0LitFormula`. -/
noncomputable def litFormulaDecidingTree_base (n : Nat) (f : AC0LitFormula n 0) :
    DecidingTreeWitness n (AC0LitFormula.eval n 0 f) := by
  cases f with
  | posLit i =>
      have h : AC0LitFormula.eval n 0 (AC0LitFormula.posLit i) = fun x => x i := by
        funext x; simp [AC0LitFormula.eval, AC0LitFormula.evalCore]
      exact DecidingTreeWitness.cast h.symm (posLitDecidingTree n i)
  | negLit i =>
      have h : AC0LitFormula.eval n 0 (AC0LitFormula.negLit i) = fun x => !(x i) := by
        funext x; simp [AC0LitFormula.eval, AC0LitFormula.evalCore]
      exact DecidingTreeWitness.cast h.symm (negLitDecidingTree n i)
  | constLit b =>
      have h : AC0LitFormula.eval n 0 (AC0LitFormula.constLit b) = fun _ => b := by
        funext x; simp [AC0LitFormula.eval, AC0LitFormula.evalCore]
      exact DecidingTreeWitness.cast h.symm (constLitDecidingTree n b)

end MultiSwitching
end AC0
end Pnp3
