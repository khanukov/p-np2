import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Complexity.PsubsetPpolyInternal.TreeToStraight

/-!
L0 probe: fixed-slice hardwiring for `gapPartialMCSP_Language` into the
canonical DAG interface.  This is an upper-bound/triviality probe only; it is
not lower-bound progress toward `P ≠ NP`.
-/

namespace Pnp3
namespace Tests
namespace HInDagTrivialityProbe

open ComplexityInterfaces
open Models
open Magnification
open Internal.PsubsetPpoly
open Internal.PsubsetPpoly.StraightLine

/-- One-gate constant-false DAG used on all non-active lengths. -/
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => .const false
  output := .gate ⟨0, Nat.lt.base 0⟩

@[simp] private theorem constFalseDag_eval {n : Nat} (x : Bitstring n) :
    DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, DagCircuit.eval, DagCircuit.eval.evalGateAt]

/-- Rename inputs in a tree circuit. -/
private def treeRename {m n : Nat} (σ : Fin m → Fin n) :
    Boolcube.Circuit m → Boolcube.Circuit n
  | .var i => .var (σ i)
  | .const b => .const b
  | .not c => .not (treeRename σ c)
  | .and c₁ c₂ => .and (treeRename σ c₁) (treeRename σ c₂)
  | .or c₁ c₂ => .or (treeRename σ c₁) (treeRename σ c₂)

private theorem treeRename_eval {m n : Nat} (σ : Fin m → Fin n)
    (c : Boolcube.Circuit m) (x : Bitstring n) :
    Boolcube.Circuit.eval (treeRename σ c) x =
      Boolcube.Circuit.eval c (fun i => x (σ i)) := by
  induction c with
  | var i => rfl
  | const b => rfl
  | not c ih => simp [treeRename, Boolcube.Circuit.eval, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [treeRename, Boolcube.Circuit.eval, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [treeRename, Boolcube.Circuit.eval, ih₁, ih₂]

/-- Truth-table tree circuit, used as a compact authoring layer for the DAG. -/
private def ttTree : ∀ {n : Nat}, (Bitstring n → Bool) → Boolcube.Circuit n
  | 0, f => .const (f (fun i => Fin.elim0 i))
  | n + 1, f =>
      let c0 := ttTree (fun x : Bitstring n => f (Fin.cases false x))
      let c1 := ttTree (fun x : Bitstring n => f (Fin.cases true x))
      .or
        (.and (.not (.var ⟨0, Nat.zero_lt_succ n⟩)) (treeRename Fin.succ c0))
        (.and (.var ⟨0, Nat.zero_lt_succ n⟩) (treeRename Fin.succ c1))

private theorem ttTree_eval :
    ∀ {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n),
      Boolcube.Circuit.eval (ttTree f) x = f x
  | 0, f, x => by
      show f (fun i => Fin.elim0 i) = f x
      congr 1
      funext i
      exact Fin.elim0 i
  | n + 1, f, x => by
      simp only [ttTree, Boolcube.Circuit.eval, treeRename_eval]
      have ih0 := ttTree_eval (fun y : Bitstring n => f (Fin.cases false y))
        (fun i => x (Fin.succ i))
      have ih1 := ttTree_eval (fun y : Bitstring n => f (Fin.cases true y))
        (fun i => x (Fin.succ i))
      rw [ih0, ih1]
      have hx : ∀ b, x ⟨0, Nat.zero_lt_succ n⟩ = b →
          (Fin.cases (n := n) b (fun i => x (Fin.succ i)) : Bitstring (n + 1)) = x := by
        intro b hb
        funext i
        induction i using Fin.cases with
        | zero => exact hb.symm
        | succ j => rfl
      cases h0 : x ⟨0, Nat.zero_lt_succ n⟩ <;>
        simp only [Bool.not_false, Bool.not_true, Bool.true_and,
          Bool.false_and, Bool.or_false, Bool.false_or] <;>
        rw [hx _ h0]

/-- DAG truth-table hardwiring obtained by compiling the tree to straight-line form. -/
private noncomputable def ttDag {n : Nat} (f : Bitstring n → Bool) : DagCircuit n :=
  let cc := compileTree (ttTree f)
  Complexity.StraightLineAdapter.toDag
    (Complexity.StraightLineAdapter.withOutput cc.ckt cc.out)

private theorem ttDag_eval {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n) :
    DagCircuit.eval (ttDag f) x = f x := by
  rw [ttDag]
  let cc := compileTree (ttTree f)
  calc
    DagCircuit.eval
        (Complexity.StraightLineAdapter.toDag
          (Complexity.StraightLineAdapter.withOutput cc.ckt cc.out)) x
        = Complexity.StraightLineAdapter.eval
          (Complexity.StraightLineAdapter.withOutput cc.ckt cc.out) x := rfl
    _ = Complexity.StraightLineAdapter.evalWire cc.ckt x cc.out := rfl
    _ = StraightLine.evalWire cc.ckt x cc.out :=
        adapter_evalWire_eq_evalWire cc.ckt x cc.out
    _ = Boolcube.Circuit.eval (ttTree f) x := by
        exact StraightLine.compileTreeWireSemantics (ttTree f) x
    _ = f x := ttTree_eval f x

/-- Per-slice DAG witness: one hardwired truth-table DAG at the active length. -/
noncomputable def fixedSlice_gapPartialMCSP_in_PpolyDAG (p : GapPartialMCSPParams) :
    InPpolyDAG (gapPartialMCSP_Language p) := by
  classical
  let N := partialInputLen p
  let C := ttDag (gapPartialMCSP_Language p N)
  let K := DagCircuit.size C
  refine
    { polyBound := fun m => if m = N then K else 2
      polyBound_poly := ?_
      family := fun m => if h : m = N then h ▸ C else constFalseDag m
      family_size_le := ?_
      correct := ?_ }
  · refine ⟨K + 2, ?_⟩
    intro m
    by_cases h : m = N
    · subst h
      have h₁ : C.size ≤ C.size + 2 := by omega
      have h₂ : C.size + 2 ≤ N ^ (C.size + 2) + (C.size + 2) :=
        Nat.le_add_left _ _
      simpa [K] using le_trans h₁ h₂
    · have : 2 ≤ m ^ (K + 2) + (K + 2) := by omega
      simpa [h] using this
  · intro m
    by_cases h : m = N
    · subst h
      simp [K]
    · simp [h, constFalseDag, DagCircuit.size]
  · intro m x
    by_cases h : m = N
    · subst h
      simpa [C] using ttDag_eval (gapPartialMCSP_Language p N) x
    · have hm : m ≠ partialInputLen p := by simpa [N] using h
      simp [h, hm, gapPartialMCSP_Language]

/-- Canonical route hypothesis surface; the premise is fixed-slice hardwiring. -/
noncomputable def hInDag_for_canonicalAsymptoticHAsym :
    ∀ n β,
      InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic
              canonicalAsymptoticHAsym).paramsOf n β)) := by
  intro n β
  exact fixedSlice_gapPartialMCSP_in_PpolyDAG _

end HInDagTrivialityProbe
end Tests
end Pnp3
