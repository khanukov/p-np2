import Complexity.Interfaces
import Complexity.PsubsetPpolyInternal.TreeToStraight
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData

namespace Pnp3
namespace Tests
namespace HInDagTrivialityProbe

open ComplexityInterfaces
open Models
open Magnification

noncomputable section

/-- One-gate constant-false DAG used off the unique encoded slice. -/
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => DagGate.const false
  output := DagWire.gate ⟨0, by simp⟩

@[simp] private theorem constFalseDag_size {n : Nat} :
    DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, DagCircuit.size]

@[simp] private theorem constFalseDag_eval {n : Nat} (x : Bitstring n) :
    DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, DagCircuit.eval, DagCircuit.eval.evalGateAt]

/-- Rename inputs in a tree circuit.  This keeps the truth-table recursion tiny. -/
private def treeRename {m n : Nat} (σ : Fin m → Fin n) :
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit m → Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n
  | .var i => .var (σ i)
  | .const b => .const b
  | .not c => .not (treeRename σ c)
  | .and c d => .and (treeRename σ c) (treeRename σ d)
  | .or c d => .or (treeRename σ c) (treeRename σ d)

private theorem treeRename_eval {m n : Nat} (σ : Fin m → Fin n)
    (c : Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit m) (x : Bitstring n) :
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval (treeRename σ c) x = Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval c (fun i => x (σ i)) := by
  induction c with
  | var i => rfl
  | const b => rfl
  | not c ih => simp [treeRename, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, ih]
  | and c d ihc ihd => simp [treeRename, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, ihc, ihd]
  | or c d ihc ihd => simp [treeRename, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, ihc, ihd]

/-- Tree truth table for one fixed input length, later compiled to a DAG. -/
private def ttTree : ∀ {n : Nat}, (Bitstring n → Bool) → Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n
  | 0, f => .const (f (fun i => Fin.elim0 i))
  | n + 1, f =>
      let c0 := ttTree (fun x : Bitstring n => f (Fin.cases false x))
      let c1 := ttTree (fun x : Bitstring n => f (Fin.cases true x))
      .or (.and (.not (.var ⟨0, Nat.zero_lt_succ n⟩)) (treeRename Fin.succ c0))
          (.and (.var ⟨0, Nat.zero_lt_succ n⟩) (treeRename Fin.succ c1))

private theorem ttTree_eval : ∀ {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n),
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval (ttTree f) x = f x
  | 0, f, x => by
      show f (fun i => Fin.elim0 i) = f x
      congr 1
      funext i
      exact Fin.elim0 i
  | n + 1, f, x => by
      simp only [ttTree, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, treeRename_eval]
      have h0 := ttTree_eval (fun y : Bitstring n => f (Fin.cases false y))
        (fun i => x (Fin.succ i))
      have h1 := ttTree_eval (fun y : Bitstring n => f (Fin.cases true y))
        (fun i => x (Fin.succ i))
      rw [h0, h1]
      have hx : ∀ b, x ⟨0, Nat.zero_lt_succ n⟩ = b →
          (Fin.cases (n := n) b (fun i => x (Fin.succ i)) : Bitstring (n + 1)) = x := by
        intro b hb
        funext i
        induction i using Fin.cases with
        | zero => exact hb.symm
        | succ j => rfl
      cases h : x ⟨0, Nat.zero_lt_succ n⟩
      · simp [hx false h]
      · simp [hx true h]

/-- Compile the tree truth table into the canonical DAG interface. -/
private def ttDag {n : Nat} (f : Bitstring n → Bool) : DagCircuit n :=
  Pnp3.Complexity.StraightLineAdapter.toDag (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeCircuit (ttTree f))

private theorem compiled_tree_eval {n : Nat} (c : Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n) (x : Bitstring n) :
    DagCircuit.eval (Pnp3.Complexity.StraightLineAdapter.toDag (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeCircuit c)) x = Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval c x := by
  have hAdapter : Pnp3.Complexity.StraightLineAdapter.eval (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeCircuit c) x = Pnp3.Internal.PsubsetPpoly.StraightLine.eval (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeCircuit c) x :=
    Pnp3.Internal.PsubsetPpoly.StraightLine.adapter_eval_eq_eval (C := Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeCircuit c) (x := x)
  have hWire : Pnp3.Internal.PsubsetPpoly.StraightLine.eval (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeCircuit c) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree c).ckt) (x := x) (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree c).out := by
    simpa [Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeCircuit] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree c).ckt)
        (out := (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree c).out) (x := x))
  exact hAdapter.trans (hWire.trans (Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeWireSemantics c x))

private theorem ttDag_eval {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n) :
    DagCircuit.eval (ttDag f) x = f x := by
  exact (compiled_tree_eval (ttTree f) x).trans (ttTree_eval f x)

/-- Every fixed partial-MCSP slice has a DAG family by hardwiring its truth table. -/
def fixedSlice_gapPartialMCSP_in_PpolyDAG (p : GapPartialMCSPParams) :
    InPpolyDAG (gapPartialMCSP_Language p) := by
  classical
  let n0 := Models.partialInputLen p
  let c0 : DagCircuit n0 := ttDag (gapPartialMCSP_Language p n0)
  let c0Size : Nat := DagCircuit.size c0
  refine {
    polyBound := fun m => if m = n0 then c0Size else 2
    polyBound_poly := ?_
    family := fun m => if h : m = n0 then (h ▸ c0 : DagCircuit m) else constFalseDag m
    family_size_le := ?_
    correct := ?_
  }
  · refine ⟨c0Size + 2, ?_⟩
    intro m
    by_cases hm : m = n0
    · simp [hm]
      omega
    · simp [hm]
      omega
  · intro m
    by_cases hm : m = n0
    · subst hm
      simp [c0Size]
    · simp [hm]
  · intro m x
    by_cases hm : m = n0
    · subst hm
      simp only [dif_pos]
      exact ttDag_eval (gapPartialMCSP_Language p n0) x
    · have hLang : gapPartialMCSP_Language p m x = false := by
        unfold gapPartialMCSP_Language
        exact dif_neg hm
      simp [hm, hLang]

def hInDag_for_canonicalAsymptoticHAsym :
    ∀ n β,
      InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic
              canonicalAsymptoticHAsym).paramsOf n β)) := by
  intro n β
  exact fixedSlice_gapPartialMCSP_in_PpolyDAG _

end

end HInDagTrivialityProbe
end Tests
end Pnp3
