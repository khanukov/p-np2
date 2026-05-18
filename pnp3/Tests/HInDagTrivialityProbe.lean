import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Complexity.PsubsetPpolyInternal.TreeToStraight
import Complexity.PsubsetPpolyInternal.StraightLineSemantics
import Mathlib.Tactic

namespace Pnp3
namespace Tests
namespace HInDagTrivialityProbe

open ComplexityInterfaces
open Models
open Magnification

noncomputable section

/-- Local constant-false DAG; the production copy is private elsewhere. -/
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => .const false
  output := .gate ⟨0, Nat.lt.base 0⟩

private theorem constFalseDag_eval (n : Nat) (x : Bitstring n) :
    DagCircuit.eval (constFalseDag n) x = false := by
  rw [DagCircuit.eval]
  change DagCircuit.eval.evalGateAt (C := constFalseDag n) (x := x) 0 (Nat.lt.base 0) = false
  rw [DagCircuit.eval.evalGateAt]
  rfl

/-- Rename inputs of an internal tree circuit. -/
private def treeRename {m n : Nat} (σ : Fin m → Fin n) :
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit m →
      Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n
  | .var i => .var (σ i)
  | .const b => .const b
  | .not c => .not (treeRename σ c)
  | .and c d => .and (treeRename σ c) (treeRename σ d)
  | .or c d => .or (treeRename σ c) (treeRename σ d)

private theorem treeRename_eval {m n : Nat} (σ : Fin m → Fin n)
    (c : Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit m) (x : Bitstring n) :
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval (treeRename σ c) x =
      Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval c (fun i => x (σ i)) := by
  induction c with
  | var i => rfl
  | const b => rfl
  | not c ih => simp [treeRename, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, ih]
  | and c d ihc ihd => simp [treeRename, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, ihc, ihd]
  | or c d ihc ihd => simp [treeRename, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, ihc, ihd]

/-- Truth-table tree circuit, later compiled to the repository DAG syntax. -/
private def ttTree : ∀ {n : Nat}, (Bitstring n → Bool) →
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n
  | 0, f => .const (f (fun i => Fin.elim0 i))
  | n + 1, f =>
      let c0 := ttTree (fun y : Bitstring n => f (Fin.cases false y))
      let c1 := ttTree (fun y : Bitstring n => f (Fin.cases true y))
      .or (.and (.not (.var ⟨0, Nat.zero_lt_succ _⟩)) (treeRename Fin.succ c0))
          (.and (.var ⟨0, Nat.zero_lt_succ _⟩) (treeRename Fin.succ c1))

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
      have hx : ∀ b, x ⟨0, Nat.zero_lt_succ _⟩ = b →
          (Fin.cases (n := n) b (fun i => x (Fin.succ i)) : Bitstring (n + 1)) = x := by
        intro b hb
        funext i
        induction i using Fin.cases with
        | zero => exact hb.symm
        | succ j => rfl
      cases hb : x ⟨0, Nat.zero_lt_succ _⟩
      · simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false]
        rw [hx false hb]
      · simp only [Bool.not_true, Bool.false_and, Bool.true_and, Bool.false_or]
        rw [hx true hb]

/-- Compile the truth-table tree through the existing straight-line-to-DAG adapter. -/
private def ttDag {n : Nat} (f : Bitstring n → Bool) : DagCircuit n :=
  let cc := Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree (ttTree f)
  Pnp3.Complexity.StraightLineAdapter.toDag
    (Pnp3.Complexity.StraightLineAdapter.withOutput cc.ckt cc.out)

private theorem ttDag_eval {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n) :
    DagCircuit.eval (ttDag f) x = f x := by
  unfold ttDag
  let cc := Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree (ttTree f)
  have hWire := Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeWireSemantics
    (c := ttTree f) (x := x)
  have hBridge := Pnp3.Internal.PsubsetPpoly.StraightLine.adapter_evalWire_eq_evalWire
    (C := cc.ckt) (x := x) (i := cc.out)
  rw [Pnp3.Complexity.StraightLineAdapter.eval_toDag]
  change Pnp3.Complexity.StraightLineAdapter.evalWire cc.ckt x cc.out = f x
  rw [hBridge]
  simpa [cc, ttTree_eval] using hWire

private theorem dag_size_pos {n : Nat} (C : DagCircuit n) : 1 ≤ DagCircuit.size C := by
  unfold DagCircuit.size
  omega

/-- Per-slice DAG hardwiring for fixed-parameter Partial MCSP.
This is marked `noncomputable` only because `gapPartialMCSP_Language` is
noncomputable; the circuit itself is obtained by the bounded truth-table tree. -/
def fixedSlice_gapPartialMCSP_in_PpolyDAG
    (p : GapPartialMCSPParams) :
    InPpolyDAG (gapPartialMCSP_Language p) := by
  classical
  let n0 := Models.partialInputLen p
  let c0 : DagCircuit n0 := ttDag (gapPartialMCSP_Language p n0)
  let c0Size : Nat := DagCircuit.size c0
  have hpos : 1 ≤ c0Size := dag_size_pos c0
  refine {
    polyBound := fun m => if m = n0 then c0Size else 2
    polyBound_poly := ?_
    family := fun m => if hm : m = n0 then (hm ▸ c0 : DagCircuit m) else constFalseDag m
    family_size_le := ?_
    correct := ?_
  }
  · refine ⟨c0Size + 2, ?_⟩
    intro m
    by_cases hm : m = n0 <;> simp [hm]
    · omega
    · have htwo : 2 ≤ c0Size + 2 := by omega
      exact Nat.le_trans htwo (Nat.le_add_left _ _)
  · intro m
    by_cases hm : m = n0
    · subst hm
      simp [c0Size]
    · simp [hm, constFalseDag, DagCircuit.size]
  · intro m x
    by_cases hm : m = n0
    · subst hm
      simpa [c0] using ttDag_eval (gapPartialMCSP_Language p n0) x
    · simp only [dif_neg hm]
      have hLang : gapPartialMCSP_Language p m x = false := by
        unfold gapPartialMCSP_Language
        exact dif_neg hm
      simp [constFalseDag_eval, hLang]

/-- Canonical route hypothesis: every fixed canonical slice is DAG-hardwired.
Noncomputability is inherited from the fixed-slice language decider. -/
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
