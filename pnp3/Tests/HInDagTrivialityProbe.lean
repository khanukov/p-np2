import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Complexity.PsubsetPpolyInternal.Simulation

namespace Pnp3
namespace Tests
namespace HInDagTrivialityProbe

open ComplexityInterfaces
open Models
open Magnification


/-!
This L0 probe is infrastructure/audit work, not lower-bound progress.  The
single mathematical point is benign hardwiring: at a fixed input length every
Boolean slice has a non-uniform DAG, and `gapPartialMCSP_Language` is
definitionally false away from its encoded slice.
-/

/-- One-gate constant-false DAG used off the single relevant slice. -/
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => .const false
  output := .gate ⟨0, Nat.lt.base 0⟩

@[simp] private theorem constFalseDag_size {n : Nat} :
    DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, DagCircuit.size]

@[simp] private theorem constFalseDag_eval {n : Nat} (x : Bitstring n) :
    DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, DagCircuit.eval, DagCircuit.eval.evalGateAt]

/--
Truth-table DAG obtained by compiling the existing finite tree truth-table
circuit.  This is `noncomputable` only because the imported truth-table builder
enumerates the finite Boolean cube using classical finite-set machinery; no
unbounded oracle or new assumption is introduced.
-/
private noncomputable def ttDag {n : Nat} (f : Bitstring n → Bool) : DagCircuit n :=
  let c := Pnp3.Internal.PsubsetPpoly.Simulation.Boolcube.Circuit.truthTableCircuit f
  let cc := Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree c
  Pnp3.Complexity.StraightLineAdapter.toDag
    (Pnp3.Complexity.StraightLineAdapter.withOutput cc.ckt cc.out)

/-- Correctness of the truth-table DAG. -/
private theorem ttDag_eval {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n) :
    DagCircuit.eval (ttDag f) x = f x := by
  classical
  let c := Pnp3.Internal.PsubsetPpoly.Simulation.Boolcube.Circuit.truthTableCircuit f
  let cc := Pnp3.Internal.PsubsetPpoly.StraightLine.compileTree c
  have hWire :
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire (C := cc.ckt) (x := x) cc.out =
        Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval c x := by
    simpa [cc] using Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeWireSemantics c x
  have hTree : Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval c x = f x :=
    Pnp3.Internal.PsubsetPpoly.Simulation.Boolcube.Circuit.eval_truthTableCircuit f x
  change Pnp3.Complexity.StraightLineAdapter.evalWire cc.ckt x cc.out = f x
  rw [Pnp3.Internal.PsubsetPpoly.StraightLine.adapter_evalWire_eq_evalWire]
  exact hWire.trans hTree

/--
Per-slice `InPpolyDAG` witness by hardwiring the only non-false length.  The
noncomputability is inherited from `ttDag`, i.e. from a bounded truth-table
enumeration at the fixed length `partialInputLen p`.
-/
noncomputable def fixedSlice_gapPartialMCSP_in_PpolyDAG
    (p : GapPartialMCSPParams) :
    InPpolyDAG (gapPartialMCSP_Language p) := by
  classical
  let n₀ := partialInputLen p
  let c₀ : DagCircuit n₀ := ttDag (gapPartialMCSP_Language p n₀)
  let c₀_size : Nat := DagCircuit.size c₀
  refine {
    polyBound := fun m => if m = n₀ then c₀_size else 2
    polyBound_poly := ?_
    family := fun m => if hm : m = n₀ then hm ▸ c₀ else constFalseDag m
    family_size_le := ?_
    correct := ?_
  }
  · refine ⟨c₀_size + 2, ?_⟩
    intro m
    by_cases hm : m = n₀
    · simp [hm]
      exact Nat.le_trans (by omega : c₀_size ≤ c₀_size + 2)
        (Nat.le_add_left _ _)
    · simp [hm]
      exact Nat.le_trans (by omega : 2 ≤ c₀_size + 2) (Nat.le_add_left _ _)
  · intro m
    by_cases hm : m = n₀
    · subst hm
      simp [c₀_size]
    · simp [hm]
  · intro m x
    by_cases hm : m = n₀
    · subst hm
      simp only
      exact ttDag_eval (gapPartialMCSP_Language p n₀) x
    · have hLang : gapPartialMCSP_Language p m x = false := by
        simp [gapPartialMCSP_Language, n₀, hm]
      simp [hm, hLang]

/--
The route hypothesis surface at the canonical asymptotic instantiation.  The
value is noncomputable only because each fixed slice reuses the bounded
truth-table hardwiring witness above.
-/
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
