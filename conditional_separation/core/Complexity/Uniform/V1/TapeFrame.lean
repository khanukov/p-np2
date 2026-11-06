import Complexity.Uniform.V1.SequentialComposition

/-! G3s Infrastructure: a tape cell that is never scanned can be updated
before or after a run. Concrete users must discharge the avoidance premise. -/
namespace Pnp3.Complexity.Uniform.V1

/-- Exact execution commutes with updating an unvisited cell. -/
theorem UniformTM.run_update_of_unvisited
    (M : UniformTM) {n B : Nat} (c : Config M.stateCount n B)
    (p : Fin (tapeLength n B)) (b : Option Bool) (T : Nat)
    (havoid : ∀ t, t < T → (M.run t c).head ≠ p) :
    M.run T {c with tape := Function.update c.tape p b} =
      {(M.run T c) with tape := Function.update (M.run T c).tape p b} := by
  have step_update (d : Config M.stateCount n B) (hp : d.head ≠ p) :
      M.stepConfig {d with tape := Function.update d.tape p b} =
        {M.stepConfig d with tape := Function.update (M.stepConfig d).tape p b} := by
    apply Config.ext_parts
    · simp [UniformTM.stepConfig, Function.update_apply, hp]
    · simp [UniformTM.stepConfig, Function.update_apply, hp]
    · funext i
      by_cases hi : i = p <;> by_cases hh : i = d.head <;>
        simp_all [UniformTM.stepConfig, Function.update_apply]
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [UniformTM.run, ih (fun t ht => havoid t (by omega))]
    exact step_update _ (havoid T (by omega))

end Pnp3.Complexity.Uniform.V1
