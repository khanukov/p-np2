import Pnp.BoolFunc

open BoolFunc

namespace BasicTests

/-- The support of a constant false function is empty. -/
lemma support_const_false (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

-- We can also verify that toggling an irrelevant coordinate leaves a
-- function unchanged by direct calculation.
example (x : Point 2) (b : Bool) :
    let f : BFunc 2 := fun y => y 0
    f x = f (Point.update x 1 b) := by
  classical
  let f : BFunc 2 := fun y => y 0
  have hneq : (0 : Fin 2) ≠ 1 := by decide
  simp [f, Point.update, hneq]

end BasicTests
