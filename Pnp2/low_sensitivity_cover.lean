import Pnp2.BoolFunc.Sensitivity
import Pnp2.BoolFunc

open BoolFunc

namespace BoolFunc

variable {n : ℕ}

/-- **Low-sensitivity cover** (statement only).  If every function in the
    family has sensitivity at most `s`, then there exists a small set of
    subcubes covering all ones of the family.  The proof will use decision
    trees or the Gopalan--Moshkovitz--Oliveira bound.  Here we only record the
    statement. -/
lemma low_sensitivity_cover (F : Family n) (s : ℕ)
    [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (10 * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- A full proof would build a decision tree for each `f` of depth ≤ C * s * log n
  -- and collect the resulting subcubes.  This is beyond the current development.
  admit

end BoolFunc

