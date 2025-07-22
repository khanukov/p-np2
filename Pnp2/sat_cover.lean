import Pnp2.Boolcube
import Pnp2.cover
import Pnp2.canonical_circuit

open Classical
open Boolcube
open Cover

variable {n : ℕ}

notation x " ∈ₛ " R => R.Mem x

def Boolcube.Subcube.monochromaticFor (R : Subcube n) (f : BoolFun n) : Prop :=
  ∃ b : Bool, ∀ x, x ∈ₛ R → f x = b

namespace SATCover

/-- Choose a canonical point inside a subcube by assigning `false` to all
free coordinates.  This is the same as `Subcube.sample`. -/
def Subcube.somePoint {n : ℕ} (R : Subcube n) : Point n := Subcube.sample R

lemma somePoint_mem {n : ℕ} (R : Subcube n) : R.Mem (Subcube.somePoint R) := by
  simpa [Subcube.somePoint] using Subcube.sample_mem (n := n) R

/-- Enumerate all rectangles in `cover` and evaluate `Φ` on a witness
point from each rectangle.  The algorithm succeeds if any evaluation
returns `true`. -/
noncomputable def satByCover {n : ℕ}
    (Φ : Circuit n) (cover : Finset (Subcube n)) : Bool :=
  decide (∃ R ∈ cover, Circuit.eval Φ (Subcube.somePoint R) = true)

lemma satByCover_true_of_sat {n : ℕ} {Φ : Circuit n} {cover : Finset (Subcube n)}
    (hmono : ∀ R ∈ cover, Subcube.monochromaticFor R (Circuit.eval Φ))
    (hcov : ∀ x, Circuit.eval Φ x = true → ∃ R ∈ cover, x ∈ₛ R) :
    (∃ x, Circuit.eval Φ x = true) → satByCover Φ cover = true := by
  classical
  intro hx
  rcases hx with ⟨x, hx⟩
  rcases hcov x hx with ⟨R, hR, hxR⟩
  rcases hmono R hR with ⟨b, hb⟩
  have hxcol : Circuit.eval Φ x = b := hb hxR
  have hbtrue : b = true := by
    calc
      b = Circuit.eval Φ x := by simpa using hxcol.symm
      _ = true := hx
  have hpoint : Circuit.eval Φ (Subcube.somePoint R) = b := hb (somePoint_mem R)
  have hpoint_true : Circuit.eval Φ (Subcube.somePoint R) = true := by simpa [hbtrue] using hpoint
  have hExists : ∃ R ∈ cover, Circuit.eval Φ (Subcube.somePoint R) = true :=
    ⟨R, hR, hpoint_true⟩
  simpa [satByCover, hExists]

lemma satByCover_complete {n : ℕ} {Φ : Circuit n} {cover : Finset (Subcube n)} :
    satByCover Φ cover = true → ∃ x, Circuit.eval Φ x = true := by
  classical
  intro h
  dsimp [satByCover] at h
  have hExists : ∃ R ∈ cover, Circuit.eval Φ (Subcube.somePoint R) = true :=
    of_decide_eq_true h
  rcases hExists with ⟨R, _, hval⟩
  exact ⟨Subcube.somePoint R, hval⟩

end SATCover
