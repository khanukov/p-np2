import Pnp2.Boolcube
import Pnp2.cover
import Pnp2.canonical_circuit

open Classical
open Cover

open Boolcube

variable {n : ℕ}

namespace Boolcube.Subcube

/-- A subcube `R` is *monochromatic* for a Boolean function `f` if `f` is
constant on all points of `R`. -/
def monochromaticFor (R : Subcube n) (f : Point n → Bool) : Prop :=
  ∃ b : Bool, ∀ {x : Point n}, R.Mem x → f x = b

end Boolcube.Subcube

namespace SATCover

/--
Evaluate `Φ` on the canonical sample point of each rectangle in `cover`.
This point assigns `false` to all free coordinates, so it witnesses the
value of `Φ` on that subcube.  The procedure succeeds if some rectangle
evaluates to `true` on its sample.
-/
noncomputable def satByCover {n : ℕ}
    (Φ : Circuit n) (cover : Finset (Subcube n)) : Bool :=
  decide (∃ R ∈ cover, Circuit.eval Φ (Subcube.sample R) = true)

lemma satByCover_true_of_sat {n : ℕ} {Φ : Circuit n} {cover : Finset (Subcube n)}
    (hmono : ∀ R ∈ cover, Subcube.monochromaticFor R (Circuit.eval Φ))
    (hcov : ∀ x, Circuit.eval Φ x = true → ∃ R ∈ cover, R.Mem x) :
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
  have hpoint : Circuit.eval Φ (Subcube.sample R) = b := hb (Subcube.sample_mem R)
  have hpoint_true : Circuit.eval Φ (Subcube.sample R) = true := by
    simpa [hbtrue] using hpoint
  have hExists : ∃ R ∈ cover, Circuit.eval Φ (Subcube.sample R) = true :=
    ⟨R, hR, hpoint_true⟩
  simpa [satByCover, hExists]

lemma satByCover_complete {n : ℕ} {Φ : Circuit n} {cover : Finset (Subcube n)} :
    satByCover Φ cover = true → ∃ x, Circuit.eval Φ x = true := by
  classical
  intro h
  dsimp [satByCover] at h
  have hExists : ∃ R ∈ cover, Circuit.eval Φ (Subcube.sample R) = true :=
    of_decide_eq_true h
  rcases hExists with ⟨R, _, hval⟩
  exact ⟨Subcube.sample R, hval⟩

end SATCover
