import Pnp.BoolFunc
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold

open Finset

namespace BoolFunc

variable {n : ℕ} [Fintype (Point n)]

/-- `sensitivityAt f x` is the number of coordinates on which flipping the
    input changes the value of `f`. -/
def sensitivityAt (f : BFunc n) (x : Point n) : ℕ :=
  (Finset.univ.filter fun i => f (Point.update x i (!x i)) ≠ f x).card

/-- The (block) sensitivity of a Boolean function.  We take the maximum of
    `sensitivityAt` over all points of the cube. -/
def sensitivity (f : BFunc n) : ℕ :=
  (Finset.univ.sup fun x => sensitivityAt f x)

lemma sensitivityAt_le (f : BFunc n) (x : Point n) :
    sensitivityAt f x ≤ sensitivity f :=
  by
    classical
    have hx : x ∈ (Finset.univ : Finset (Point n)) := by simp
    exact Finset.le_sup (s := Finset.univ) hx

end BoolFunc

