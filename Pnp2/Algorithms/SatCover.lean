import Pnp2.Boolcube
import Pnp2.Cover.Compute

namespace Pnp2
namespace Algorithms

open Boolcube
open Cover
open BoolFunc

variable {n : ℕ}

/--
`satViaCover f h` tries to find a satisfying assignment for the Boolean
function `f` using the low entropy cover returned by `buildCoverCompute`.
It enumerates the rectangles of the cover and evaluates `f` on the
canonical representative `Subcube.rep` of each subcube.
If any evaluation returns `true` the corresponding witness is returned. -/
noncomputable def satViaCover (f : BFunc n) (h : ℕ) : Option (Point n) :=
  let hH : BoolFunc.H₂ ({f} : Family n) ≤ (h : ℝ) := by
    have hcard : ({f} : Finset (BFunc n)).card = 1 := by simp
    have hzero : BoolFunc.H₂ ({f} : Family n) = 0 := by
      simpa [hcard] using BoolFunc.H₂_card_one (F := ({f} : Family n)) hcard
    have : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.zero_le h
    simpa [hzero] using this
  let Rlist := buildCoverCompute (F := ({f} : Family n)) (h := h) hH
  match Rlist.find? (fun R => f (Subcube.rep (n := n) R)) with
  | none => none
  | some R => some (Subcube.rep (n := n) R)

end Algorithms
end Pnp2
