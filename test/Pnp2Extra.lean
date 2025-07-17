import Pnp2.Agreement
import Pnp2.BoolFunc

open BoolFunc
open Agreement

namespace Pnp2ExtraTests

/-- The support of a constantly false function is empty. -/
example (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

/-- If two points agree on all coordinates of `K`, the second lies in the same subcube. -/
example {n : ℕ} {K : Finset (Fin n)} {x y : Point n}
    (h : ∀ i, i ∈ K → x i = y i) :
    y ∈ₛ Subcube.fromPoint x K := by
  simpa using Agreement.mem_fromPoint_of_agree (K := K) (x := x) (y := y) h

end Pnp2ExtraTests
