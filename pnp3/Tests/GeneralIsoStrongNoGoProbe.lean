import Mathlib
import Tests.CircuitCountTraceBoundProbe

namespace Pnp3
namespace Tests
namespace GeneralIsoStrongNoGoProbe

/--
Finite pigeonhole helper used by the generalized diagonal argument:
if a finite trace image has cardinality below `2^|α|`, a Boolean label
outside the image exists.
-/
theorem exists_label_not_in_trace_image_of_card_lt
    {α : Type} [Fintype α] [DecidableEq (α → Bool)]
    (S : Finset (α → Bool))
    (h : S.card < 2 ^ Fintype.card α) :
    ∃ label : α → Bool, label ∉ S := by
  classical
  have hAll : S.card < Fintype.card (α → Bool) := by
    simpa [Fintype.card_fun, Fintype.card_bool] using h
  by_contra hNo
  push_neg at hNo
  have hEq : S = Finset.univ := Finset.eq_univ_of_forall hNo
  have hCardEq : S.card = Fintype.card (α → Bool) := by
    simpa [hEq] using (Finset.card_univ : (Finset.univ : Finset (α → Bool)).card = _)
  exact (Nat.lt_irrefl _ ) (hCardEq ▸ hAll)

/-- L1 status marker: only the finite-image helper is landed in this probe. -/
theorem generalIsoStrong_L1_partial_status : True := by
  trivial

end GeneralIsoStrongNoGoProbe
end Tests
end Pnp3
