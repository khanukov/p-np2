import LowerBounds.AsymptoticDAGBarrier

namespace Pnp3
namespace LowerBounds

/-!
Closed-route module for the historical `GapSliceFamily` carrier.

This file isolates two facts:

1. the carrier is empty in the current parameterization;
2. any theorem universally quantified over `GapSliceFamily` is therefore
   vacuous.

Keeping these statements out of `AsymptoticDAGBarrier` reduces noise in the
active asymptotic migration path (`GapSliceFamilyEventually`,
`AsymptoticDAGSliceBridgeAt`).
-/

/--
`GapSliceFamily` is empty in the current parameterization.

Reason: the structure requires a coherent index field
`hIndex : (paramsOf n β).n = n` for *all* natural `n`, while every
`GapPartialMCSPParams` carries `n_large : 8 ≤ n`. Instantiating `hIndex` at
`n = 0` yields `(paramsOf 0 β).n = 0` and `8 ≤ (paramsOf 0 β).n`, hence
`8 ≤ 0`, contradiction.
-/
theorem gapSliceFamily_isEmpty : IsEmpty GapSliceFamily := by
  refine ⟨?_⟩
  intro F
  have hIdx : (F.paramsOf 0 (0 : Rat)).n = 0 := F.hIndex 0 0
  have hLarge : 8 ≤ (F.paramsOf 0 (0 : Rat)).n := (F.paramsOf 0 (0 : Rat)).n_large
  have hImpossible : 8 ≤ 0 := by simpa [hIdx] using hLarge
  exact Nat.not_succ_le_zero 7 hImpossible

/-- Convenience corollary: there are no `GapSliceFamily` witnesses. -/
theorem not_nonempty_gapSliceFamily : ¬ Nonempty GapSliceFamily := by
  intro h
  rcases h with ⟨F⟩
  exact gapSliceFamily_isEmpty.false F

/--
Vacuity helper for legacy theorem surfaces:
any property over all `GapSliceFamily` instances is automatically true.
-/
theorem forall_gapSliceFamily_vacuous (P : GapSliceFamily → Prop) : ∀ F, P F := by
  intro F
  exact (gapSliceFamily_isEmpty.false F).elim

end LowerBounds
end Pnp3
