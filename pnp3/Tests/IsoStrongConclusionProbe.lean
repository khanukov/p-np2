import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.FinalResultMainline
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import «pnp3».Tests.GlobalHInDagContractProbe

namespace Pnp3
namespace Tests
namespace IsoStrongConclusionProbe

open ComplexityInterfaces
open Models
open Magnification
open LowerBounds
open GlobalHInDagContractProbe

/-- Local alias for the canonical eventual family used in this L0 probe. -/
private def canonicalF : GapSliceFamilyEventually :=
  eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym

/--
At any fixed `(n, β)`, if the agreement set `D` is the full coordinate set,
then the iso-strong slack inequality cannot hold.

This is the core mechanical blocker for the "force singleton by fixing every
value coordinate" strategy from the D0 audit.
-/
theorem slack_fails_for_full_coordinates
    (n : Nat) (β : Rat)
    (hSlack :
      canonicalF.Mof n (canonicalF.Tof n β) <
        2 ^
          (GapSliceFamilyEventually.tableLen canonicalF n β -
            (Finset.univ : Finset (Fin (GapSliceFamilyEventually.tableLen canonicalF n β))).card)) :
    False := by
  have hExpZero :
      GapSliceFamilyEventually.tableLen canonicalF n β -
        (Finset.univ : Finset (Fin (GapSliceFamilyEventually.tableLen canonicalF n β))).card = 0 := by
    simp
  have hPowOne :
      2 ^
          (GapSliceFamilyEventually.tableLen canonicalF n β -
            (Finset.univ : Finset (Fin (GapSliceFamilyEventually.tableLen canonicalF n β))).card) = 1 := by
    simp [hExpZero]
  have hPos : 1 ≤ canonicalF.Mof n (canonicalF.Tof n β) := by
    simpa [canonicalF] using (Nat.one_le_circuitCountBound _ _)
  have hNotLtOne : ¬ canonicalF.Mof n (canonicalF.Tof n β) < 1 :=
    Nat.not_lt_of_ge hPos
  exact hNotLtOne (hPowOne ▸ hSlack)

/--
Partial L0 landing: for canonical parameters, any iso-strong witness must use
an agreement set `D` that is strictly smaller than the full coordinate set.

This is a useful prerequisite for the Direction N pigeonhole route, but it does
not by itself prove `¬ IsoStrongFamilyEventually ...`.
-/
theorem any_isoStrong_witness_has_nonfull_D
    {n : Nat} {β : Rat}
    {D : Finset (Fin (GapSliceFamilyEventually.tableLen canonicalF n β))}
    (hSlack :
      canonicalF.Mof n (canonicalF.Tof n β) <
        2 ^ (GapSliceFamilyEventually.tableLen canonicalF n β - D.card)) :
    D.card < GapSliceFamilyEventually.tableLen canonicalF n β := by
  by_contra hNotLt
  have hGe : GapSliceFamilyEventually.tableLen canonicalF n β ≤ D.card :=
    Nat.le_of_not_lt hNotLt
  have hLe : D.card ≤ GapSliceFamilyEventually.tableLen canonicalF n β := by
    exact Finset.card_le_univ
  have hEq : D.card = GapSliceFamilyEventually.tableLen canonicalF n β :=
    Nat.le_antisymm hLe hGe
  have hZero : GapSliceFamilyEventually.tableLen canonicalF n β - D.card = 0 := by
    simp [hEq]
  have hPowOne : 2 ^ (GapSliceFamilyEventually.tableLen canonicalF n β - D.card) = 1 := by
    simp [hZero]
  have hPos : 1 ≤ canonicalF.Mof n (canonicalF.Tof n β) := by
    simpa [canonicalF] using (Nat.one_le_circuitCountBound _ _)
  exact (Nat.not_lt_of_ge hPos) (hPowOne ▸ hSlack)

end IsoStrongConclusionProbe
end Tests
end Pnp3
