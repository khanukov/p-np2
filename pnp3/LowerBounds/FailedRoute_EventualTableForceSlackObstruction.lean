import LowerBounds.AsymptoticDAGBarrierTheorems

namespace Pnp3
namespace LowerBounds

/-!
`FailedRoute_EventualTableForceSlackObstruction`

This module isolates one closed/deprecated route:

*source contract* `tableForceFamilyEventually + slack` (and convenience
`sliceConst` packaging) for the intended MCSP semantics.

Main outcome:
the route is internally inconsistent for nontrivial eventual slices, so it
should not be used as an active target for family instantiation.
-/

/--
Convenience wrapper: the `tableForce + slack` source package is contradictory
for the intended counting semantics.
-/
theorem failedRoute_tableForce_slack
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hTable : tableForceFamilyEventually F β0 κ nIso)
    (hSlack :
      ∀ n : Nat, ∀ β : Rat,
        0 < β → β < β0 → n ≥ max F.N0 (nIso β) →
          F.Mof n (F.Tof n β) <
            2 ^ (GapSliceFamilyEventually.tableLen F n β - κ n β)) :
    False :=
  false_of_tableForceFamilyEventually_and_slack
    F β0 hβ0 κ nIso hTable hSlack

/--
Convenience wrapper: `tableForce` is also incompatible with the `sliceConst`
convenience global-language packaging.
-/
theorem failedRoute_tableForce_sliceConst
    (F : GapSliceFamilyEventually)
    (β0 : Rat)
    (hβ0 : 0 < β0)
    (κ : Nat → Rat → Nat)
    (nIso : Rat → Nat)
    (hTable : tableForceFamilyEventually F β0 κ nIso)
    (hSliceConst : sliceConstFamilyEventually F)
    (hDecodeEncode :
      ∀ {n : Nat} (T : Models.PartialTruthTable n),
        Models.decodePartial (Models.encodePartial T) = T) :
    False :=
  false_of_tableForceFamilyEventually_and_sliceConst
    F β0 hβ0 κ nIso hTable hSliceConst hDecodeEncode

end LowerBounds
end Pnp3
