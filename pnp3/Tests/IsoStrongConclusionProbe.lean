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

/--
L0 probe helper: unfold `IsoStrongFamilyEventually` once and package the
pointwise forcing payload at one concrete `(n, β, C)`.

This lemma is intentionally lightweight and infrastructure-facing:
it does not settle the canonical conclusion (positive or negative), but it gives
an explicit reusable elimination form for L1 work.
-/
theorem isoStrong_unpack_at
    (W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym)
    (hIso :
      IsoStrongFamilyEventually
        (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
        (globalWitness_to_hInDag W)) :
    ∃ β0 : Rat, 0 < β0 ∧
      ∃ κ : Nat → Rat → Nat,
        ∃ nIso : Rat → Nat,
          (∀ n : Nat, ∀ β : Rat,
            0 < β → β < β0 →
            n ≥ max
              (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).N0
              (nIso β) →
            ∀ C : DagCircuit
              (GapSliceFamilyEventually.encodedLen
                (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
                n β),
              ppolyDAGSizeBoundOnSlicesEventually
                (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
                (globalWitness_to_hInDag W)
                n β 1 (DagCircuit.size C) →
              CorrectOnPromiseSlice C
                (gapSliceOfParams
                  ((eventualGapSliceFamily_of_asymptotic
                    canonicalAsymptoticHAsym).paramsOf n β)) →
                ∃ yYes : Bitstring
                  (GapSliceFamilyEventually.encodedLen
                    (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
                    n β),
                  yYes ∈ (gapSliceOfParams
                    ((eventualGapSliceFamily_of_asymptotic
                      canonicalAsymptoticHAsym).paramsOf n β)).Yes ∧
                  ValidEncoding
                    ((eventualGapSliceFamily_of_asymptotic
                      canonicalAsymptoticHAsym).paramsOf n β) yYes ∧
                  ∃ D : Finset
                    (Fin
                      (GapSliceFamilyEventually.tableLen
                        (eventualGapSliceFamily_of_asymptotic
                          canonicalAsymptoticHAsym)
                        n β)),
                    D.card ≤ κ n β ∧
                    ∀ z : Bitstring
                      (GapSliceFamilyEventually.encodedLen
                        (eventualGapSliceFamily_of_asymptotic
                          canonicalAsymptoticHAsym)
                        n β),
                      ValidEncoding
                        ((eventualGapSliceFamily_of_asymptotic
                          canonicalAsymptoticHAsym).paramsOf n β) z →
                      AgreeOnValues
                        (p :=
                          (eventualGapSliceFamily_of_asymptotic
                            canonicalAsymptoticHAsym).paramsOf n β)
                        D yYes z →
                      z ∈ (gapSliceOfParams
                        ((eventualGapSliceFamily_of_asymptotic
                          canonicalAsymptoticHAsym).paramsOf n β)).Yes) ∧
          (∀ n : Nat, ∀ β : Rat,
            0 < β → β < β0 →
            n ≥ max
              (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).N0
              (nIso β) →
              (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).Mof n
                  ((eventualGapSliceFamily_of_asymptotic
                    canonicalAsymptoticHAsym).Tof n β) <
                2 ^
                  (GapSliceFamilyEventually.tableLen
                    (eventualGapSliceFamily_of_asymptotic
                      canonicalAsymptoticHAsym)
                    n β -
                    κ n β)) := by
  simpa [IsoStrongFamilyEventually] using hIso

end IsoStrongConclusionProbe
end Tests
end Pnp3
