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
L0 partial probe for the canonical iso-strong conclusion.

We do not settle Direction N or Direction P in this file. Instead, we extract a
reusable local payload: once an `IsoStrongFamilyEventually` witness is assumed,
the forcing package is available at any admissible `(n, β)` for any small and
promise-correct DAG `C` on the canonical family.

This is intended as a clean L1 starting point: subsequent sessions can focus on
constructing either a contradiction (Direction N) or a constructive center
(Direction P), without repeatedly unpacking the outer eventual quantifiers.
-/
theorem isoStrong_canonical_forcing_payload
    (W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym)
    (hStrong :
      IsoStrongFamilyEventually
        (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
        (globalWitness_to_hInDag W)) :
    ∃ β0 : Rat, 0 < β0 ∧
      ∃ κ : Nat → Rat → Nat,
        ∃ nIso : Rat → Nat,
          (∀ n : Nat, ∀ β : Rat,
            0 < β → β < β0 → n ≥ max
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
                      canonicalAsymptoticHAsym).paramsOf n β)
                    yYes ∧
                  ∃ D : Finset (Fin
                    (GapSliceFamilyEventually.tableLen
                      (eventualGapSliceFamily_of_asymptotic
                        canonicalAsymptoticHAsym) n β)),
                    D.card ≤ κ n β ∧
                    ∀ z : Bitstring
                      (GapSliceFamilyEventually.encodedLen
                        (eventualGapSliceFamily_of_asymptotic
                          canonicalAsymptoticHAsym)
                        n β),
                      ValidEncoding
                        ((eventualGapSliceFamily_of_asymptotic
                          canonicalAsymptoticHAsym).paramsOf n β)
                        z →
                      AgreeOnValues
                        (p := (eventualGapSliceFamily_of_asymptotic
                          canonicalAsymptoticHAsym).paramsOf n β)
                        D yYes z →
                        z ∈ (gapSliceOfParams
                          ((eventualGapSliceFamily_of_asymptotic
                            canonicalAsymptoticHAsym).paramsOf n β)).Yes) ∧
          (∀ n : Nat, ∀ β : Rat,
            0 < β → β < β0 → n ≥ max
              (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).N0
              (nIso β) →
              (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).Mof
                n
                ((eventualGapSliceFamily_of_asymptotic
                  canonicalAsymptoticHAsym).Tof n β) <
                2 ^
                  (GapSliceFamilyEventually.tableLen
                    (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
                    n β - κ n β)) := by
  simpa using hStrong

/--
A compact corollary used by L1: instantiate the forcing branch at fixed
admissible parameters, leaving only the combinatorial core to solve.
-/
theorem isoStrong_canonical_forcing_at
    (W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym)
    (hStrong :
      IsoStrongFamilyEventually
        (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
        (globalWitness_to_hInDag W)) :
    ∀ n β,
      (∃ β0 : Rat, 0 < β0 ∧
        ∃ κ : Nat → Rat → Nat,
          ∃ nIso : Rat → Nat,
            0 < β ∧ β < β0 ∧
            n ≥ max
              (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).N0
              (nIso β) ∧
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
                      canonicalAsymptoticHAsym).paramsOf n β)).Yes) := by
  intro n β
  rcases isoStrong_canonical_forcing_payload (W := W) hStrong with
    ⟨β0, hβ0, κ, nIso, hForce, _hSlack⟩
  refine ⟨β0, hβ0, κ, nIso, ?_⟩
  intro hβPos hβLt hn C hSize hCorrect
  rcases hForce n β hβPos hβLt hn C hSize hCorrect with
    ⟨yYes, hyYes, _hyValid, _D, _hDCard, _hAllYes⟩
  exact ⟨yYes, hyYes⟩

end IsoStrongConclusionProbe
end Tests
end Pnp3
