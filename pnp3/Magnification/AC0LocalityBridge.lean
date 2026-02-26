import AC0.MultiSwitching.Main
import Core.ShrinkageWitness
import Complexity.Interfaces
import Models.Model_PartialMCSP
import ThirdPartyFacts.Facts_Switching
import ThirdPartyFacts.PartialLocalityLift
import Facts.LocalityLift.Exports

/-!
  pnp3/Magnification/AC0LocalityBridge.lean

  AC0-specific constructive bridge for I-4.

  This module intentionally avoids any global conversion
  `PpolyFormula -> AC0`. Instead, it assumes an explicit AC0/CNF family
  witness at the bridge boundary and reuses the constructive common-CCDT
  pipeline from `AC0.MultiSwitching.Main`.
-/

namespace Pnp3
namespace Magnification
namespace AC0LocalityBridge

open Core
open AC0.MultiSwitching
open Models
open ComplexityInterfaces

/--
Path A bridge (constructive):
from an explicit CNF-family witness `F` and the strict counting inequality,
construct a nontrivial `PartialCertificate` for the restricted family.
-/
theorem partialCertificate_from_common_canonical_params
    {n w : Nat} (F : FormulaFamily n w)
    (ht : tParam F.length n ≤ sParam n w)
    [DecidablePred (BadEvent_common (F := F) (tParam F.length n))]
    (hbound :
      (R_s (n := n) (sParam n w - tParam F.length n)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ (tParam F.length n)
        < (R_s (n := n) (sParam n w)).card) :
    ∃ ρ ∈ R_s (n := n) (sParam n w),
      ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamilyRestrict (ρ := ρ) F)),
        ℓ = 0 ∧ C.depthBound = tParam F.length n ∧
          C.epsilon = (1 : Q) / (n + 2) := by
  exact stage1_6_complete_canonicalCCDT_params_common
    (F := F) ht hbound

/--
Derived AC0 bridge to a full shrinkage witness.
-/
theorem shrinkage_from_common_canonical_params
    {n w : Nat} (F : FormulaFamily n w)
    (ht : tParam F.length n ≤ sParam n w)
    [DecidablePred (BadEvent_common (F := F) (tParam F.length n))]
    (hbound :
      (R_s (n := n) (sParam n w - tParam F.length n)).card
          * (2 * n * (w + 1) * (F.length + 1)) ^ (tParam F.length n)
        < (R_s (n := n) (sParam n w)).card) :
    ∃ ρ ∈ R_s (n := n) (sParam n w), ∃ (S : Shrinkage n),
      S.F = evalFamilyRestrict (ρ := ρ) F ∧
      S.t = tParam F.length n ∧
      S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ρ, hρ, ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_common_canonical_params
      (F := F) ht hbound
  subst hℓ
  refine ⟨ρ, hρ, C.toShrinkage, ?_, ?_, ?_⟩
  · simpa using (PartialCertificate.toShrinkage_family (C := C))
  · simpa [PartialCertificate.toShrinkage_depth, hdepth]
  · simpa [PartialCertificate.toShrinkage_epsilon, hε]

/--
I-2B target interface: data that a depth-aware multi-switching/CCDT layer must
provide for each extracted strict formula witness.

The package intentionally asks for:
1) explicit AC0-family provenance (`ac0`, `F`, AC0 witness, multi-switching witness),
2) concrete support-derived numeric bounds required by the certificate route.
-/
structure FormulaSupportBoundsFromMultiSwitchingContract where
  package :
    ∀ {p : GapPartialMCSPParams}
      (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
      let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
        Classical.choose hFormula
      let c := wf.family (Models.partialInputLen p)
      let alive := ComplexityInterfaces.FormulaCircuit.support c
      let rPartial : Facts.LocalityLift.Restriction (Models.partialInputLen p) :=
        Facts.LocalityLift.Restriction.ofVector alive (fun _ => false)
      let hlen :
        Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) =
          Models.partialInputLen p :=
        ThirdPartyFacts.inputLen_toFactsPartial p
      let rFacts :
        Facts.LocalityLift.Restriction
          (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) :=
        ThirdPartyFacts.castRestriction hlen.symm rPartial
      ∃ (ac0 : ThirdPartyFacts.AC0Parameters) (F : Core.Family ac0.n),
        ac0.n = Models.partialInputLen p ∧
        ThirdPartyFacts.AC0FamilyWitnessProp ac0 F ∧
        Nonempty (ThirdPartyFacts.AC0MultiSwitchingWitness ac0 F) ∧
        rFacts.alive.card ≤
          Facts.LocalityLift.polylogBudget
            (Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)) ∧
        Facts.LocalityLift.LocalCircuitSmallEnough
          { n := Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p)
            , M := ComplexityInterfaces.FormulaCircuit.size c * rFacts.alive.card.succ
            , ℓ := rFacts.alive.card
            , depth := 0 } ∧
        rFacts.alive.card ≤
          Facts.LocalityLift.inputLen (ThirdPartyFacts.toFactsParamsPartial p) / 4

end AC0LocalityBridge
end Magnification
end Pnp3
