import AC0.MultiSwitching.Main
import Core.ShrinkageWitness

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

end AC0LocalityBridge
end Magnification
end Pnp3

