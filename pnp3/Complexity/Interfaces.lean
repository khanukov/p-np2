/-!
  pnp3/Complexity/Interfaces.lean

  **Legacy interface** to complexity classes for magnification machinery.

  ## Status (Phase 1 - In Progress)

  This file provides abstract Props for compatibility with existing magnification code.
  Full definitions of P, NP, P/poly are now in `Complexity/ComplexityClasses.lean`.

  **Axiom Status:**
  * `NP_not_subset_Ppoly` — ⚠️ AXIOM (will be derived from GapMCSP hardness + magnification)
  * `P_subset_Ppoly` — ⚠️ AXIOM (proven in Pnp2, can be ported, ~11K LOC)
  * `P_subset_Ppoly_proof` — ⚠️ AXIOM (instance of above)
  * `P_ne_NP` — ⚠️ AXIOM (target theorem, will be derived)
  * `P_ne_NP_of_nonuniform_separation` — ✅ **NOW PROVEN** in `NP_Separation.lean`!

  ## Migration Plan

  Phase 1 (current): Create real definitions in ComplexityClasses.lean
  Phase 2 (next): Migrate magnification files to use Set Language instead of Props
  Phase 3 (later): Remove this file entirely

  ## New Developments

  See:
  - `Complexity/ComplexityClasses.lean` - full definitions of P, NP, P/poly
  - `Complexity/NP_Separation.lean` - **PROOF** of P≠NP logical step (no axioms!)
-/

namespace Pnp3
namespace ComplexityInterfaces

/-- Заглушка для утверждения `NP ⊄ P/poly`. -/
axiom NP_not_subset_Ppoly : Prop

/-- Интерфейс к доказанному в `pnp2` включению `P ⊆ P/poly`. -/
axiom P_subset_Ppoly : Prop

/-- Доказательство включения `P ⊆ P/poly`, заимствованное из `pnp2`. -/
axiom P_subset_Ppoly_proof : P_subset_Ppoly

/-- Итоговое целевое утверждение `P ≠ NP`. -/
axiom P_ne_NP : Prop

/--
  Классический вывод: если `NP ⊄ P/poly`, но `P ⊆ P/poly`, то `P ≠ NP`.
  Подробное доказательство реализовано в `Pnp2/NP_separation.lean`.
-/
axiom P_ne_NP_of_nonuniform_separation
  (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) : P_ne_NP

end ComplexityInterfaces
end Pnp3
