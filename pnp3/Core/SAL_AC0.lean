import Core.SAL_Core
import ThirdPartyFacts.Facts_Switching
import Core.ShrinkageAC0

/-!
  pnp3/Core/SAL_AC0.lean

  Specialisation of the abstract SAL pipeline to AC⁰ families.  As soon as a
  multi-switching witness is available (via the typeclass
  `ThirdPartyFacts.HasMultiSwitchingWitness`) we can feed it to the generic
  `SAL_from_Shrinkage` lemma and immediately obtain an atlas together with the
  quantitative bounds promised in Step A of the roadmap.

  The goal of this module is bookkeeping rather than new combinatorics: we wrap
  the statements proven in `ThirdPartyFacts/Facts_Switching.lean` into a tidy
  interface that downstream developments (steps B and beyond) can import without
  worrying about the details of partial certificates.
-/

namespace Pnp3
namespace Core

open ThirdPartyFacts

section

variable (params : AC0Parameters) (F : Family params.n)
variable [HasAC0PartialWitness params F]

/--
Atlas returned by the AC⁰ shrinkage witness.  The definition simply reuses the
helper from `ThirdPartyFacts`, but keeping it in the `Core` namespace emphasises
that no external axioms are involved: as soon as a witness is provided, the SAL
conversion is constructive.
-/
noncomputable def atlasAC0 : Atlas params.n :=
  atlas_from_AC0 params F

/--
The specialised SAL statement: any AC⁰ witness immediately yields an atlas that
covers the whole family `F` with the claimed error parameter.
-/
theorem worksFor_atlasAC0 : WorksFor (atlasAC0 (params := params) (F := F)) F := by
  classical
  simpa [atlasAC0] using atlas_from_AC0_works (params := params) (F := F)

/--
Depth bound inherited from the multi-switching witness.  This is a direct
re-export of `certificate_from_AC0_depth_bound` tailored to the new notation.
-/
theorem atlasAC0_depth_le :
    (Core.Shrinkage.depthBound (S := certificate_from_AC0 params F))
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) :=
  certificate_from_AC0_depth_bound (params := params) (F := F)

/--
Leaf dictionary bound for the atlas obtained from the AC⁰ witness.  This
packages the statement in a form that is convenient for the counting step.
-/
theorem atlasAC0_dict_length_le :
    (atlasAC0 (params := params) (F := F)).dict.length
      ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
  classical
  simpa [atlasAC0]
    using partial_from_AC0_leafDict_len_le (params := params) (F := F)

/--
Error control: the AC⁰ witness guarantees that the shrinkage certificate stays
below `1 / (n + 2)`, and hence the resulting atlas inherits the same bound.
-/
lemma atlasAC0_epsilon_le_inv :
    (atlasAC0 (params := params) (F := F)).epsilon
      ≤ (1 : Q) / (params.n + 2) := by
  classical
  simpa [atlasAC0]
    using certificate_from_AC0_eps_bound (params := params) (F := F)

/-- A convenient corollary used when matching the counting lemmas. -/
lemma atlasAC0_epsilon_le_half :
    (atlasAC0 (params := params) (F := F)).epsilon ≤ (1 : Q) / 2 := by
  classical
  simpa [atlasAC0]
    using certificate_from_AC0_eps_le_half (params := params) (F := F)

end

end Core
end Pnp3
