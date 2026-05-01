import Magnification.FinalResultMainline
import Magnification.UnconditionalResearchGap

/-!
# Refuted predicates registry

Research Governance v0.1, PR 4a (`Engineering Execution Plan v0.2.1`).

Centralised audit point for predicates whose `→ False` proofs are
recorded in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.

This file does **not** redefine those predicates; their definition
homes remain unchanged so that PR 4a does not introduce import cycles
(see `Phase0_Audit_Surface.md` §1.2 and the
`Engineering Execution Plan v0.2.1` notes on cycle risk for
`MagnificationAssumptions[_fromPipeline]`).  Each entry below is a
canonical `RefutedPredicate_*` alias over the existing definition,
created so that:

1. Guard scripts can recognise refuted-predicate use sites by a single
   uniform name family.
2. Future code is encouraged to refer to refuted predicates only via
   their `RefutedPredicate_*` audit alias.
3. The physical move of these definitions into
   `pnp3/RefutedPredicates/` (PR 4b) becomes a mechanical follow-up
   after the FinalResult file split (PR 14).

The six refuted predicates and their definition homes:

| Refuted predicate                                  | Definition home                                                      |
| -------------------------------------------------- | -------------------------------------------------------------------- |
| `FormulaSupportRestrictionBoundsPartial`           | `pnp3/Magnification/LocalityProvider_Partial.lean:239`               |
| `FormulaSupportBoundsPartial_fromPipeline`         | `pnp3/Magnification/LocalityProvider_Partial.lean:312`               |
| `FormulaSupportBoundsFromMultiSwitchingContract`   | `pnp3/Magnification/AC0LocalityBridge.lean:42`                       |
| `MagnificationAssumptions`                         | `pnp3/Magnification/FinalResultMainline.lean:152`                    |
| `MagnificationAssumptions_fromPipeline`            | `pnp3/Magnification/FinalResultMainline.lean:161`                    |
| `fixedParams ∧ uniformProvenance` (Probe 8a shape) | `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:532` (premise of `false_of_fixedParams_and_uniformProvenance`) |

The first five are named definitions; the sixth is a conjunction shape
(no single named Prop in the codebase). For the sixth, the alias
bundles the two halves into a single `Prop` form using
`OverbroadUniformFormulaProvenance` from
`pnp3/Magnification/UnconditionalResearchGap.lean` as the
`uniformProvenance` half.
-/

namespace Pnp3
namespace RefutedPredicates

open Magnification (
  FormulaSupportRestrictionBoundsPartial
  FormulaSupportBoundsPartial_fromPipeline
  FormulaSupportBoundsPartial_fromPipeline_fixedParams
  MagnificationAssumptions
  MagnificationAssumptions_fromPipeline
  OverbroadUniformFormulaProvenance
)

/--
Audit alias for the original refuted predicate
`Magnification.FormulaSupportRestrictionBoundsPartial`.

`False` is provable from this alias via
`Pnp3.Tests.false_of_FormulaSupportRestrictionBoundsPartial`.
-/
abbrev RefutedPredicate_FormulaSupportRestrictionBoundsPartial : Prop :=
  FormulaSupportRestrictionBoundsPartial

/--
Audit alias for the original refuted contract
`Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract`.

`False` is provable via
`Pnp3.Tests.false_of_FormulaSupportBoundsFromMultiSwitchingContract`.
-/
abbrev RefutedPredicate_FormulaSupportBoundsFromMultiSwitchingContract : Prop :=
  Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract

/--
Audit alias for the original refuted package structure
`Magnification.MagnificationAssumptions`.

`False` is provable via `Pnp3.Tests.false_of_MagnificationAssumptions`.
-/
abbrev RefutedPredicate_MagnificationAssumptions : Type :=
  MagnificationAssumptions

/--
Audit alias for the pipeline-aware refuted predicate
`Magnification.FormulaSupportBoundsPartial_fromPipeline`.

`False` is provable via
`Pnp3.Tests.false_of_FormulaSupportBoundsPartial_fromPipeline`.
-/
abbrev RefutedPredicate_FormulaSupportBoundsPartial_fromPipeline : Prop :=
  FormulaSupportBoundsPartial_fromPipeline

/--
Audit alias for the pipeline-aware refuted package structure
`Magnification.MagnificationAssumptions_fromPipeline`.

`False` is provable via
`Pnp3.Tests.false_of_MagnificationAssumptions_fromPipeline`.
-/
abbrev RefutedPredicate_MagnificationAssumptions_fromPipeline : Type :=
  MagnificationAssumptions_fromPipeline

/--
Audit alias bundling the refuted "fixed-parameters with uniform
provenance" conjunction shape (Probe 8a in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`).

This conjunction is not a single named `Prop` in the codebase; the
alias bundles the two halves so that guard scripts can recognise it
under one canonical audit name.

`False` is provable from this alias via
`Pnp3.Tests.false_of_fixedParams_and_uniformProvenance`.
-/
abbrev RefutedPredicate_FixedParamsUniformProvenancePair
    (ac0 : ThirdPartyFacts.AC0Parameters) (sb : Nat → Nat) : Prop :=
  FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb ∧
  OverbroadUniformFormulaProvenance ac0

end RefutedPredicates
end Pnp3
