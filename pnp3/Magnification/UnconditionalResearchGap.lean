import Magnification.FinalResultCore

namespace Pnp3
namespace Magnification

open Models

/-!
# Single-file research gap for unconditional `P != NP`

This module is the intended one-file frontier for the remaining gap.

Current status:

* The repository has internalized `P_subset_PpolyDAG`.
* The route from `NP_not_subset_PpolyDAG` to `P != NP` is already compiled as
  `P_ne_NP_final_dag_only`.
* The old support-bounds route is not merely unfinished: the audit proves that
  its core predicates are ex-falso.

Therefore the remaining mathematical task is not another wrapper.  It is a
non-vacuous source theorem for `NP_not_subset_PpolyDAG`, or an equivalent
formula/locality theorem that delivers that DAG separation without routing
through the refuted support-bounds predicates.

How to use this file for a future breakthrough:

1. Prove `ResearchGapWitness` in this file, by replacing the placeholder
   *commented template* below with a real proof.
2. Then expose the zero-argument theorem in this file:

```
theorem P_ne_NP_unconditional : ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_final researchGapWitness
```

No API change elsewhere should be necessary.  This file is imported by
`Magnification.FinalResult`, and the theorem below already connects the
research witness to the final `P != NP` target.

What must NOT count as solving the gap:

* providing `FormulaSupportRestrictionBoundsPartial`;
* providing `FormulaSupportBoundsFromMultiSwitchingContract`;
* providing `FormulaSupportBoundsPartial_fromPipeline`;
* pairing `FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb` with
  overbroad uniform provenance for every formula witness under the same `ac0`.

Those routes are refuted by the falsifiability audit.  A successful proof must
avoid truth-table hardwiring and singleton/per-formula AC0 provenance.
-/

/-- Uniform provenance shape that is now known to be too broad when paired
with fixed-params support bounds.

This abbreviation is kept here only to name the leak.  A future solution should
not try to prove this for all `PpolyFormula` witnesses: together with
`FormulaSupportBoundsPartial_fromPipeline_fixedParams`, it reconstructs the old
false support-bounds predicate. -/
abbrev OverbroadUniformFormulaProvenance
    (ac0 : ThirdPartyFacts.AC0Parameters) : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    ∃ (F : Core.Family ac0.n) (hsame : ac0.n = Models.partialInputLen p),
      ThirdPartyFacts.AC0FamilyWitnessProp ac0 F ∧
      Nonempty (ThirdPartyFacts.AC0MultiSwitchingWitness ac0 F) ∧
      (∃ f : Core.BitVec ac0.n → Bool, f ∈ F ∧
        ∀ x : Core.BitVec ac0.n,
          f x = ComplexityInterfaces.FormulaCircuit.eval
            ((Classical.choose hFormula).family (Models.partialInputLen p))
            (ThirdPartyFacts.castBitVec hsame x))

/-- The known-bad fixed-params pair.

This packages the exact combination that the audit identifies as leaking back
to the old false predicate.  It is intentionally not used by the final theorem
below. -/
structure RefutedFixedParamsUniformRoute : Type where
  ac0 : ThirdPartyFacts.AC0Parameters
  supportBudget : Nat → Nat
  bounds :
    FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 supportBudget
  uniformProvenance : OverbroadUniformFormulaProvenance ac0

/-- The one remaining theorem product needed by the already-compiled final
route.

This is deliberately stated at the DAG-separation boundary.  Any lower-level
approach is acceptable only if it proves this without using the refuted
support-bounds surfaces listed in this module's header. -/
def ResearchGapTarget : Prop :=
  ComplexityInterfaces.NP_not_subset_PpolyDAG

/-- Future research witness.

To close the project unconditionally, prove an inhabitant of this structure in
this file.  The only mathematical field is `dagSeparation`; the rest of this
module records the audit constraints that such a proof must respect. -/
structure ResearchGapWitness : Type where
  dagSeparation : ResearchGapTarget

/-- Conditional final theorem from the isolated research witness.

This is the compiled bridge from the single remaining gap to the final target.
It does not use the refuted support-bounds route; it uses only the existing
DAG-track final wrapper with internalized `P_subset_PpolyDAG`. -/
theorem P_ne_NP_of_researchGap
    (gap : ResearchGapWitness) :
    ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_final_dag_only gap.dagSeparation

/-- Public final DAG-separation endpoint.

The name is intentionally reserved for the honest research-gap boundary.  Legacy
support-bounds / multiswitching routes live under explicit audit-route names in
`FinalResultMainline`.
-/
theorem NP_not_subset_PpolyDAG_final
    (gap : ResearchGapWitness) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  gap.dagSeparation

/-- Public final `P != NP` endpoint.

The only mathematical input is `ResearchGapWitness`, i.e. a direct proof of
`NP_not_subset_PpolyDAG` that avoids the refuted support-bounds surfaces.
-/
theorem P_ne_NP_final
    (gap : ResearchGapWitness) :
    ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_researchGap gap

/-!
Future completion template, intentionally commented out.

Once the real mathematics is available, prove the witness below in this file
and then expose the zero-argument theorem.  Avoid adding any project-local
trusted assumptions or proof holes.

```
noncomputable def researchGapWitness : ResearchGapWitness := by
  -- Real proof of `ComplexityInterfaces.NP_not_subset_PpolyDAG` goes here.

theorem P_ne_NP_unconditional : ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_final researchGapWitness
```
-/

end Magnification
end Pnp3
