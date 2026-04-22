import Complexity.PpolyFormula_from_PpolyDAG_FixedSlice
import LowerBounds.FailedRoute_FixedSliceSupportHalfCore
import LowerBounds.SingletonDensityContradiction
import Magnification.LocalityProvider_Partial

/-!
# Formula Support Bounds Falsifiability — Regression Test

Formalizes the two-probe audit recorded in
`outputs/formula-support-bounds-falsifiability-audit.md` (commit
`d8a7753`) as an in-project Lean proof.  The audit showed that
`Magnification.FormulaSupportRestrictionBoundsPartial` is formally
INCONSISTENT with already-proven fixed-slice infrastructure — any
theorem depending on it is ex falso rather than genuine progress
toward an unconditional `NP ≠ P/poly`.

This file makes that inconsistency an in-project theorem so any future
edit that breaks the audit (or accidentally relies on the predicate in
a new context) trips a regression.

## Probe 1 (this file)

Combined with a fixed-slice `PpolyDAG` witness, `FormulaSupportRestrictionBoundsPartial`
yields `False` — via the existing DAG→Formula bridge plus the
existing support-bounds consumer
`false_of_abstractGapTargetedPayload_of_supportBounds`.

## Probe 2 (referenced, not yet re-proved here)

The audit ALSO shows that `FormulaSupportRestrictionBoundsPartial`
alone (without any external `PpolyDAG` hypothesis) yields `False` via
truth-table hardwiring: at a single input length, any Boolean function
is trivially in `PpolyFormula`.  Porting that probe into the project
requires a fixed-slice truth-table-DNF formula construction (~100 LOC)
and is deferred to a follow-up session.  See
`outputs/formula-support-bounds-falsifiability-audit.md` for the
informal proof.

## Consequences (applies to the "active final line" in
`Magnification/FinalResultMainline.lean`)

Every theorem whose statement includes `hBounds :
FormulaSupportRestrictionBoundsPartial` in its hypotheses is
"ex-falso-capable": combined with ANY fixed-slice `PpolyDAG` witness
(or, via Probe 2, with no side hypothesis at all), it proves `False`,
so any conclusion it derives about `NP` is vacuously true and does not
represent progress toward unconditionality.

The regression lemma below encodes this vacuity directly.
-/

namespace Pnp3
namespace Tests
namespace FormulaSupportBoundsFalsifiabilityProbe

open ComplexityInterfaces
open Models
open LowerBounds

/-- **Regression lemma (Probe 1 from the audit)**: assuming
`FormulaSupportRestrictionBoundsPartial`, the fixed-slice language
`gapPartialMCSP_Language p` is NOT in `PpolyDAG`.

The proof chains the existing fixed-slice DAG→Formula bridge
`Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`, the
existing abstract payload constructor
`abstractGapTargetedSingletonDensityPayload_of_dag`, and the existing
support-bounds consumer
`false_of_abstractGapTargetedPayload_of_supportBounds`.

**Interpretation**: since any LARGE-S fixed-slice hardwiring IS in
`PpolyDAG` (it's trivially a DAG at a single input length — see
the audit for details), this lemma witnesses the predicate's
inconsistency.  The lemma itself does not prove `False` unconditionally
(Probe 2 would — see module docstring), but any attempt to use
`hBounds` alongside a fixed-slice DAG witness produces `False`. -/
theorem fixedSlice_not_PpolyDAG_of_FormulaSupportRestrictionBoundsPartial
    {p : GapPartialMCSPParams}
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    ¬ ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) := by
  intro hDag
  classical
  have hFormula :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
    Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice p hDag
  have hPkg :
      Nonempty (AbstractGapTargetedSingletonDensityPayload p) :=
    abstractGapTargetedSingletonDensityPayload_of_dag hDag
  rcases hPkg with ⟨pkg⟩
  exact false_of_abstractGapTargetedPayload_of_supportBounds
    pkg hBounds hFormula

/-- **Stronger regression statement**: combining
`FormulaSupportRestrictionBoundsPartial` with a fixed-slice `PpolyDAG`
witness yields `False` directly.  Equivalent to the negation form
above (`A → ¬ B` iff `A ∧ B → False`), but the explicit `False`
version makes the inconsistency more visible in audit grep. -/
theorem false_of_FormulaSupportBounds_and_fixedSlice_PpolyDAG
    {p : GapPartialMCSPParams}
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial)
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    False :=
  fixedSlice_not_PpolyDAG_of_FormulaSupportRestrictionBoundsPartial
    hBounds hDag

end FormulaSupportBoundsFalsifiabilityProbe
end Tests
end Pnp3
