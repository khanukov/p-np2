import Magnification.UnconditionalResearchGap

/-!
# Target-lock probe — Research Governance v0.1, PR 11.

Compile-time structural assertions that pin the trust root's
`ResearchGapWitness` shape. If the structure ever drifts (extra
required field, type change, or removal of `dagSeparation`), the
elaborator rejects this file and `lake build` fails — independently
of the shell-level `scripts/check_target_lock.sh` guard.

The complementary phantom-axiom check (no top-level
`axiom P_ne_NP_unconditional` in pnp3/pnp4) lives in the shell
guard, since Lean's elaborator cannot easily test "no declaration
with this name exists in the program".
-/

namespace Pnp3
namespace Tests
namespace TargetLock

open Pnp3.Magnification

/-- Constructor-shape probe: `ResearchGapWitness` must be
inhabited by exactly one field named `dagSeparation` of type
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

Adding a second required field would leave this anonymous-constructor
syntax incomplete, breaking the build. -/
example (h : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
    ResearchGapWitness :=
  { dagSeparation := h }

/-- Field-projection probe: the projector must produce exactly the
expected `NP_not_subset_PpolyDAG` type. A type drift in the
`dagSeparation` field would trip this. -/
example (g : ResearchGapWitness) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  g.dagSeparation

/-- `ResearchGapTarget` alias must equal `NP_not_subset_PpolyDAG`.
A drift in the alias would break this constructor. -/
example (h : ResearchGapTarget) : ResearchGapWitness :=
  { dagSeparation := h }

end TargetLock
end Tests
end Pnp3
