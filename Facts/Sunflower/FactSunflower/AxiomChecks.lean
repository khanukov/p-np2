import FactSunflower
import Lean.Util.CollectAxioms
import Mathlib.Tactic

/-!
Checks for the sunflower fact package.

We provide a custom command `check_axioms` which verifies that a
constant depends only on the explicitly permitted axioms.  For the
classical sunflower lemma this should be exactly `Classical.choice`.
-/

open Facts
open Sunflower
open Lean Meta Elab Command

/-- List of axioms that are allowed to appear in the sunflower development. -/
def allowedAxioms : List Name := [``Classical.choice]

/-- Command `check_axioms id` fails if `id` depends on axioms outside
`allowedAxioms`. -/
elab "check_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let unexpected := axioms.filter fun ax => !allowedAxioms.contains ax
  unless unexpected.isEmpty do
    throwError
      "{n} depends on unexpected axioms: {unexpected.map (·.toString)}"

--! NOTE:
--  The fact package deliberately re-exports a small API under the
--  `Facts.Sunflower` namespace (see `FactSunflower.lean`).  We list
--  *every* exported declaration here so that future refactors cannot
--  accidentally introduce a dependency on stronger axioms without
--  getting caught by the regression suite.

check_axioms Sunflower.threshold
check_axioms Sunflower.HasSunflower
check_axioms Sunflower.sunflower_exists_classic
check_axioms Sunflower.sunflower_exists_of_fixedSize
check_axioms Sunflower.removeSupersets

check_axioms Sunflower.SunflowerFam
check_axioms Sunflower.exists_of_large_family_classic
check_axioms Sunflower.cover_step_if_large
check_axioms Sunflower.card_removeCovered_le_sub_t
check_axioms Sunflower.card_removeCovered_le_sub_t'
check_axioms Sunflower.uniform_of_removeCovered
check_axioms Sunflower.card_removeCovered_lt
check_axioms Sunflower.exists_cover_step_strict
check_axioms Sunflower.exists_cover_until_threshold
check_axioms Sunflower.removeCovered
