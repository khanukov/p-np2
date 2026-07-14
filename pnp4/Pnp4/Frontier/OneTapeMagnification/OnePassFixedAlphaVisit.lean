import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaBlockVisitReplay
import Pnp4.Frontier.OneTapeMagnification.OnePassBoundaryCounterVector

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One-pass replay of one advertised fixed-alpha visit

`fixedAlphaBlockVisitCheck` is already an exact executable specification, but
its surface mentions `runFrom` separately for the slab-membership quantifier
and for every endpoint field.  Crossing-counter validation is likewise
available as a separate traversal.  This file fuses those semantic traversals
for one advertised visit.

The recursive runner below returns three values after one pass through the
advertised number of transitions:

* a Boolean saying that every pre-transition work head was in the slab;
* the final configuration; and
* a finite vector of bounded crossing counters.

Starting from the zero vector and using horizon `H`, the counter component is
exact whenever the visit has at most `H` transitions.  The fixed-alpha wrapper
uses `H = T`, which is sufficient for every visit with endpoints in
`Fin (T + 1)`.  Its checker is propositionally and Boolean-equal to the old
one-visit checker.

The returned `Configuration` still contains a full `WorkTape`.  Thus this is a
semantic fusion precursor, not yet a finite-width branching-program state.
-/

/-- The three outputs of a fused traversal through one advertised visit. -/
structure OnePassFixedAlphaVisitResult (State : Type) (H m : Nat) where
  allPreHeadsInside : Bool
  finalConfig : Configuration State
  counters : BoundedCrossingCounterVector H m

/-- Traverse one deterministic segment exactly once.  At each transition the
current (pre-transition) work head contributes to the slab-membership Boolean,
and the pair of current and successor heads updates all crossing coordinates.
-/
def onePassFixedAlphaVisitFrom
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (base width : Nat) (boundaries : Fin m → Nat) :
    Configuration machine.State → Nat → BoundedCrossingCounterVector H m →
      OnePassFixedAlphaVisitResult machine.State H m
  | config, 0, counters =>
      { allPreHeadsInside := true
        finalConfig := config
        counters := counters }
  | config, steps + 1, counters =>
      let next := step machine input config
      let tail := onePassFixedAlphaVisitFrom machine input base width boundaries
        next steps
        (bumpBoundedCrossingCounterVector boundaries
          config.workHead next.workHead counters)
      { allPreHeadsInside :=
          decide (WorkCellInSlab base width config.workHead) &&
            tail.allPreHeadsInside
        finalConfig := tail.finalConfig
        counters := tail.counters }

/-- The final configuration returned by the fused traversal is exactly the
ordinary deterministic replay. -/
theorem onePassFixedAlphaVisitFrom_finalConfig
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (base width : Nat) (boundaries : Fin m → Nat)
    (config : Configuration machine.State) (steps : Nat)
    (initial : BoundedCrossingCounterVector H m) :
    (onePassFixedAlphaVisitFrom machine input base width boundaries
      config steps initial).finalConfig =
      runFrom machine input config steps := by
  induction steps generalizing config initial with
  | zero => rfl
  | succ steps ih =>
      simp only [onePassFixedAlphaVisitFrom, runFrom_succ]
      exact ih (step machine input config)
        (bumpBoundedCrossingCounterVector boundaries config.workHead
          (step machine input config).workHead initial)

/-- The counter projection of the fused traversal is definitionally the same
single-pass bounded vector traversal as the standalone counter layer. -/
theorem onePassFixedAlphaVisitFrom_counters
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (base width : Nat) (boundaries : Fin m → Nat)
    (config : Configuration machine.State) (steps : Nat)
    (initial : BoundedCrossingCounterVector H m) :
    (onePassFixedAlphaVisitFrom machine input base width boundaries
      config steps initial).counters =
      onePassBoundedCrossingCounterVectorFrom machine input boundaries
        config steps initial := by
  induction steps generalizing config initial with
  | zero => rfl
  | succ steps ih =>
      simp only [onePassFixedAlphaVisitFrom,
        onePassBoundedCrossingCounterVectorFrom]
      exact ih (step machine input config)
        (bumpBoundedCrossingCounterVector boundaries config.workHead
          (step machine input config).workHead initial)

/-- With a zero initial vector and enough horizon, every fused counter
coordinate is the exact finite-sum boundary-crossing count. -/
theorem onePassFixedAlphaVisitFrom_zero_counter_val_eq
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (base width : Nat) (boundaries : Fin m → Nat)
    (config : Configuration machine.State) (steps : Nat)
    (hsteps : steps ≤ H) (i : Fin m) :
    ((onePassFixedAlphaVisitFrom machine input base width boundaries
        config steps (zeroBoundedCrossingCounterVector H m)).counters i).val =
      workBoundaryCrossingCountFrom machine input config steps
        (boundaries i) := by
  rw [onePassFixedAlphaVisitFrom_counters]
  exact onePassBoundedCrossingCounterVectorFrom_zero_apply_val_eq
    machine input boundaries config steps hsteps i

/-- Splitting the pre-transition slab condition into the first head and the
remaining segment. -/
private theorem all_pre_heads_inside_succ_iff
    (machine : DeterministicMachine) (input : List Bool)
    (base width : Nat) (config : Configuration machine.State) (steps : Nat) :
    (∀ time : Fin (steps + 1),
        WorkCellInSlab base width
          (runFrom machine input config time.val).workHead) ↔
      WorkCellInSlab base width config.workHead ∧
        ∀ time : Fin steps,
          WorkCellInSlab base width
            (runFrom machine input (step machine input config)
              time.val).workHead := by
  constructor
  · intro hall
    constructor
    · simpa using hall ⟨0, by omega⟩
    · intro time
      simpa only [Fin.succ, Nat.succ_eq_add_one, runFrom_succ] using
        hall time.succ
  · rintro ⟨hfirst, htail⟩ time
    refine Fin.cases ?_ (fun remaining => ?_) time
    · simpa using hfirst
    · simpa only [Fin.succ, Nat.succ_eq_add_one, runFrom_succ] using
        htail remaining

/-- The Boolean accumulated by the fused traversal is exact: it holds iff
every head before one of the advertised transitions lies in the slab.  The
final head is deliberately not constrained. -/
theorem onePassFixedAlphaVisitFrom_allPreHeadsInside_eq_true_iff
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (base width : Nat) (boundaries : Fin m → Nat)
    (config : Configuration machine.State) (steps : Nat)
    (initial : BoundedCrossingCounterVector H m) :
    (onePassFixedAlphaVisitFrom machine input base width boundaries
      config steps initial).allPreHeadsInside = true ↔
      ∀ time : Fin steps,
        WorkCellInSlab base width
          (runFrom machine input config time.val).workHead := by
  induction steps generalizing config initial with
  | zero => simp [onePassFixedAlphaVisitFrom]
  | succ steps ih =>
      rw [all_pre_heads_inside_succ_iff]
      simp only [onePassFixedAlphaVisitFrom, Bool.and_eq_true,
        decide_eq_true_eq]
      rw [ih]

/-- Every advertised visit fits in its ambient time horizon. -/
theorem FixedAlphaBlockVisit.steps_le_horizon
    {State : Type} {T : Nat} (visit : FixedAlphaBlockVisit State T) :
    visit.steps ≤ T := by
  have hexit := visit.exitTime.isLt
  unfold FixedAlphaBlockVisit.steps
  omega

/-- Fixed-alpha specialization of the fused traversal.  It starts from the
materialized carried slab, uses the advertised block as the membership region,
and allocates counters at the ambient horizon `T`. -/
def onePassFixedAlphaBlockVisit
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) :
    OnePassFixedAlphaVisitResult machine.State T m :=
  onePassFixedAlphaVisitFrom machine input
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block) boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps (zeroBoundedCrossingCounterVector T m)

/-- The fixed-alpha fused result reaches the old replay's exact final
configuration. -/
theorem onePassFixedAlphaBlockVisit_finalConfig
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) :
    (onePassFixedAlphaBlockVisit machine input alpha block visit carried
      boundaries).finalConfig =
      fixedAlphaBlockVisitRun machine input alpha block visit carried := by
  exact onePassFixedAlphaVisitFrom_finalConfig machine input
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block) boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps (zeroBoundedCrossingCounterVector T m)

/-- The fixed-alpha fused membership Boolean is exactly the quantified
pre-transition membership clause of `FixedAlphaBlockVisitValid`. -/
theorem onePassFixedAlphaBlockVisit_allPreHeadsInside_eq_true_iff
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) :
    (onePassFixedAlphaBlockVisit machine input alpha block visit carried
      boundaries).allPreHeadsInside = true ↔
      ∀ time : Fin visit.steps,
        WorkCellInSlab
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockWidth alpha.offsets block)
          (runFrom machine input
            (fixedAlphaBlockVisitEntryConfiguration
              alpha block visit carried) time.val).workHead := by
  exact onePassFixedAlphaVisitFrom_allPreHeadsInside_eq_true_iff
    machine input (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block) boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps (zeroBoundedCrossingCounterVector T m)

/-- Every fixed-alpha fused counter is the exact crossing count of this
materialized visit. -/
theorem onePassFixedAlphaBlockVisit_counter_val_eq
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) (i : Fin m) :
    ((onePassFixedAlphaBlockVisit machine input alpha block visit carried
      boundaries).counters i).val =
      workBoundaryCrossingCountFrom machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps (boundaries i) := by
  exact onePassFixedAlphaVisitFrom_zero_counter_val_eq machine input
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block) boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps visit.steps_le_horizon i

/-- Restricting the fused final tape to the advertised slab gives exactly the
old carried output slab. -/
theorem onePassFixedAlphaBlockVisit_outputSlab_eq
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) :
    restrictWorkSlab
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockWidth alpha.offsets block)
        (onePassFixedAlphaBlockVisit machine input alpha block visit carried
          boundaries).finalConfig.workTape =
      fixedAlphaBlockVisitOutputSlab
        machine input alpha block visit carried := by
  rw [onePassFixedAlphaBlockVisit_finalConfig]
  rfl

/-- Boolean one-visit check whose membership and endpoint clauses are all read
from the result of the single fused traversal.  The counter vector is returned
for later cut checks but does not alter local visit validity. -/
def onePassFixedAlphaBlockVisitCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) : Bool :=
  let result := onePassFixedAlphaBlockVisit
    machine input alpha block visit carried boundaries
  result.allPreHeadsInside &&
    (decide (visit.exit.state = result.finalConfig.state) &&
      (decide (visit.exit.inputHead.val = result.finalConfig.inputHead) &&
        decide (visit.exit.workHead.val = result.finalConfig.workHead)))

/-- The one-pass checker accepts exactly the old semantic validity relation. -/
theorem onePassFixedAlphaBlockVisitCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) :
    onePassFixedAlphaBlockVisitCheck machine input alpha block visit carried
        boundaries = true ↔
      FixedAlphaBlockVisitValid machine input alpha block visit carried := by
  simp only [onePassFixedAlphaBlockVisitCheck, Bool.and_eq_true,
    decide_eq_true_eq]
  rw [onePassFixedAlphaBlockVisit_allPreHeadsInside_eq_true_iff,
    onePassFixedAlphaBlockVisit_finalConfig]
  rfl

/-- Fusing the traversal changes no Boolean behavior: the new one-pass checker
is extensionally equal to `fixedAlphaBlockVisitCheck`. -/
theorem onePassFixedAlphaBlockVisitCheck_eq_fixedAlphaBlockVisitCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat) :
    onePassFixedAlphaBlockVisitCheck machine input alpha block visit carried
        boundaries =
      fixedAlphaBlockVisitCheck machine input alpha block visit carried := by
  rw [Bool.eq_iff_iff,
    onePassFixedAlphaBlockVisitCheck_eq_true_iff,
    fixedAlphaBlockVisitCheck_eq_true_iff]

end OneTapeMagnification
end Frontier
end Pnp4
