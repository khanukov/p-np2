import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.WorkHeadCrossings

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Canonical crossing records from an actual run

This file records the information carried by actual crossings of the
canonical work-tape boundaries selected in `CanonicalBoundarySelection`.
For the transition numbered `time`, the convention is:

* the direction is the direction in which that transition crosses the cut;
* the control state is the **post-transition** state, at time `time + 1`;
* the input-head position is also the post-transition position.

The input head is stored in `Fin (T + 1)`: during a blank-start run, its
position after any of the first `T` transitions is at most `T`.  The list
below contains one record for every pair `(selected cut, crossing time)`, and
its length is exactly the sum of the actual crossing counts at those cuts.
The canonical charging theorem therefore bounds this length by `T / b`.

This is deterministic extraction from one concrete run only.  No local
validator, uniqueness of a guessed transcript, branching-program width, or
compression theorem is claimed here.
-/

/-- The two possible directions of a genuine work-boundary crossing. -/
inductive WorkCrossingDirection where
  | leftToRight
  | rightToLeft
deriving DecidableEq, Fintype, Repr

@[simp]
theorem card_workCrossingDirection :
    Fintype.card WorkCrossingDirection = 2 := by
  decide

/-- The finite machine information retained at one work-boundary crossing.

Both `postState` and `postInputHead` are sampled after the crossing
transition.  The direction is sampled from the work-head positions before
and after that same transition. -/
structure CrossingRecordPayload (State : Type) (T : Nat) where
  direction : WorkCrossingDirection
  postState : State
  postInputHead : Fin (T + 1)
deriving DecidableEq, Fintype

/-- One crossing payload together with the identity and physical position of
its selected cut.

`selectedCut : Fin (T / b)` is the full-bucket index used by
`canonicalWorkBoundary`.  `physicalCut : Fin T` stores the actual boundary
position selected inside that bucket, so the record does not rely on knowing
the run/input merely to recover that position. -/
structure CanonicalCrossingRecord (State : Type) (T b : Nat) where
  selectedCut : Fin (T / b)
  physicalCut : Fin T
  payload : CrossingRecordPayload State T
deriving Fintype

/-- One input-head step advances by at most one cell. -/
theorem inputHead_step_le_succ_for_crossingRecord
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    (step machine input config).inputHead ≤ config.inputHead + 1 := by
  rcases inputHead_step_cases machine input config with h | h <;> omega

/-- In a blank-start run, the input head after `time` transitions is at most
`time`. -/
theorem inputHead_run_le_time_for_crossingRecord
    (machine : DeterministicMachine) (input : List Bool) (time : Nat) :
    (run machine input time).inputHead ≤ time := by
  change
    (runFrom machine input (initialConfiguration machine) time).inputHead ≤ time
  have hGeneral : ∀ (config : Configuration machine.State) (steps : Nat),
      (runFrom machine input config steps).inputHead ≤
        config.inputHead + steps := by
    intro config steps
    induction steps generalizing config with
    | zero => simp
    | succ steps ih =>
        rw [runFrom_succ]
        calc
          (runFrom machine input (step machine input config) steps).inputHead ≤
              (step machine input config).inputHead + steps := ih _
          _ ≤ (config.inputHead + 1) + steps :=
            Nat.add_le_add_right
              (inputHead_step_le_succ_for_crossingRecord machine input config)
              steps
          _ = config.inputHead + Nat.succ steps := by omega
  simpa [initialConfiguration] using
    (hGeneral (initialConfiguration machine) time)

/-- Direction extracted from the exact two-position crossing witness. -/
def workCrossingDirectionOf {j fromHead toHead : Nat}
    (_hCross : CrossesWorkBoundary j fromHead toHead) :
    WorkCrossingDirection :=
  if fromHead = j then .leftToRight else .rightToLeft

/-- The canonical work boundary selected in bucket `i` for this concrete
blank-start run. -/
noncomputable def canonicalWorkBoundary
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (i : Fin (T / b)) : Fin T :=
  canonicalBoundary hb
    (fun j : Fin T => workBoundaryCrossingCount machine input T j.val) i

/-- The complete vector of physical canonical cuts, including cuts with zero
actual crossings.  Keeping this separate from the crossing-record list is
essential: a zero-crossing cut contributes no list entry but is still part of
the fixed cut description. -/
abbrev CanonicalCutDescription (T b : Nat) := Fin (T / b) → Fin T

/-- Extract every physical canonical boundary of this concrete run. -/
noncomputable def canonicalCutDescription
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : CanonicalCutDescription T b :=
  fun i => canonicalWorkBoundary machine input T b hb i

@[simp]
theorem canonicalCutDescription_apply
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (i : Fin (T / b)) :
    canonicalCutDescription machine input T b hb i =
      canonicalWorkBoundary machine input T b hb i :=
  rfl

/-- All actual pairs `(selected bucket, time)` at which the selected boundary
of that bucket is crossed.  The first coordinate identifies the cut and the
second identifies one of the first `T` transitions. -/
noncomputable def canonicalCrossingEvents
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : Finset (Fin (T / b) × Fin T) :=
  by
    classical
    exact Finset.univ.filter fun event =>
      WorkBoundaryCrossingAt machine input event.2.val
        (canonicalWorkBoundary machine input T b hb event.1).val

/-- Membership in `canonicalCrossingEvents` is exactly the concrete crossing
predicate, not a relaxed or guessed event relation. -/
theorem mem_canonicalCrossingEvents_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (event : Fin (T / b) × Fin T) :
    event ∈ canonicalCrossingEvents machine input T b hb ↔
      WorkBoundaryCrossingAt machine input event.2.val
        (canonicalWorkBoundary machine input T b hb event.1).val := by
  classical
  simp [canonicalCrossingEvents]

/-- A selected-cut crossing occurrence, carrying the exact membership proof
needed to extract its record. -/
abbrev CanonicalCrossingOccurrence
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :=
  { event // event ∈ canonicalCrossingEvents machine input T b hb }

/-- Extract the post-transition record attached to one actual occurrence. -/
noncomputable def canonicalCrossingRecordOfOccurrence
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : CanonicalCrossingOccurrence machine input T b hb) :
    CanonicalCrossingRecord machine.State T b := by
  let event := occurrence.val
  have hCross : WorkBoundaryCrossingAt machine input event.2.val
      (canonicalWorkBoundary machine input T b hb event.1).val :=
    (mem_canonicalCrossingEvents_iff machine input T b hb event).mp
      occurrence.property
  let postConfig := run machine input (event.2.val + 1)
  exact
    { selectedCut := event.1
      physicalCut := canonicalWorkBoundary machine input T b hb event.1
      payload :=
        { direction := workCrossingDirectionOf hCross
          postState := postConfig.state
          postInputHead :=
            ⟨postConfig.inputHead, by
              have hTime : event.2.val + 1 ≤ T := event.2.isLt
              exact Nat.lt_succ_of_le
                ((inputHead_run_le_time_for_crossingRecord machine input
                  (event.2.val + 1)).trans hTime)⟩ } }

/-- Extraction stores the exact physical canonical boundary selected for the
record's bucket. -/
@[simp]
theorem canonicalCrossingRecordOfOccurrence_physicalCut
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : CanonicalCrossingOccurrence machine input T b hb) :
    (canonicalCrossingRecordOfOccurrence machine input T b hb occurrence).physicalCut =
      canonicalWorkBoundary machine input T b hb occurrence.val.1 := by
  rfl

/-- The bucket identity stored by extraction is also exact. -/
@[simp]
theorem canonicalCrossingRecordOfOccurrence_selectedCut
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : CanonicalCrossingOccurrence machine input T b hb) :
    (canonicalCrossingRecordOfOccurrence machine input T b hb occurrence).selectedCut =
      occurrence.val.1 := by
  rfl

/-- A finite list of all extracted records.  Its enumeration order is not
used semantically; the occurrence subtype retains the exact cut/time link
before the records are mapped out. -/
noncomputable def canonicalCrossingRecords
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (CanonicalCrossingRecord machine.State T b) :=
  (canonicalCrossingEvents machine input T b hb).attach.toList.map
    (canonicalCrossingRecordOfOccurrence machine input T b hb)

/-- Counting selected-cut events is exactly summing the actual crossing
counts at the selected canonical work boundaries. -/
theorem card_canonicalCrossingEvents_eq_sum
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (canonicalCrossingEvents machine input T b hb).card =
      ∑ i : Fin (T / b),
        workBoundaryCrossingCount machine input T
          (canonicalWorkBoundary machine input T b hb i).val := by
  classical
  calc
    (canonicalCrossingEvents machine input T b hb).card =
        ∑ event : Fin (T / b) × Fin T,
          if WorkBoundaryCrossingAt machine input event.2.val
              (canonicalWorkBoundary machine input T b hb event.1).val
            then 1 else 0 := by
      rw [Finset.sum_boole]
      rfl
    _ = ∑ i : Fin (T / b), ∑ time : Fin T,
          if WorkBoundaryCrossingAt machine input time.val
              (canonicalWorkBoundary machine input T b hb i).val
            then 1 else 0 :=
      Fintype.sum_prod_type _
    _ = ∑ i : Fin (T / b),
        workBoundaryCrossingCount machine input T
          (canonicalWorkBoundary machine input T b hb i).val := by
      unfold workBoundaryCrossingCount workBoundaryCrossingCountFrom
        WorkBoundaryCrossingAt
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro time _
      by_cases hCross : WorkBoundaryCrossingAtFrom machine input
          (initialConfiguration machine) time.val
          (canonicalWorkBoundary machine input T b hb i).val <;>
        simp [hCross]

/-- The extracted record-list length is the exact selected crossing-count
sum.  Mapping to records loses neither events nor multiplicity. -/
theorem length_canonicalCrossingRecords_eq_sum
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (canonicalCrossingRecords machine input T b hb).length =
      ∑ i : Fin (T / b),
        workBoundaryCrossingCount machine input T
          (canonicalWorkBoundary machine input T b hb i).val := by
  rw [canonicalCrossingRecords, List.length_map, Finset.length_toList,
    Finset.card_attach, card_canonicalCrossingEvents_eq_sum]

/-- Canonical charging bounds the total number of retained crossing records
by the exact floor quotient `T / b`. -/
theorem length_canonicalCrossingRecords_le_div
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (canonicalCrossingRecords machine input T b hb).length ≤ T / b := by
  rw [length_canonicalCrossingRecords_eq_sum]
  simpa [canonicalWorkBoundary] using
    (sum_canonicalWorkBoundaryCrossings_le_div machine input T b hb)

/-- Exact size of the ambient one-record carrier.  This counts all triples,
not only records reachable in a particular run. -/
def crossingRecordPayloadEquiv (State : Type) (T : Nat) :
    CrossingRecordPayload State T ≃
      WorkCrossingDirection × State × Fin (T + 1) where
  toFun record := (record.direction, record.postState, record.postInputHead)
  invFun fields :=
    { direction := fields.1
      postState := fields.2.1
      postInputHead := fields.2.2 }
  left_inv record := by cases record; rfl
  right_inv fields := by rcases fields with ⟨direction, state, head⟩; rfl

theorem card_crossingRecordPayload
    (State : Type) [Fintype State] (T : Nat) :
    Fintype.card (CrossingRecordPayload State T) =
      2 * Fintype.card State * (T + 1) := by
  rw [Fintype.card_congr (crossingRecordPayloadEquiv State T)]
  simp [Nat.mul_assoc]

/-- The full record is its selected-bucket coordinate, physical cut, and
machine crossing payload. -/
def canonicalCrossingRecordEquiv (State : Type) (T b : Nat) :
    CanonicalCrossingRecord State T b ≃
      Fin (T / b) × Fin T × CrossingRecordPayload State T where
  toFun record := (record.selectedCut, record.physicalCut, record.payload)
  invFun fields :=
    { selectedCut := fields.1
      physicalCut := fields.2.1
      payload := fields.2.2 }
  left_inv record := by cases record; rfl
  right_inv fields := by
    rcases fields with ⟨cut, physicalCut, payload⟩
    rfl

/-- The full record carrier additionally pays for both the selected-bucket
identity and physical boundary position.  This is an ambient count; it is not
a count of reachable records. -/
theorem card_canonicalCrossingRecord
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (CanonicalCrossingRecord State T b) =
      (T / b) * T * (2 * Fintype.card State * (T + 1)) := by
  rw [Fintype.card_congr (canonicalCrossingRecordEquiv State T b)]
  simp only [Fintype.card_prod, Fintype.card_fin,
    card_crossingRecordPayload]
  simp [Nat.mul_assoc]

/-- Fixed-length words over the payload alphabet.  This ambient carrier is
useful only as a transparent counting reference; the concrete extracted list
may be shorter and carries explicit selected-cut identities separately. -/
abbrev AmbientCrossingPayloadVector (State : Type) (T b : Nat) :=
  Fin (T / b) → CrossingRecordPayload State T

/-- Exact ambient payload-vector count
`(2 * |State| * (T + 1))^(T / b)`.  No claim is made that every such vector is
reachable, locally valid, or a complete machine transcript. -/
theorem card_ambientCrossingPayloadVector
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (AmbientCrossingPayloadVector State T b) =
      (2 * Fintype.card State * (T + 1)) ^ (T / b) := by
  rw [Fintype.card_fun, Fintype.card_fin, card_crossingRecordPayload]

/-- Exact number of complete physical cut descriptions.  This pays for every
selected `b_i`, including zero-crossing cuts. -/
theorem card_canonicalCutDescription (T b : Nat) :
    Fintype.card (CanonicalCutDescription T b) = T ^ (T / b) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- A transparent full ambient `α` carrier: all physical cuts together with
one fixed-length word over the crossing-payload alphabet.

This is only an ambient product carrier.  It is not asserted to coincide with
the variable-length extracted record list, nor to satisfy local consistency. -/
structure AmbientCanonicalAlpha (State : Type) (T b : Nat) where
  cuts : CanonicalCutDescription T b
  payloads : AmbientCrossingPayloadVector State T b
deriving Fintype

/-- The full ambient carrier counts both the physical cut vector and the
payload-only word.  In particular it is larger than the payload-only count by
the exact factor `T^(T / b)`. -/
theorem card_ambientCanonicalAlpha
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (AmbientCanonicalAlpha State T b) =
      T ^ (T / b) *
        (2 * Fintype.card State * (T + 1)) ^ (T / b) := by
  let equiv : AmbientCanonicalAlpha State T b ≃
      CanonicalCutDescription T b ×
        AmbientCrossingPayloadVector State T b :=
    { toFun := fun alpha => (alpha.cuts, alpha.payloads)
      invFun := fun fields => { cuts := fields.1, payloads := fields.2 }
      left_inv := fun alpha => by cases alpha; rfl
      right_inv := fun fields => by rcases fields with ⟨cuts, payloads⟩; rfl }
  rw [Fintype.card_congr equiv, Fintype.card_prod,
    card_canonicalCutDescription, card_ambientCrossingPayloadVector]

end OneTapeMagnification
end Frontier
end Pnp4
