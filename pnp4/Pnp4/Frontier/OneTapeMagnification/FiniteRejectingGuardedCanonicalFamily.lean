import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.RejectingGuardedCanonicalAggregateEndpoint
import Pnp4.Frontier.OneTapeMagnification.MandatoryFixedOrderQueryCollapse

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A finite alpha-indexed family of exact guarded components

The rejecting-guarded endpoint was previously stated as an existential over
both an ambient timed alpha and an arbitrary `List` of scheduled visits.  The
schedule is in fact the output of a deterministic builder.  This file removes
the apparently infinite `List` index: the family below is indexed by a finite
subtype of ambient alphas and installs the uniquely built schedule in each
component.

This is an exact finite family of deterministic layered query programs.  It is
not, by itself, a literal single uFBDD: selecting one member still requires a
nondeterministic selector (or a sharing theorem), and the present program API
records read-once behavior on consistent Boolean inputs rather than on every
formal graph path.
-/

/-! ## Generic finite dependent families -/

/-- A finite collection of layered programs whose layer counts may depend on
the component index. -/
structure FiniteLayeredQueryProgramFamily (n : Nat) where
  Index : Type
  indexFintype : Fintype Index
  layers : Index -> Nat
  program : (index : Index) -> LayeredQueryProgram n (layers index)

namespace FiniteLayeredQueryProgramFamily

/-- Boolean union of every component in a finite family. -/
def eval {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) : Bool := by
  letI : Fintype family.Index := family.indexFintype
  exact Finset.univ.fold (fun left right => left || right) false
    (fun index => (family.program index).eval input)

/-- Every component is read-once in the current layered-program semantics. -/
def IsReadOnce {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Prop :=
  forall index, (family.program index).IsReadOnce

/-- At most one component accepts each Boolean input. -/
def IsUnambiguous {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Prop :=
  forall input left right,
    (family.program left).eval input = true ->
    (family.program right).eval input = true ->
    left = right

/-- Number of homogeneous state slots in the disjoint layered presentation.
There is one copy of the component state carrier at every boundary layer. -/
def layeredStateSlotCount {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Nat := by
  letI : Fintype family.Index := family.indexFintype
  exact Finset.univ.sum fun index =>
    (family.layers index + 1) * (family.program index).width

private theorem finset_fold_or_eq_true_iff
    {alpha : Type*} (items : Finset alpha) (predicate : alpha -> Bool) :
    items.fold (fun left right => left || right) false predicate = true <->
      exists item, item ∈ items /\ predicate item = true := by
  have h := Finset.fold_op_rel_iff_or
    (s := items) (op := fun left right : Bool => left || right)
    (b := false) (f := predicate)
    (r := fun _ value : Bool => value = true) (c := false) (by
      intro x y z
      simp)
  simpa using h

/-- The finite Boolean union accepts exactly when one component accepts. -/
theorem eval_eq_true_iff {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) :
    family.eval input = true <->
      exists index, (family.program index).eval input = true := by
  letI : Fintype family.Index := family.indexFintype
  unfold eval
  rw [finset_fold_or_eq_true_iff]
  simp

/-- Honest card-times-maximum upper bound for a disjoint layered family.  The
hypothesis must bound the full layer-by-width slot contribution of every
component, not merely its live-state width. -/
theorem layeredStateSlotCount_le_card_mul {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (maximum : Nat)
    (hbound : forall index,
      (family.layers index + 1) * (family.program index).width <= maximum) :
    family.layeredStateSlotCount <=
      @Fintype.card family.Index family.indexFintype * maximum := by
  letI : Fintype family.Index := family.indexFintype
  unfold layeredStateSlotCount
  calc
    (∑ index : family.Index,
        (family.layers index + 1) * (family.program index).width) <=
        ∑ _index : family.Index, maximum := by
          apply Finset.sum_le_sum
          intro index _hindex
          exact hbound index
    _ = @Fintype.card family.Index family.indexFintype * maximum := by
      simp

end FiniteLayeredQueryProgramFamily

local instance cachedInputMachineStateDecidableEqForFiniteCanonicalFamily
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-! ## Eliminate the schedule index -/

/-- The total list installed in the alpha component.  A builder failure uses
the empty list; such an alpha is excluded by the eligibility predicate below. -/
def builtTimedAlphaVisitSchedule
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    List (TimedAlphaScheduledVisit machine.State T b) :=
  (buildTimedAlphaVisitSchedule machine alpha).getD []

/-- Any semantically valid advertised schedule is exactly the schedule
installed by the deterministic builder. -/
theorem builtTimedAlphaVisitSchedule_eq_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hvalid : TimedAlphaVisitScheduleValid machine alpha scheduled) :
    builtTimedAlphaVisitSchedule machine alpha = scheduled := by
  rcases hvalid with
    ⟨_syntactic, finalCursor, visitsSoFar, hfold, hfinish, _chained⟩
  have hbuild : buildTimedAlphaVisitSchedule machine alpha = some scheduled :=
    (buildTimedAlphaVisitSchedule_eq_some_iff
      machine alpha scheduled).2
        ⟨finalCursor, visitsSoFar, hfold, hfinish⟩
  simp [builtTimedAlphaVisitSchedule, hbuild]

/-- Static membership conditions for a useful component: the builder output
is a valid schedule, its input endpoints are monotone, and the advertised
terminal state is accepting.  All three conditions are independent of the
eventual Boolean input. -/
def BuiltRejectingGuardedCanonicalAlphaEligible
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b) : Prop :=
  timedAlphaVisitScheduleCheck (cachedInputMachine machine) alpha
      (builtTimedAlphaVisitSchedule (cachedInputMachine machine) alpha) = true /\
    timedAlphaScheduledVisitsInputMonotoneCheck
      (builtTimedAlphaVisitSchedule (cachedInputMachine machine) alpha) = true /\
    (cachedInputMachine machine).halt alpha.terminal.state = some .accept

/-- Finite alpha-only index type for the exact component family. -/
abbrev BuiltRejectingGuardedCanonicalAlphaIndex
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :=
  { alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b //
    BuiltRejectingGuardedCanonicalAlphaEligible machine alpha }

/-- The machine carries the finite cached-state universe as data, so the
eligible alpha subtype has a finite enumeration without any list bound. -/
instance builtRejectingGuardedCanonicalAlphaIndexFintype
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :
    Fintype (BuiltRejectingGuardedCanonicalAlphaIndex machine T b) := by
  letI : Fintype (cachedInputMachine machine).State :=
    (cachedInputMachine machine).stateFintype
  letI : DecidablePred
      (BuiltRejectingGuardedCanonicalAlphaEligible machine (T := T) (b := b)) :=
    fun alpha => by
      unfold BuiltRejectingGuardedCanonicalAlphaEligible
      infer_instance
  exact inferInstance

/-- The finite family of strict guarded components with their schedules
computed, rather than existentially supplied. -/
def finiteRejectingGuardedCanonicalFamily
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) : FiniteLayeredQueryProgramFamily n := by
  let cached := cachedInputMachine machine
  letI : Fintype cached.State := cached.stateFintype
  letI : DecidableEq cached.State := cachedInputStateDecidableEq machine
  let indexType := BuiltRejectingGuardedCanonicalAlphaIndex machine T b
  exact
    { Index := indexType
      indexFintype := inferInstance
      layers := fun index =>
        finiteCachedAllBlocksFuel (fun block =>
          timedAlphaBlockVisits block
            (builtTimedAlphaVisitSchedule cached index.1))
      program := fun index =>
        compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
          (n := n) machine index.1
            (builtTimedAlphaVisitSchedule cached index.1) }

/-- The monotonicity proof hardwired by membership in the finite index. -/
def builtRejectingGuardedCanonicalIndexMonotone
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    TimedAlphaScheduledVisitsInputMonotone
      (builtTimedAlphaVisitSchedule
        (cachedInputMachine machine) index.1) :=
  (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
    (builtTimedAlphaVisitSchedule
      (cachedInputMachine machine) index.1)).1 index.2.2.1

/-- Exact width of each useful installed component.  The formula exposes the
base homogeneous compiler width, the finite master cursor, and the one
absorbing reject state; the checked total wrapper adds no hidden states on an
eligible index. -/
theorem finiteRejectingGuardedCanonicalFamily_component_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    ((finiteRejectingGuardedCanonicalFamily
      machine n T b).program index).width =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)).width *
        ((finiteCachedTimedAlphaScheduleMasterQueryOrder
          (n := n)
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)
          (builtRejectingGuardedCanonicalIndexMonotone
            machine index)).length + 1) + 1 := by
  change
    (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1)).width = _
  unfold
    compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
  rw [dif_pos index.2.1, dif_pos index.2.2.1]
  exact
    compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_width
      machine index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1)
        (builtRejectingGuardedCanonicalIndexMonotone machine index)

/-- Explicit state-slot contribution of one component in the naive disjoint
layered presentation.  This is the quantitative cost that a selector/sharing
argument would have to reduce; it cannot be replaced by the maximum component
width. -/
def builtRejectingGuardedCanonicalComponentSlotCount
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) : Nat :=
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let layers := finiteCachedAllBlocksFuel
    (fun block => timedAlphaBlockVisits block scheduled)
  let baseWidth :=
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine index.1 scheduled).width
  let masterLength :=
    (finiteCachedTimedAlphaScheduleMasterQueryOrder
      (n := n) scheduled
        (builtRejectingGuardedCanonicalIndexMonotone machine index)).length
  (layers + 1) * (baseWidth * (masterLength + 1) + 1)

/-- Exact sum, not a maximum-width surrogate, for the finite disjoint union
of all useful built-alpha components. -/
theorem finiteRejectingGuardedCanonicalFamily_layeredStateSlotCount_eq_sum
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    (finiteRejectingGuardedCanonicalFamily
      machine n T b).layeredStateSlotCount =
      ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        builtRejectingGuardedCanonicalComponentSlotCount machine n index := by
  unfold FiniteLayeredQueryProgramFamily.layeredStateSlotCount
  apply Finset.sum_congr rfl
  intro index _hindex
  rw [finiteRejectingGuardedCanonicalFamily_component_width]
  rfl

/-- The alpha-only family is finite with no residual `List` enumeration. -/
theorem card_builtRejectingGuardedCanonicalAlphaIndex_le_ambient
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :
    letI : Fintype (cachedInputMachine machine).State :=
      (cachedInputMachine machine).stateFintype
    Fintype.card (BuiltRejectingGuardedCanonicalAlphaIndex machine T b) <=
      Fintype.card (AmbientTimedCanonicalAlpha
        (cachedInputMachine machine).State T b) := by
  letI : Fintype (cachedInputMachine machine).State :=
    (cachedInputMachine machine).stateFintype
  exact Fintype.card_subtype_le _

/-- Explicit ambient upper bound for the number of alpha-only components. -/
theorem card_builtRejectingGuardedCanonicalAlphaIndex_le_formula
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :
    letI : Fintype (cachedInputMachine machine).State :=
      (cachedInputMachine machine).stateFintype
    Fintype.card (BuiltRejectingGuardedCanonicalAlphaIndex machine T b) <=
      b ^ (T / b) *
        (1 + T * ((T / b) *
          (2 * Fintype.card (cachedInputMachine machine).State *
            (T + 1)))) ^ (T / b) *
        (Fintype.card (cachedInputMachine machine).State *
          (T + 1) * (T + 1)) := by
  letI : Fintype (cachedInputMachine machine).State :=
    (cachedInputMachine machine).stateFintype
  rw [<- card_ambientTimedCanonicalAlpha
    (cachedInputMachine machine).State T b]
  exact Fintype.card_subtype_le _

/-! ## Exact semantics, read-once behavior, and unambiguity -/

/-- Every installed component is globally read-once in the current
layered-program semantics. -/
theorem finiteRejectingGuardedCanonicalFamily_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    (finiteRejectingGuardedCanonicalFamily machine n T b).IsReadOnce := by
  intro index
  exact
    compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_isReadOnce
      machine index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1)

/-- Acceptance of one installed component is a strict certificate because
index membership already supplies the accepting terminal condition. -/
theorem builtCanonicalIndex_certificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (heval : ((finiteRejectingGuardedCanonicalFamily
      machine input.length T b).program index).eval
        (fun coordinate => input.get coordinate) = true) :
    RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1) := by
  constructor
  . simpa [finiteRejectingGuardedCanonicalFamily] using heval
  . exact index.2.2.2

/-- Exact per-index interface.  The program output supplies the compiled
canonical check, while membership in the finite subtype supplies the static
terminal accept gate. -/
theorem finiteRejectingGuardedCanonicalFamily_program_eval_eq_true_iff_certificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    ((finiteRejectingGuardedCanonicalFamily
      machine input.length T b).program index).eval
        (fun coordinate => input.get coordinate) = true <->
      RejectingMasterGuardedFusedAcceptingComponentCertificate
        machine input index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1) := by
  constructor
  . exact builtCanonicalIndex_certificate machine input index
  . intro hcertificate
    simpa [finiteRejectingGuardedCanonicalFamily] using hcertificate.1

/-- The finite family union is exactly cached acceptance at horizon `T`. -/
theorem finiteRejectingGuardedCanonicalFamily_eval_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (finiteRejectingGuardedCanonicalFamily
        machine input.length T b).eval
          (fun coordinate => input.get coordinate) = true <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  rw [FiniteLayeredQueryProgramFamily.eval_eq_true_iff]
  constructor
  . rintro ⟨index, heval⟩
    exact
      (exists_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
        machine input T b hb).1
          ⟨index.1,
            builtTimedAlphaVisitSchedule
              (cachedInputMachine machine) index.1,
            builtCanonicalIndex_certificate machine input index heval⟩
  . intro haccept
    obtain ⟨alpha, scheduled, hcertificate⟩ :=
      (exists_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
        machine input T b hb).2 haccept
    have hcheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) input alpha scheduled = true :=
      (rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
        machine input alpha scheduled).1 hcertificate |>.1
    have hbase : timedAlphaVisitScheduleAllBlockVisitsCheck
        (cachedInputMachine machine) input alpha scheduled = true := by
      rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck,
        Bool.and_eq_true] at hcheck
      exact hcheck.1
    have hreflect :=
      (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
        (cachedInputMachine machine) input alpha scheduled).1 hbase
    have hvalid : TimedAlphaVisitScheduleValid
        (cachedInputMachine machine) alpha scheduled := hreflect.1
    have hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        (cachedInputMachine machine) input alpha scheduled hreflect.2
    have hschedule : builtTimedAlphaVisitSchedule
        (cachedInputMachine machine) alpha = scheduled :=
      builtTimedAlphaVisitSchedule_eq_of_valid
        (cachedInputMachine machine) alpha scheduled hvalid
    have heligible :
        BuiltRejectingGuardedCanonicalAlphaEligible machine alpha := by
      constructor
      . rw [hschedule]
        exact (timedAlphaVisitScheduleCheck_eq_true_iff
          (cachedInputMachine machine) alpha scheduled).2 hvalid
      constructor
      . rw [hschedule]
        exact (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
          scheduled).2 hmonotone
      . exact hcertificate.2
    let index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b :=
      ⟨alpha, heligible⟩
    refine ⟨index, ?_⟩
    change
      (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := input.length) machine alpha
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) alpha)).eval
              (fun coordinate => input.get coordinate) = true
    rw [hschedule]
    exact hcertificate.1

/-- The finite family is pointwise unambiguous on the list presentation used
by the one-tape machine: two accepting installed components have the same
alpha index. -/
theorem finiteRejectingGuardedCanonicalFamily_accepting_index_unique
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b}
    (hleft : ((finiteRejectingGuardedCanonicalFamily
      machine input.length T b).program left).eval
        (fun coordinate => input.get coordinate) = true)
    (hright : ((finiteRejectingGuardedCanonicalFamily
      machine input.length T b).program right).eval
        (fun coordinate => input.get coordinate) = true) :
    left = right := by
  apply Subtype.ext
  exact
    rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_unique
      machine input T b hb
      (builtCanonicalIndex_certificate machine input left hleft)
      (builtCanonicalIndex_certificate machine input right hright)

/-- Pointwise unambiguity in the generic `Fin n -> Bool` family API.  The
dependent list-length witness below transports the same input bits to the
one-tape list convention without assuming proof-irrelevant index casts by
fiat. -/
theorem finiteRejectingGuardedCanonicalFamily_isUnambiguous
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) :
    (finiteRejectingGuardedCanonicalFamily machine n T b).IsUnambiguous := by
  intro bits left right hleft hright
  have hrepresentation :
      Exists fun input : List Bool =>
        Exists fun hlen : input.length = n =>
          forall coordinate : Fin input.length,
            input.get coordinate = bits (Fin.cast hlen coordinate) := by
    refine Exists.intro (List.ofFn bits) ?_
    refine Exists.intro List.length_ofFn ?_
    intro coordinate
    rw [List.get_ofFn]
  choose input hlen hget using hrepresentation
  subst n
  apply finiteRejectingGuardedCanonicalFamily_accepting_index_unique
    machine input T b hb
  case hleft =>
    rw [show (fun coordinate => input.get coordinate) = bits by
      funext coordinate
      exact hget coordinate]
    exact hleft
  case hright =>
    rw [show (fun coordinate => input.get coordinate) = bits by
      funext coordinate
      exact hget coordinate]
    exact hright

/-- Cached acceptance is equivalent to existence of exactly one accepting
index in the finite family. -/
theorem existsUnique_finiteRejectingGuardedCanonicalFamily_index_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (∃! index,
      ((finiteRejectingGuardedCanonicalFamily
        machine input.length T b).program index).eval
          (fun coordinate => input.get coordinate) = true) <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  constructor
  . rintro ⟨index, heval, _unique⟩
    exact
      (finiteRejectingGuardedCanonicalFamily_eval_eq_true_iff
        machine input T b hb).1
        ((FiniteLayeredQueryProgramFamily.eval_eq_true_iff _ _).2
          ⟨index, heval⟩)
  . intro haccept
    have hunion :=
      (finiteRejectingGuardedCanonicalFamily_eval_eq_true_iff
        machine input T b hb).2 haccept
    obtain ⟨index, heval⟩ :=
      (FiniteLayeredQueryProgramFamily.eval_eq_true_iff _ _).1 hunion
    refine ⟨index, heval, ?_⟩
    intro other hother
    exact finiteRejectingGuardedCanonicalFamily_accepting_index_unique
      machine input T b hb hother heval

/-! ## Mandatory fixed-order realization of every installed component -/

/-- Eligibility recovers the chaining field needed for duplicate-freedom of
the static schedule master. -/
theorem builtRejectingGuardedCanonicalIndex_chained
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    TimedAlphaScheduledVisitsChained
      (builtTimedAlphaVisitSchedule
        (cachedInputMachine machine) index.1) := by
  have hvalid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1) :=
    (timedAlphaVisitScheduleCheck_eq_true_iff
      (cachedInputMachine machine) index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1)).1 index.2.1
  rcases hvalid with
    ⟨_syntactic, _cursor, _prefix, _fold, _finish, hchained⟩
  exact hchained

/-- The master of every installed alpha component is duplicate-free. -/
theorem builtRejectingGuardedCanonicalIndex_master_nodup
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    (finiteCachedTimedAlphaScheduleMasterQueryOrder
      (n := n)
      (builtTimedAlphaVisitSchedule
        (cachedInputMachine machine) index.1)
      (builtRejectingGuardedCanonicalIndexMonotone machine index)).Nodup := by
  exact finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
    (builtTimedAlphaVisitSchedule
      (cachedInputMachine machine) index.1)
    (builtRejectingGuardedCanonicalIndex_chained machine index)
    (builtRejectingGuardedCanonicalIndexMonotone machine index)

/-- Literal `n`-layer mandatory fixed-order realization of one installed
component.  Silent verifier layers are collapsed by query count and unread
coordinates are queried as ignored padding. -/
def mandatoryBuiltRejectingGuardedCanonicalComponent
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    LayeredQueryProgram n n :=
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone := builtRejectingGuardedCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  LayeredQueryProgram.collapseToMandatoryFixedOrder
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine index.1 scheduled)
    master
    (builtRejectingGuardedCanonicalIndex_master_nodup machine n index)

/-- The mandatory realization is extensionally identical to its installed
strict guarded component on every Boolean input. -/
theorem mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (input : Fin n -> Bool) :
    (mandatoryBuiltRejectingGuardedCanonicalComponent
      machine n index).eval input =
      ((finiteRejectingGuardedCanonicalFamily
        machine n T b).program index).eval input := by
  rw [mandatoryBuiltRejectingGuardedCanonicalComponent,
    LayeredQueryProgram.collapseToMandatoryFixedOrder_eval_eq_rejectingGuard]
  change
    (LayeredQueryProgram.rejectingGuardByMasterOrder
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1))
      (finiteCachedTimedAlphaScheduleMasterQueryOrder
        (n := n)
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1)
        (builtRejectingGuardedCanonicalIndexMonotone
          machine index))).eval input =
      (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)).eval input
  unfold
    compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
  rw [dif_pos index.2.1, dif_pos index.2.2.1]
  rfl

/-- Every mandatory realization queries a fixed permutation and is therefore
read-once on every input. -/
theorem mandatoryBuiltRejectingGuardedCanonicalComponent_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    (mandatoryBuiltRejectingGuardedCanonicalComponent
      machine n index).IsReadOnce := by
  exact LayeredQueryProgram.collapseToMandatoryFixedOrder_isReadOnce _ _ _

/-- Exact width after collapsing silent layers and adding the two shared
completed-result states. -/
theorem mandatoryBuiltRejectingGuardedCanonicalComponent_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    (mandatoryBuiltRejectingGuardedCanonicalComponent
      machine n index).width =
      finiteCachedAllBlocksFuel (fun block =>
        timedAlphaBlockVisits block
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)) *
        (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
          (n := n) machine index.1
            (builtTimedAlphaVisitSchedule
              (cachedInputMachine machine) index.1)).width + 2 := by
  exact LayeredQueryProgram.collapseToMandatoryFixedOrder_width _ _ _

/-- Uniform `n`-layer family obtained by applying the mandatory collapse to
every eligible alpha component. -/
def mandatoryFiniteRejectingGuardedCanonicalFamily
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) : FiniteLayeredQueryProgramFamily n where
  Index := BuiltRejectingGuardedCanonicalAlphaIndex machine T b
  indexFintype := inferInstance
  layers := fun _index => n
  program := fun index =>
    mandatoryBuiltRejectingGuardedCanonicalComponent machine n index

/-- Every member of the uniform mandatory family is read-once. -/
theorem mandatoryFiniteRejectingGuardedCanonicalFamily_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    (mandatoryFiniteRejectingGuardedCanonicalFamily
      machine n T b).IsReadOnce := by
  intro index
  exact mandatoryBuiltRejectingGuardedCanonicalComponent_isReadOnce
    machine n index

/-- Componentwise equivalence transfers pointwise unambiguity to the uniform
mandatory family. -/
theorem mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) :
    (mandatoryFiniteRejectingGuardedCanonicalFamily
      machine n T b).IsUnambiguous := by
  intro input left right hleft hright
  apply finiteRejectingGuardedCanonicalFamily_isUnambiguous
    machine n T b hb input left right
  . rw [← mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family]
    exact hleft
  . rw [← mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family]
    exact hright

/-- The finite OR of the uniform mandatory components is still exactly cached
one-tape acceptance. -/
theorem mandatoryFiniteRejectingGuardedCanonicalFamily_eval_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (mandatoryFiniteRejectingGuardedCanonicalFamily
      machine input.length T b).eval
        (fun coordinate => input.get coordinate) = true <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  rw [FiniteLayeredQueryProgramFamily.eval_eq_true_iff]
  rw [← finiteRejectingGuardedCanonicalFamily_eval_eq_true_iff
    machine input T b hb]
  rw [FiniteLayeredQueryProgramFamily.eval_eq_true_iff]
  constructor
  . rintro ⟨index, heval⟩
    exact ⟨index,
      (mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family
        machine input.length index
          (fun coordinate => input.get coordinate)).symm.trans heval⟩
  . rintro ⟨index, heval⟩
    exact ⟨index,
      (mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family
        machine input.length index
          (fun coordinate => input.get coordinate)).trans heval⟩

end OneTapeMagnification
end Frontier
end Pnp4
