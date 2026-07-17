import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorCompleteness
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDAffineRestrictionIteration

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The parallel mandatory canonical nonaccepting selector

The accepting mandatory selector cannot be complemented by merely exchanging
its two sinks: on a rejected input every alpha component would then create an
accepting path.  Instead this file keeps the same exact canonical verifier and
indexes it by structurally eligible alphas whose advertised terminal state is
*not* accepting.  Since the verifier accepts exactly the chronological alpha,
the resulting union is again unambiguous and computes the pointwise complement
of the accepting selector.

The construction has the same mandatory fixed-order and per-component width
as the accepting construction.  Its total selector size is a disjoint-family
sum over a different alpha subtype; no comparison between the two sums, and no
polynomial sharing bound, is asserted.
-/

noncomputable section

local instance cachedInputMachineStateDecidableEqForNonacceptingSelector
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Static membership conditions for a nonaccepting canonical component.
The first two checks are exactly the structural checks used by the accepting
family; only the terminal gate is complemented. -/
def BuiltNonacceptingCanonicalAlphaEligible
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b) : Prop :=
  timedAlphaVisitScheduleCheck (cachedInputMachine machine) alpha
      (builtTimedAlphaVisitSchedule (cachedInputMachine machine) alpha) = true /\
    timedAlphaScheduledVisitsInputMonotoneCheck
      (builtTimedAlphaVisitSchedule (cachedInputMachine machine) alpha) = true /\
    Not ((cachedInputMachine machine).halt alpha.terminal.state = some .accept)

/-- Finite alpha-only index type for nonaccepting canonical components. -/
abbrev BuiltNonacceptingCanonicalAlphaIndex
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :=
  { alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b //
    BuiltNonacceptingCanonicalAlphaEligible machine alpha }

instance builtNonacceptingCanonicalAlphaIndexFintype
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :
    Fintype (BuiltNonacceptingCanonicalAlphaIndex machine T b) := by
  letI : Fintype (cachedInputMachine machine).State :=
    (cachedInputMachine machine).stateFintype
  letI : DecidablePred
      (BuiltNonacceptingCanonicalAlphaEligible
        machine (T := T) (b := b)) := fun alpha => by
    unfold BuiltNonacceptingCanonicalAlphaEligible
    infer_instance
  exact inferInstance

/-- The nonaccepting alpha subtype has the same ambient finite cap as the
accepting alpha subtype. -/
theorem card_builtNonacceptingCanonicalAlphaIndex_le_ambient
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :
    letI : Fintype (cachedInputMachine machine).State :=
      (cachedInputMachine machine).stateFintype
    Fintype.card (BuiltNonacceptingCanonicalAlphaIndex machine T b) <=
      Fintype.card (AmbientTimedCanonicalAlpha
        (cachedInputMachine machine).State T b) := by
  letI : Fintype (cachedInputMachine machine).State :=
    (cachedInputMachine machine).stateFintype
  exact Fintype.card_subtype_le _

/-- Monotonicity hardwired by nonaccepting-index membership. -/
def builtNonacceptingCanonicalIndexMonotone
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
    TimedAlphaScheduledVisitsInputMonotone
      (builtTimedAlphaVisitSchedule
        (cachedInputMachine machine) index.1) :=
  (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
    (builtTimedAlphaVisitSchedule
      (cachedInputMachine machine) index.1)).1 index.2.2.1

/-- Schedule validity hardwired by nonaccepting-index membership supplies
the chaining property needed for a duplicate-free master. -/
theorem builtNonacceptingCanonicalIndex_chained
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
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
    ⟨_, _finalCursor, _prefix, _fold, _finish, hchained⟩
  exact hchained

/-- The finite input-query master of every nonaccepting component is
duplicate-free. -/
theorem builtNonacceptingCanonicalIndex_master_nodup
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
    (finiteCachedTimedAlphaScheduleMasterQueryOrder
      (n := n)
      (builtTimedAlphaVisitSchedule
        (cachedInputMachine machine) index.1)
      (builtNonacceptingCanonicalIndexMonotone machine index)).Nodup := by
  exact finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
    (builtTimedAlphaVisitSchedule
      (cachedInputMachine machine) index.1)
    (builtNonacceptingCanonicalIndex_chained machine index)
    (builtNonacceptingCanonicalIndexMonotone machine index)

/-- Literal `n`-layer mandatory fixed-order realization of one
nonaccepting-terminal canonical component.  The program itself is the same
canonical transcript verifier as on the accepting side; terminal polarity is
carried by index membership. -/
def mandatoryBuiltNonacceptingCanonicalComponent
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
    LayeredQueryProgram n n :=
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone := builtNonacceptingCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  LayeredQueryProgram.collapseToMandatoryFixedOrder
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine index.1 scheduled)
    master
    (builtNonacceptingCanonicalIndex_master_nodup machine n index)

/-- The mandatory nonaccepting realization is extensionally identical to the
strict total canonical verifier on its installed alpha and schedule. -/
theorem mandatoryBuiltNonacceptingCanonicalComponent_eval_eq_total
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b)
    (input : Fin n -> Bool) :
    (mandatoryBuiltNonacceptingCanonicalComponent
      machine n index).eval input =
      (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)).eval input := by
  rw [mandatoryBuiltNonacceptingCanonicalComponent,
    LayeredQueryProgram.collapseToMandatoryFixedOrder_eval_eq_rejectingGuard]
  unfold
    compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
  rw [dif_pos index.2.1, dif_pos index.2.2.1]
  rfl

/-- Every nonaccepting mandatory component has a fixed completed query
order. -/
def mandatoryBuiltNonacceptingCanonicalQueryOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
    Fin n -> Fin n :=
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone := builtNonacceptingCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  LayeredQueryProgram.completeMasterQuery master
    (builtNonacceptingCanonicalIndex_master_nodup machine n index)

theorem mandatoryBuiltNonacceptingCanonicalComponent_hasFixedQueryOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
    (mandatoryBuiltNonacceptingCanonicalComponent machine n index)
      |>.HasFixedQueryOrder
        (fun layer => some
          (mandatoryBuiltNonacceptingCanonicalQueryOrder
            machine n index layer)) := by
  unfold mandatoryBuiltNonacceptingCanonicalComponent
    mandatoryBuiltNonacceptingCanonicalQueryOrder
  exact LayeredQueryProgram.collapseToMandatoryFixedOrder_hasFixedQueryOrder
    _ _ _

theorem mandatoryBuiltNonacceptingCanonicalQueryOrder_nodup
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
    (List.ofFn
      (mandatoryBuiltNonacceptingCanonicalQueryOrder
        machine n index)).Nodup := by
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone := builtNonacceptingCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  let hmaster : master.Nodup := by
    dsimp [master, scheduled, hmonotone]
    exact builtNonacceptingCanonicalIndex_master_nodup machine n index
  change (List.ofFn
    (LayeredQueryProgram.completeMasterQuery master hmaster)).Nodup
  rw [LayeredQueryProgram.listOfFn_completeMasterQuery master hmaster]
  exact LayeredQueryProgram.completeMasterOrder_nodup master hmaster

/-- Exact per-component width.  This is the same formula as for an accepting
alpha with the same installed schedule. -/
theorem mandatoryBuiltNonacceptingCanonicalComponent_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b) :
    (mandatoryBuiltNonacceptingCanonicalComponent machine n index).width =
      finiteCachedAllBlocksFuel (fun block =>
        timedAlphaBlockVisits block
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)) *
        (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
          (n := n) machine index.1
            (builtTimedAlphaVisitSchedule
              (cachedInputMachine machine) index.1)).width + 2 := by
  exact LayeredQueryProgram.collapseToMandatoryFixedOrder_width _ _ _

/-- Uniform mandatory family over nonaccepting-terminal eligible alphas. -/
def mandatoryFiniteNonacceptingCanonicalFamily
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) : FiniteLayeredQueryProgramFamily n where
  Index := BuiltNonacceptingCanonicalAlphaIndex machine T b
  indexFintype := inferInstance
  layers := fun _ => n
  program := fun index =>
    mandatoryBuiltNonacceptingCanonicalComponent machine n index

/-- An accepted nonaccepting component still forces its alpha to be the
unique chronological alpha. -/
theorem mandatoryBuiltNonacceptingCanonicalComponent_alpha_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (index : BuiltNonacceptingCanonicalAlphaIndex machine T b)
    (heval : (mandatoryBuiltNonacceptingCanonicalComponent
      machine input.length index).eval
        (fun coordinate => input.get coordinate) = true) :
    index.1 = chronologicalTimedCanonicalAlpha
      (cachedInputMachine machine) input T b hb := by
  have htotal :
      (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := input.length) machine index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1)).eval
        (fun coordinate => input.get coordinate) = true :=
    (mandatoryBuiltNonacceptingCanonicalComponent_eval_eq_total
      machine input.length index
        (fun coordinate => input.get coordinate)).symm.trans heval
  have hcheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) input index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1) = true := by
    rw [← compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_inPlaceCanonicalCutCheck]
    exact htotal
  have hreplayed :
      timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
        (cachedInputMachine machine) input index.1
          (builtTimedAlphaVisitSchedule
            (cachedInputMachine machine) index.1) = true :=
    (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
      (cachedInputMachine machine) input T b hb index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1)).1 hcheck
  exact
    timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
      (cachedInputMachine machine) input T b hb index.1
        (builtTimedAlphaVisitSchedule
          (cachedInputMachine machine) index.1) hreplayed

/-- Two accepted nonaccepting components have the same subtype index. -/
theorem mandatoryFiniteNonacceptingCanonicalFamily_accepting_index_unique
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : BuiltNonacceptingCanonicalAlphaIndex machine T b}
    (hleft : (mandatoryBuiltNonacceptingCanonicalComponent
      machine input.length left).eval
        (fun coordinate => input.get coordinate) = true)
    (hright : (mandatoryBuiltNonacceptingCanonicalComponent
      machine input.length right).eval
        (fun coordinate => input.get coordinate) = true) :
    left = right := by
  apply Subtype.ext
  exact
    (mandatoryBuiltNonacceptingCanonicalComponent_alpha_eq
      machine input T b hb left hleft).trans
    (mandatoryBuiltNonacceptingCanonicalComponent_alpha_eq
      machine input T b hb right hright).symm

/-- Exact Boolean semantics of the nonaccepting family union. -/
theorem mandatoryFiniteNonacceptingCanonicalFamily_eval_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (mandatoryFiniteNonacceptingCanonicalFamily
      machine input.length T b).eval
        (fun coordinate => input.get coordinate) = true <->
      Not (IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T)) := by
  rw [FiniteLayeredQueryProgramFamily.eval_eq_true_iff]
  constructor
  . rintro ⟨index, heval⟩
    intro haccept
    have halpha :=
      mandatoryBuiltNonacceptingCanonicalComponent_alpha_eq
        machine input T b hb index heval
    have hterminal := index.2.2.2
    apply hterminal
    rw [halpha]
    simpa [IsAccepting, outcome, chronologicalTimedCanonicalAlpha] using
      haccept
  . intro hnonaccept
    let cached := cachedInputMachine machine
    let alpha : AmbientTimedCanonicalAlpha cached.State T b :=
      chronologicalTimedCanonicalAlpha cached input T b hb
    obtain ⟨scheduled, hreplayed⟩ :=
      exists_actualTimedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true
        cached input T b hb
    have hbase : timedAlphaVisitScheduleAllBlockVisitsCheck
        cached input alpha scheduled = true :=
      (timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true_iff
        cached input T b hb alpha scheduled).1 (by
          simpa [alpha] using hreplayed) |>.1
    have hreflect :=
      (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
        cached input alpha scheduled).1 hbase
    have hvalid : TimedAlphaVisitScheduleValid cached alpha scheduled :=
      hreflect.1
    have hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        cached input alpha scheduled hreflect.2
    have hschedule : builtTimedAlphaVisitSchedule cached alpha = scheduled :=
      builtTimedAlphaVisitSchedule_eq_of_valid cached alpha scheduled hvalid
    have hterminal : Not (cached.halt alpha.terminal.state = some .accept) := by
      simpa [cached, alpha, IsAccepting, outcome,
        chronologicalTimedCanonicalAlpha] using hnonaccept
    have heligible :
        BuiltNonacceptingCanonicalAlphaEligible machine alpha := by
      constructor
      . rw [hschedule]
        exact (timedAlphaVisitScheduleCheck_eq_true_iff
          cached alpha scheduled).2 hvalid
      constructor
      . rw [hschedule]
        exact (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
          scheduled).2 hmonotone
      . exact hterminal
    let index : BuiltNonacceptingCanonicalAlphaIndex machine T b :=
      ⟨alpha, heligible⟩
    refine ⟨index, ?_⟩
    have hinPlace : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        cached input alpha scheduled = true :=
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
        cached input T b hb alpha scheduled).2 (by
          simpa [alpha] using hreplayed)
    have htotal :
        (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
          (n := input.length) machine alpha scheduled).eval
            (fun coordinate => input.get coordinate) = true := by
      rw [compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_inPlaceCanonicalCutCheck]
      exact hinPlace
    have htotalBuilt :
        (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
          (n := input.length) machine alpha
            (builtTimedAlphaVisitSchedule cached alpha)).eval
              (fun coordinate => input.get coordinate) = true := by
      rw [hschedule]
      exact htotal
    exact
      (mandatoryBuiltNonacceptingCanonicalComponent_eval_eq_total
        machine input.length index
          (fun coordinate => input.get coordinate)).trans htotalBuilt

/-- Pointwise unambiguity of the nonaccepting family. -/
theorem mandatoryFiniteNonacceptingCanonicalFamily_isUnambiguous
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) :
    (mandatoryFiniteNonacceptingCanonicalFamily
      machine n T b).IsUnambiguous := by
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
  apply mandatoryFiniteNonacceptingCanonicalFamily_accepting_index_unique
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

/-- The single finite selector diagram for nonaccepting canonical
components. -/
noncomputable abbrev mandatoryCanonicalNonacceptingUFBDD
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) : FiniteUnambiguousFBDD n :=
  (mandatoryFiniteNonacceptingCanonicalFamily machine n T b).selectorFBDD

/-- Exact complement semantics on the native list-input presentation. -/
theorem mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_cached_acceptance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalNonacceptingUFBDD
      machine input.length T b).Accepts
        (fun coordinate => input.get coordinate) <->
      Not (IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T)) := by
  rw [FiniteLayeredQueryProgramFamily.selectorFBDD_accepts_iff_eval_eq_true]
  exact mandatoryFiniteNonacceptingCanonicalFamily_eval_eq_true_iff
    machine input T b hb

/-- Transport the list-input semantics along an exact representation of a
function input. -/
theorem mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_cached_acceptance_of_word
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : Fin n -> Bool) (word : List Bool)
    (hlen : word.length = n)
    (hget : forall coordinate : Fin word.length,
      word.get coordinate = input (Fin.cast hlen coordinate))
    (T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalNonacceptingUFBDD machine n T b).Accepts input <->
      Not (IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) word T)) := by
  subst n
  rw [show input = (fun coordinate => word.get coordinate) by
    funext coordinate
    exact (hget coordinate).symm]
  exact
    (mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_cached_acceptance
      machine word T b hb)

/-- Function-input form specialized to its canonical list representation. -/
theorem mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_cached_acceptance_ofFn
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : Fin n -> Bool) (T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalNonacceptingUFBDD machine n T b).Accepts input <->
      Not (IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) (List.ofFn input) T)) := by
  apply mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_cached_acceptance_of_word
    machine input (List.ofFn input) List.length_ofFn
  . intro coordinate
    rw [List.get_ofFn]
  . exact hb

/-- Transport the existing accepting selector's list semantics along an
exact representation of a function input. -/
theorem mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance_of_word
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : Fin n -> Bool) (word : List Bool)
    (hlen : word.length = n)
    (hget : forall coordinate : Fin word.length,
      word.get coordinate = input (Fin.cast hlen coordinate))
    (T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalUFBDD machine n T b).Accepts input <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) word T) := by
  subst n
  rw [show input = (fun coordinate => word.get coordinate) by
    funext coordinate
    exact (hget coordinate).symm]
  exact mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance
    machine word T b hb

/-- Function-input form specialized to its canonical list representation. -/
theorem mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance_ofFn
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : Fin n -> Bool) (T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalUFBDD machine n T b).Accepts input <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) (List.ofFn input) T) := by
  apply mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance_of_word
    machine input (List.ofFn input) List.length_ofFn
  . intro coordinate
    rw [List.get_ofFn]
  . exact hb

/-- Direct selector-level complement: exactly one of the accepting and
nonaccepting mandatory selectors accepts each input. -/
theorem mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_mandatoryCanonicalUFBDD
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (input : Fin n -> Bool) :
    (mandatoryCanonicalNonacceptingUFBDD machine n T b).Accepts input <->
      Not ((mandatoryCanonicalUFBDD machine n T b).Accepts input) := by
  rw [mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_cached_acceptance_ofFn
      machine input T b hb,
    mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance_ofFn
      machine input T b hb]

/-- The nonaccepting selector is syntactically read-once. -/
theorem mandatoryCanonicalNonacceptingUFBDD_isSyntacticallyReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    (mandatoryCanonicalNonacceptingUFBDD
      machine n T b).IsSyntacticallyReadOnce := by
  apply FiniteLayeredQueryProgramFamily.selectorFBDD_isSyntacticallyReadOnce_of_fixedMandatoryOrder
      (order := fun index =>
        mandatoryBuiltNonacceptingCanonicalQueryOrder machine n index)
  . intro index
    exact mandatoryBuiltNonacceptingCanonicalComponent_hasFixedQueryOrder
      machine n index
  . intro index
    exact mandatoryBuiltNonacceptingCanonicalQueryOrder_nodup
      machine n index

/-- Positive block size makes the nonaccepting selector unambiguous. -/
theorem mandatoryCanonicalNonacceptingUFBDD_isUnambiguous
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) :
    (mandatoryCanonicalNonacceptingUFBDD machine n T b).IsUnambiguous := by
  apply FiniteLayeredQueryProgramFamily.selectorFBDD_isUnambiguous_of_family
  exact mandatoryFiniteNonacceptingCanonicalFamily_isUnambiguous
    machine n T b hb

/-- Every formal accepting path reads every input coordinate. -/
theorem mandatoryCanonicalNonacceptingUFBDD_acceptingPath_queryVars_eq_univ
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (input : Fin n -> Bool)
    (path : (mandatoryCanonicalNonacceptingUFBDD
      machine n T b).AcceptingPath input) :
    path.walk.queryVars = Finset.univ := by
  let family := mandatoryFiniteNonacceptingCanonicalFamily machine n T b
  let order : (index : family.Index) ->
      Fin (family.layers index) -> Fin n := fun index =>
    mandatoryBuiltNonacceptingCanonicalQueryOrder machine n index
  apply FiniteLayeredQueryProgramFamily.selectorAcceptingPath_queryVars_eq_univ_of_fixedMandatoryOrder
      family order
  . intro index
    exact mandatoryBuiltNonacceptingCanonicalComponent_hasFixedQueryOrder
      machine n index
  . intro index
    rfl
  . intro index
    exact mandatoryBuiltNonacceptingCanonicalQueryOrder_nodup
      machine n index

/-- Exact disjoint-family vertex count. -/
theorem mandatoryCanonicalNonacceptingUFBDD_vertex_card
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    @Fintype.card
        (mandatoryCanonicalNonacceptingUFBDD machine n T b).Vertex
        (mandatoryCanonicalNonacceptingUFBDD
          machine n T b).vertexFintype =
      (∑ index : BuiltNonacceptingCanonicalAlphaIndex machine T b,
        (n + 1) *
          (mandatoryBuiltNonacceptingCanonicalComponent
            machine n index).width) + 3 := by
  rw [FiniteLayeredQueryProgramFamily.selectorFBDD_vertex_card]
  unfold FiniteLayeredQueryProgramFamily.layeredStateSlotCount
  simp [mandatoryFiniteNonacceptingCanonicalFamily]

/-- Exact pointwise rational complement of the accepting mandatory
selector. -/
theorem mandatoryCanonicalNonacceptingUFBDD_ratAcceptanceIndicator_eq_one_sub
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (input : Fin n -> Bool) :
    (mandatoryCanonicalNonacceptingUFBDD
      machine n T b).ratAcceptanceIndicator input =
      1 - (mandatoryCanonicalUFBDD
        machine n T b).ratAcceptanceIndicator input := by
  unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
  have hnonaccept :=
    mandatoryCanonicalNonacceptingUFBDD_accepts_iff_not_cached_acceptance_ofFn
      machine input T b hb
  have haccept' :=
    mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance_ofFn
      machine input T b hb
  rw [propext hnonaccept, propext haccept']
  by_cases h : IsAccepting (cachedInputMachine machine)
      (run (cachedInputMachine machine) (List.ofFn input) T) <;> simp [h]

/-- Affine-prefix version used by adjacent hybrid steps. -/
noncomputable abbrev prefixedMandatoryCanonicalNonacceptingSelector
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound n)) :
    FiniteUnambiguousFBDD n :=
  (mandatoryCanonicalNonacceptingUFBDD machine n T b)
    |>.affinePaddedRestrictByRounds rounds

/-- The pointwise complement identity survives every fixed affine prefix. -/
theorem prefixedMandatoryCanonicalNonacceptingSelector_ratAcceptanceIndicator_eq_one_sub
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n)) (input : Fin n -> Bool) :
    (prefixedMandatoryCanonicalNonacceptingSelector
      machine n T b rounds).ratAcceptanceIndicator input =
      1 - ((mandatoryCanonicalUFBDD machine n T b)
        |>.affinePaddedRestrictByRounds rounds).ratAcceptanceIndicator input := by
  rw [FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq]
  rw [FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq]
  exact mandatoryCanonicalNonacceptingUFBDD_ratAcceptanceIndicator_eq_one_sub
    machine n T b hb (applyAffineRestrictionRounds rounds input)

/-- Fixed affine prefixes preserve all three structural selector
properties. -/
theorem prefixedMandatoryCanonicalNonacceptingSelector_structural
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n)) :
    (prefixedMandatoryCanonicalNonacceptingSelector
        machine n T b rounds).IsSyntacticallyReadOnce /\
      (prefixedMandatoryCanonicalNonacceptingSelector
        machine n T b rounds).IsUnambiguous /\
      (forall input
        (path : (prefixedMandatoryCanonicalNonacceptingSelector
          machine n T b rounds).AcceptingPath input),
        path.walk.queryVars = Finset.univ) := by
  let B := mandatoryCanonicalNonacceptingUFBDD machine n T b
  constructor
  . exact B.affinePaddedRestrictByRounds_isSyntacticallyReadOnce rounds
      (mandatoryCanonicalNonacceptingUFBDD_isSyntacticallyReadOnce
        machine n T b)
  constructor
  . exact B.affinePaddedRestrictByRounds_isUnambiguous rounds
      (mandatoryCanonicalNonacceptingUFBDD_isUnambiguous
        machine n T b hb)
  . exact B.affinePaddedRestrictByRounds_acceptingPath_queryVars_eq_univ
      rounds (mandatoryCanonicalNonacceptingUFBDD_acceptingPath_queryVars_eq_univ
        machine n T b)

end

end OneTapeMagnification
end Frontier
end Pnp4
