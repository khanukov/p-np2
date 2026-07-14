import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitReplay
import Pnp4.Frontier.OneTapeMagnification.SilentStepQueryCollapse

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Streaming finite verifier for one cached visit

The phase machine in this file consumes one advertised machine transition per
microstep.  Its live state contains only a bounded remaining-step counter and
`LocalReplayState`; completion retains the finite final endpoint.  It decides
from that state whether the next transition needs a fresh in-range input bit.
Cached stay transitions and reads beyond the finite input are silent.
-/

/-- Explicit finite failure modes of one streaming visit. -/
inductive FiniteCachedVisitStreamingFailure where
  | zeroRemaining
  | missingFreshInput
  | unexpectedInput
  | intermediateWorkHeadExit
  | inputHorizonExceeded
  | finalWorkHorizonExceeded
deriving Fintype, DecidableEq

/-- Finite phase state for one visit. -/
inductive FiniteCachedVisitStreamingState (State : Type) (H w : Nat) where
  | running (remaining : Fin (H + 1))
      (live : LocalReplayState State H w)
  | completed (final : FiniteLocalFinalState State H w)
  | rejected (failure : FiniteCachedVisitStreamingFailure)
deriving Fintype

/-- Explicit cached-state decidable equality, since a machine stores its
finite-state instance as a field rather than a global typeclass instance. -/
def cachedInputStateDecidableEq (machine : DeterministicMachine)
    [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State := by
  change DecidableEq (Option (machine.State × ReadOnlySymbol))
  infer_instance

/-- Explicit phase Fintype for cached control. -/
def cachedFiniteVisitStreamingStateFintype
    (machine : DeterministicMachine) (H w : Nat) :
    Fintype (FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w) := by
  letI := (cachedInputMachine machine).stateFintype
  exact inferInstance

/-- Product/sum presentation of the phase state. -/
def finiteCachedVisitStreamingStateEquiv (State : Type) (H w : Nat) :
    FiniteCachedVisitStreamingState State H w ≃
      Sum (Fin (H + 1) × LocalReplayState State H w)
        (Sum (FiniteLocalFinalState State H w)
          FiniteCachedVisitStreamingFailure) where
  toFun
    | .running remaining live => .inl (remaining, live)
    | .completed final => .inr (.inl final)
    | .rejected failure => .inr (.inr failure)
  invFun
    | .inl fields => .running fields.1 fields.2
    | .inr (.inl final) => .completed final
    | .inr (.inr failure) => .rejected failure
  left_inv state := by cases state <;> rfl
  right_inv state := by
    rcases state with fields | finalOrFailure
    · rfl
    · rcases finalOrFailure with final | failure <;> rfl

/-- Exact cardinality of the generic phase carrier. -/
theorem card_finiteCachedVisitStreamingState
    (State : Type) [Fintype State] (H w : Nat) :
    Fintype.card (FiniteCachedVisitStreamingState State H w) =
      (H + 1) * (Fintype.card State * (H + 1) * w * 2 ^ w) +
        Fintype.card State * (H + 1) * (H + 1) * 2 ^ w + 6 := by
  rw [Fintype.card_congr
    (finiteCachedVisitStreamingStateEquiv State H w)]
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod,
    card_finiteLocalFinalState]
  rw [Fintype.card_congr (localReplayStateEquiv State H w)]
  have hFailure : Fintype.card FiniteCachedVisitStreamingFailure = 6 := by
    decide
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, hFailure]
  ring

/-- Exact phase-carrier size for cached control. -/
theorem card_cachedFiniteVisitStreamingState
    (machine : DeterministicMachine) (H w : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card (FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w) =
      (H + 1) *
          ((1 + 3 * @Fintype.card machine.State machine.stateFintype) *
            (H + 1) * w * 2 ^ w) +
        (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
          (H + 1) * (H + 1) * 2 ^ w + 6 := by
  letI := (cachedInputMachine machine).stateFintype
  rw [card_finiteCachedVisitStreamingState]
  rw [cachedInputMachine_state_card]

/-- Uniform `2b` upper bound for the phase carrier of any advertised block. -/
theorem card_cachedFixedAlphaVisitStreamingState_le
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) :
    @Fintype.card (FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth offsets block))
      (cachedFiniteVisitStreamingStateFintype machine T
        (advertisedBlockWidth offsets block)) ≤
      (T + 1) *
          ((1 + 3 * @Fintype.card machine.State machine.stateFintype) *
            (T + 1) * (2 * b) * 2 ^ (2 * b)) +
        (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
          (T + 1) * (T + 1) * 2 ^ (2 * b) + 6 := by
  rw [card_cachedFiniteVisitStreamingState]
  have hwidth := advertisedBlockWidth_le_two_mul hb offsets block
  have hpow : 2 ^ advertisedBlockWidth offsets block ≤ 2 ^ (2 * b) :=
    Nat.pow_le_pow_right (by omega) hwidth
  gcongr

/-- Whether the next nonhalting cached transition genuinely depends on the
physical unread symbol. -/
def cachedLocalStepNeedsUnread (machine : DeterministicMachine)
    {H w : Nat}
    (live : LocalReplayState (cachedInputMachine machine).State H w) : Bool :=
  match (cachedInputMachine machine).halt live.control with
  | some _ => false
  | none =>
      match live.control with
      | none => true
      | some (state, cached) =>
          match (machine.transition state cached
            (live.workSlab live.relativeWorkHead)).inputMove with
          | .stay => false
          | .right => true

/-- Structural characterization of a genuinely unread cached transition. -/
theorem cachedLocalStepNeedsUnread_eq_true_iff
    (machine : DeterministicMachine) {H w : Nat}
    (live : LocalReplayState (cachedInputMachine machine).State H w) :
    cachedLocalStepNeedsUnread machine live = true ↔
      (cachedInputMachine machine).halt live.control = none ∧
        (live.control = none ∨
          ∃ state cached,
            live.control = some (state, cached) ∧
              (machine.transition state cached
                (live.workSlab live.relativeWorkHead)).inputMove = .right) := by
  cases hhalt : (cachedInputMachine machine).halt live.control with
  | some outcome =>
      simp [cachedLocalStepNeedsUnread, hhalt]
  | none =>
      rw [cachedLocalStepNeedsUnread, hhalt]
      cases hcontrol : live.control with
      | none =>
          simp
      | some fields =>
          rcases fields with ⟨state, cached⟩
          cases hmove : (machine.transition state cached
              (live.workSlab live.relativeWorkHead)).inputMove with
          | stay =>
              simp [hmove]
              intro otherState otherCached heq hright
              rcases heq with ⟨rfl, rfl⟩
              rw [hmove] at hright
              contradiction
          | right =>
              simp [hmove]
              exact ⟨state, cached, rfl, hmove⟩

/-- Exact fresh-query predicate of a running phase. -/
def finiteCachedVisitPhaseRequestsInput
    (machine : DeterministicMachine) (n : Nat)
    {H w : Nat}
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w) : Bool :=
  match phase with
  | .running remaining live =>
      decide (0 < remaining.val) && cachedLocalStepNeedsUnread machine live &&
        decide (live.inputHead.val < n)
  | _ => false

theorem finiteCachedVisitPhaseRequestsInput_running_eq_true_iff
    (machine : DeterministicMachine) (n : Nat)
    {H w : Nat} (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w) :
    finiteCachedVisitPhaseRequestsInput machine n
        (.running remaining live) = true ↔
      0 < remaining.val ∧ cachedLocalStepNeedsUnread machine live = true ∧
        live.inputHead.val < n := by
  simp [finiteCachedVisitPhaseRequestsInput, Bool.and_eq_true]
  tauto

/-- Fully expanded fresh-input characterization. -/
theorem finiteCachedVisitPhaseRequestsInput_running_structural_iff
    (machine : DeterministicMachine) (n : Nat)
    {H w : Nat} (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w) :
    finiteCachedVisitPhaseRequestsInput machine n
        (.running remaining live) = true ↔
      0 < remaining.val ∧
        (cachedInputMachine machine).halt live.control = none ∧
        (live.control = none ∨
          ∃ state cached,
            live.control = some (state, cached) ∧
              (machine.transition state cached
                (live.workSlab live.relativeWorkHead)).inputMove = .right) ∧
        live.inputHead.val < n := by
  rw [finiteCachedVisitPhaseRequestsInput_running_eq_true_iff,
    cachedLocalStepNeedsUnread_eq_true_iff]
  tauto

/-- Spend one advertised transition in the phase-local counter. -/
def spendVisitStep {H : Nat} (remaining : Fin (H + 1)) : Fin (H + 1) :=
  ⟨remaining.val - 1,
    lt_of_le_of_lt (Nat.sub_le remaining.val 1) remaining.isLt⟩

/-- Execute one resolved cached transition.  The caller has already decided
whether `unread` came from a fresh query, a known right-end marker, or an
arbitrary value on a cached stay transition. -/
def advanceFiniteCachedVisitPhase
    (machine : DeterministicMachine) (H w base : Nat)
    (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) :
    FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w :=
  if _hzero : remaining.val = 0 then
    .rejected .zeroRemaining
  else if _hlast : remaining.val = 1 then
    match finiteLocalCachedFinalStep machine H w base unread live with
    | .stepped final => .completed final
    | .halted _ =>
        .completed (finiteLocalFinalStateOfReplayState base hbound live)
    | .inputHorizonExceeded => .rejected .inputHorizonExceeded
    | .workHorizonExceeded => .rejected .finalWorkHorizonExceeded
  else
    match finiteLocalCachedStep machine H w base unread live with
    | .inside next => .running (spendVisitStep remaining) next
    | .halted _ => .running (spendVisitStep remaining) live
    | .workHeadExit => .rejected .intermediateWorkHeadExit
    | .inputHorizonExceeded => .rejected .inputHorizonExceeded

/-- One streaming microstep.  A fresh in-range read must be supplied as
`some`; stay steps and known right-end reads must be supplied as `none`. -/
def finiteCachedVisitStreamingStep
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) :
    FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State H w →
      Option ReadOnlySymbol →
      FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State H w
  | phase@(.completed _), _ => phase
  | phase@(.rejected _), _ => phase
  | .running remaining live, supplied =>
      if cachedLocalStepNeedsUnread machine live then
        if live.inputHead.val < n then
          match supplied with
          | some unread => advanceFiniteCachedVisitPhase machine H w base
              hbound remaining live unread
          | none => .rejected .missingFreshInput
        else
          match supplied with
          | none => advanceFiniteCachedVisitPhase machine H w base hbound
              remaining live .rightEnd
          | some _ => .rejected .unexpectedInput
      else
        match supplied with
        | none => advanceFiniteCachedVisitPhase machine H w base hbound
            remaining live .rightEnd
        | some _ => .rejected .unexpectedInput

/-- If the cached transition does not need the physical unread symbol, the
resolved phase transition is independent of which symbol is supplied. -/
theorem advanceFiniteCachedVisitPhase_unread_independent
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread₁ unread₂ : ReadOnlySymbol)
    (hneeds : cachedLocalStepNeedsUnread machine live = false) :
    advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        unread₁ =
      advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        unread₂ := by
  have hfinal : finiteLocalCachedFinalStep machine H w base unread₁ live =
      finiteLocalCachedFinalStep machine H w base unread₂ live := by
    cases hhalt : (cachedInputMachine machine).halt live.control with
    | some outcome =>
        unfold finiteLocalCachedFinalStep
        rw [hhalt]
    | none =>
        rw [cachedLocalStepNeedsUnread, hhalt] at hneeds
        cases hcontrol : live.control with
        | none =>
            simp [hcontrol] at hneeds
        | some fields =>
            rcases fields with ⟨state, cached⟩
            cases hmove : (machine.transition state cached
                (live.workSlab live.relativeWorkHead)).inputMove with
            | stay =>
                exact finiteLocalCachedFinalStep_stay_independent
                  machine live state cached hcontrol unread₁ unread₂ hmove
            | right =>
                simp [hcontrol, hmove] at hneeds
  have hinside : finiteLocalCachedStep machine H w base unread₁ live =
      finiteLocalCachedStep machine H w base unread₂ live := by
    cases hhalt : (cachedInputMachine machine).halt live.control with
    | some outcome =>
        unfold finiteLocalCachedStep
        rw [hhalt]
    | none =>
        rw [cachedLocalStepNeedsUnread, hhalt] at hneeds
        cases hcontrol : live.control with
        | none =>
            simp [hcontrol] at hneeds
        | some fields =>
            rcases fields with ⟨state, cached⟩
            cases hmove : (machine.transition state cached
                (live.workSlab live.relativeWorkHead)).inputMove with
            | stay =>
                exact finiteLocalCachedStep_stay_independent
                  machine live state cached hcontrol unread₁ unread₂ hmove
            | right =>
                simp [hcontrol, hmove] at hneeds
  unfold advanceFiniteCachedVisitPhase
  split
  · rfl
  · split
    · rw [hfinal]
    · rw [hinside]

/-- Option supplied to the streaming microstep when comparing it with a
per-transition unread-symbol trace. -/
def streamingAnswerForUnread
    (machine : DeterministicMachine) (n : Nat)
    {H w : Nat}
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) : Option ReadOnlySymbol :=
  if cachedLocalStepNeedsUnread machine live &&
      decide (live.inputHead.val < n) then
    some unread
  else
    none

/-- One streaming microstep equals the resolved per-transition step.  The
only required side condition says that a true unread transition beyond the
finite input is represented by the known `rightEnd` symbol. -/
theorem finiteCachedVisitStreamingStep_answerForUnread
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (hend : cachedLocalStepNeedsUnread machine live = true →
      ¬ live.inputHead.val < n → unread = .rightEnd) :
    finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live)
        (streamingAnswerForUnread machine n live unread) =
      advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        unread := by
  by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
  · by_cases hhead : live.inputHead.val < n
    · simp [finiteCachedVisitStreamingStep, streamingAnswerForUnread,
        hneeds, hhead]
    · have hunread := hend hneeds hhead
      subst unread
      simp [finiteCachedVisitStreamingStep, streamingAnswerForUnread,
        hneeds, hhead]
  · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
      cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
    rw [show streamingAnswerForUnread machine n live unread = none by
      simp [streamingAnswerForUnread, hneedsFalse]]
    simp only [finiteCachedVisitStreamingStep, hneedsFalse, Bool.false_eq_true,
      ↓reduceIte]
    exact advanceFiniteCachedVisitPhase_unread_independent
      machine hbound remaining live .rightEnd unread hneedsFalse

/-- At or beyond the finite input length, the known `rightEnd` transition is
executed by a silent `none` microstep. -/
theorem finiteCachedVisitStreamingStep_rightEnd_none
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (hhead : n ≤ live.inputHead.val) :
    finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live) none =
      advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        .rightEnd := by
  have hanswer := finiteCachedVisitStreamingStep_answerForUnread
    machine n hbound remaining live .rightEnd (by intros; rfl)
  have hnone : streamingAnswerForUnread machine n live .rightEnd = none := by
    simp [streamingAnswerForUnread, Nat.not_lt_of_ge hhead]
  simpa [hnone] using hanswer

/-- A cached stay transition is a silent microstep and is equal to resolving
that step with any unread symbol. -/
theorem finiteCachedVisitStreamingStep_stay_none
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (state : machine.State) (cached : ReadOnlySymbol)
    (hcontrol : live.control = some (state, cached))
    (hstay : (machine.transition state cached
      (live.workSlab live.relativeWorkHead)).inputMove = .stay)
    (unread : ReadOnlySymbol) :
    finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live) none =
      advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        unread := by
  have hneeds : cachedLocalStepNeedsUnread machine live = false := by
    cases hhalt : (cachedInputMachine machine).halt live.control with
    | some outcome => simp [cachedLocalStepNeedsUnread, hhalt]
    | none =>
        rw [cachedLocalStepNeedsUnread, hhalt]
        simp [hcontrol, hstay]
  have hright : finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live) none =
      advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        .rightEnd := by
    simp [finiteCachedVisitStreamingStep, hneeds]
  exact hright.trans (advanceFiniteCachedVisitPhase_unread_independent
    machine hbound remaining live .rightEnd unread hneeds)

/-- A halted last advertised transition stutters into the retained endpoint
while consuming that last unit of visit time. -/
theorem finiteCachedVisitStreamingStep_halted_last
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (outcome : HaltOutcome)
    (hhalt : (cachedInputMachine machine).halt live.control = some outcome)
    (hlast : remaining.val = 1) :
    finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live) none =
      .completed (finiteLocalFinalStateOfReplayState base hbound live) := by
  have hneeds : cachedLocalStepNeedsUnread machine live = false := by
    simp [cachedLocalStepNeedsUnread, hhalt]
  simp [finiteCachedVisitStreamingStep, hneeds,
    advanceFiniteCachedVisitPhase, hlast,
    finiteLocalCachedFinalStep, hhalt]

/-- A halted non-final advertised transition stutters, decrements the bounded
remaining counter, and preserves the entire finite local state. -/
theorem finiteCachedVisitStreamingStep_halted_intermediate
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (outcome : HaltOutcome)
    (hhalt : (cachedInputMachine machine).halt live.control = some outcome)
    (hremaining : 1 < remaining.val) :
    finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live) none =
      .running (spendVisitStep remaining) live := by
  have hneeds : cachedLocalStepNeedsUnread machine live = false := by
    simp [cachedLocalStepNeedsUnread, hhalt]
  have hzero : remaining.val ≠ 0 := by omega
  have hlast : remaining.val ≠ 1 := by omega
  simp [finiteCachedVisitStreamingStep, hneeds,
    advanceFiniteCachedVisitPhase, hzero, hlast,
    finiteLocalCachedStep, hhalt]

/-- Embed the old finite replay result into the streaming phase result. -/
def streamingStateOfFiniteReplayResult
    {State : Type} {H w : Nat} :
    FiniteCachedVisitReplayResult State H w →
      FiniteCachedVisitStreamingState State H w
  | .completed final => .completed final
  | .emptyTrace => .rejected .zeroRemaining
  | .intermediateWorkHeadExit => .rejected .intermediateWorkHeadExit
  | .inputHorizonExceeded => .rejected .inputHorizonExceeded
  | .finalWorkHorizonExceeded => .rejected .finalWorkHorizonExceeded

/-- Adapt one per-transition unread symbol to the option consumed by the
streaming phase at its current state. -/
def streamingAnswerForPhaseUnread
    (machine : DeterministicMachine) (n : Nat)
    {H w : Nat}
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) : Option ReadOnlySymbol :=
  match phase with
  | .running _ live => streamingAnswerForUnread machine n live unread
  | _ => none

/-- Run a per-transition unread trace through the streaming adapter.  This is
a comparison semantics, not the executable fixed-order compiler: the latter
supplies only queried bits and lets silent closure perform the `none` steps. -/
def runFiniteCachedVisitStreamingWithUnreads
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) :
    List ReadOnlySymbol →
      FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State H w →
      FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State H w
  | [], phase => phase
  | unread :: rest, phase =>
      runFiniteCachedVisitStreamingWithUnreads machine n H w base hbound rest
        (finiteCachedVisitStreamingStep machine n H w base hbound phase
          (streamingAnswerForPhaseUnread machine n phase unread))

/-- One-step unfolding equation for the comparison run. -/
theorem runFiniteCachedVisitStreamingWithUnreads_cons
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1)
    (unread : ReadOnlySymbol) (rest : List ReadOnlySymbol)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w) :
    runFiniteCachedVisitStreamingWithUnreads machine n H w base hbound
        (unread :: rest) phase =
      runFiniteCachedVisitStreamingWithUnreads machine n H w base hbound rest
        (finiteCachedVisitStreamingStep machine n H w base hbound phase
          (streamingAnswerForPhaseUnread machine n phase unread)) := by
  rfl

@[simp]
theorem runFiniteCachedVisitStreamingWithUnreads_rejected
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1)
    (unreads : List ReadOnlySymbol)
    (failure : FiniteCachedVisitStreamingFailure) :
    runFiniteCachedVisitStreamingWithUnreads machine n H w base hbound
        unreads (.rejected failure) = .rejected failure := by
  induction unreads with
  | nil => rfl
  | cons unread rest ih =>
      simp [runFiniteCachedVisitStreamingWithUnreads,
        finiteCachedVisitStreamingStep, ih]

/-- Per-transition unread traces are compatible with a length-`n` input when
every genuinely unread transition at head `≥ n` carries `rightEnd`.  Cached
stay transitions impose no condition on their unused symbol. -/
def FiniteCachedVisitUnreadsRespectEnd
    (machine : DeterministicMachine) (n H w base : Nat) :
    List ReadOnlySymbol →
      LocalReplayState (cachedInputMachine machine).State H w → Prop
  | [], _ => True
  | [unread], live =>
      cachedLocalStepNeedsUnread machine live = true →
        ¬ live.inputHead.val < n → unread = .rightEnd
  | unread :: nextUnread :: rest, live =>
      (cachedLocalStepNeedsUnread machine live = true →
          ¬ live.inputHead.val < n → unread = .rightEnd) ∧
        match finiteLocalCachedStep machine H w base unread live with
        | .inside next =>
            FiniteCachedVisitUnreadsRespectEnd machine n H w base
              (nextUnread :: rest) next
        | .halted _ =>
            FiniteCachedVisitUnreadsRespectEnd machine n H w base
              (nextUnread :: rest) live
        | .workHeadExit => True
        | .inputHorizonExceeded => True

/-- Exact run-level correspondence between the streaming phase and the older
per-transition finite replay.  The bounded remaining counter must equal the
nonempty trace length. -/
theorem runFiniteCachedVisitStreamingWithUnreads_eq_replay
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (unreads : List ReadOnlySymbol)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (hnonempty : unreads ≠ [])
    (hlength : remaining.val = unreads.length)
    (hend : FiniteCachedVisitUnreadsRespectEnd machine n H w base
      unreads live) :
    runFiniteCachedVisitStreamingWithUnreads machine n H w base hbound
        unreads (.running remaining live) =
      streamingStateOfFiniteReplayResult
        (finiteCachedVisitReplay machine H w base hbound unreads live) := by
  induction unreads generalizing remaining live with
  | nil => contradiction
  | cons unread unreads ih =>
      cases unreads with
      | nil =>
          have hlast : remaining.val = 1 := by simpa using hlength
          have hstep := finiteCachedVisitStreamingStep_answerForUnread
            machine n hbound remaining live unread hend
          rw [runFiniteCachedVisitStreamingWithUnreads_cons]
          simp only [streamingAnswerForPhaseUnread]
          rw [hstep]
          cases hfinal : finiteLocalCachedFinalStep machine H w base unread
              live <;>
            simp [advanceFiniteCachedVisitPhase, hlast,
              finiteCachedVisitReplay, streamingStateOfFiniteReplayResult,
              runFiniteCachedVisitStreamingWithUnreads, hfinal]
      | cons nextUnread rest =>
          have hzero : remaining.val ≠ 0 := by
            have : 2 ≤ (unread :: nextUnread :: rest).length := by simp
            omega
          have hlast : remaining.val ≠ 1 := by
            have : 2 ≤ (unread :: nextUnread :: rest).length := by simp
            omega
          change
            (cachedLocalStepNeedsUnread machine live = true →
                ¬ live.inputHead.val < n → unread = .rightEnd) ∧
              (match finiteLocalCachedStep machine H w base unread live with
              | .inside next =>
                  FiniteCachedVisitUnreadsRespectEnd machine n H w base
                    (nextUnread :: rest) next
              | .halted _ =>
                  FiniteCachedVisitUnreadsRespectEnd machine n H w base
                    (nextUnread :: rest) live
              | .workHeadExit => True
              | .inputHorizonExceeded => True) at hend
          have hstreamStep := finiteCachedVisitStreamingStep_answerForUnread
            machine n hbound remaining live unread hend.1
          rw [finiteCachedVisitReplay_cons_cons]
          rw [runFiniteCachedVisitStreamingWithUnreads_cons]
          simp only [streamingAnswerForPhaseUnread]
          rw [hstreamStep]
          cases hinside : finiteLocalCachedStep machine H w base unread live with
          | inside next =>
              have htailEnd : FiniteCachedVisitUnreadsRespectEnd
                  machine n H w base (nextUnread :: rest) next := by
                simpa [hinside] using hend.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: rest).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              rw [show advanceFiniteCachedVisitPhase machine H w base hbound
                    remaining live unread =
                  .running (spendVisitStep remaining) next by
                unfold advanceFiniteCachedVisitPhase
                rw [dif_neg hzero, dif_neg hlast, hinside]]
              exact ih (spendVisitStep remaining) next (by simp)
                htailLength htailEnd
          | halted outcome =>
              have htailEnd : FiniteCachedVisitUnreadsRespectEnd
                  machine n H w base (nextUnread :: rest) live := by
                simpa [hinside] using hend.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: rest).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              rw [show advanceFiniteCachedVisitPhase machine H w base hbound
                    remaining live unread =
                  .running (spendVisitStep remaining) live by
                unfold advanceFiniteCachedVisitPhase
                rw [dif_neg hzero, dif_neg hlast, hinside]]
              exact ih (spendVisitStep remaining) live (by simp)
                htailLength htailEnd
          | workHeadExit =>
              simp [advanceFiniteCachedVisitPhase, hzero, hlast, hinside,
                streamingStateOfFiniteReplayResult]
          | inputHorizonExceeded =>
              simp [advanceFiniteCachedVisitPhase, hzero, hlast, hinside,
                streamingStateOfFiniteReplayResult]

/-- Reading at or beyond the finite input length yields the known terminal
symbol. -/
theorem readOnlySymbol_eq_rightEnd_of_length_le
    (input : List Bool) (head : Nat) (hhead : input.length ≤ head) :
    readOnlySymbol input head = .rightEnd := by
  simp [readOnlySymbol, hhead]

/-- Exact input agreement implies the terminal-marker side condition needed
by the streaming comparison. -/
theorem finiteCachedVisitSymbolsAgree_implies_respectEnd
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (unreads : List ReadOnlySymbol)
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (hagree : FiniteCachedVisitSymbolsAgree machine input H w base
      unreads live) :
    FiniteCachedVisitUnreadsRespectEnd machine input.length H w base
      unreads live := by
  induction unreads generalizing live with
  | nil => simp [FiniteCachedVisitSymbolsAgree] at hagree
  | cons unread unreads ih =>
      cases unreads with
      | nil =>
          simp only [FiniteCachedVisitSymbolsAgree] at hagree
          intro _ hhead
          calc
            unread = readOnlySymbol input live.inputHead.val := hagree.symm
            _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le
              input live.inputHead.val (Nat.le_of_not_gt hhead)
      | cons nextUnread rest =>
          simp only [FiniteCachedVisitSymbolsAgree] at hagree
          rcases hagree with ⟨hread, htailAgree⟩
          change
            (cachedLocalStepNeedsUnread machine live = true →
                ¬ live.inputHead.val < input.length → unread = .rightEnd) ∧
              (match finiteLocalCachedStep machine H w base unread live with
              | .inside next =>
                  FiniteCachedVisitUnreadsRespectEnd machine input.length
                    H w base (nextUnread :: rest) next
              | .halted _ =>
                  FiniteCachedVisitUnreadsRespectEnd machine input.length
                    H w base (nextUnread :: rest) live
              | .workHeadExit => True
              | .inputHorizonExceeded => True)
          constructor
          · intro _ hhead
            calc
              unread = readOnlySymbol input live.inputHead.val := hread.symm
              _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le
                input live.inputHead.val (Nat.le_of_not_gt hhead)
          · cases hstep : finiteLocalCachedStep machine H w base unread live with
            | inside next =>
                rw [hstep] at htailAgree
                simpa [hstep] using ih next htailAgree
            | halted outcome =>
                rw [hstep] at htailAgree
                simpa [hstep] using ih live htailAgree
            | workHeadExit => simp
            | inputHorizonExceeded => simp

/-- Terminal and zero-remaining states stop streaming closure. -/
def finiteCachedVisitPhaseHalted
    {State : Type} {H w : Nat}
    (phase : FiniteCachedVisitStreamingState State H w) : Bool :=
  match phase with
  | .running remaining _ => decide (remaining.val = 0)
  | .completed _ => true
  | .rejected _ => true

/-- Boolean endpoint comparison for a completed phase. -/
def finiteCachedVisitPhaseAccept
    {State : Type} [DecidableEq State] {H w : Nat}
    (expected : FixedAlphaVisitEndpoint State H)
    (phase : FiniteCachedVisitStreamingState State H w) : Bool :=
  match phase with
  | .completed final =>
      decide (expected.state = final.control) &&
        decide (expected.inputHead = final.inputHead) &&
          decide (expected.workHead = final.workHead)
  | _ => false

theorem finiteCachedVisitPhaseAccept_completed_eq_true_iff
    {State : Type} [DecidableEq State] {H w : Nat}
    (expected : FixedAlphaVisitEndpoint State H)
    (final : FiniteLocalFinalState State H w) :
    finiteCachedVisitPhaseAccept expected (.completed final) = true ↔
      expected.state = final.control ∧
        expected.inputHead = final.inputHead ∧
        expected.workHead = final.workHead := by
  simp [finiteCachedVisitPhaseAccept, Bool.and_eq_true]
  tauto

/-- Reusable finite streaming verifier for one cached visit. -/
def finiteCachedVisitStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n H w base : Nat) (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (start : LocalReplayState (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H) :
    FiniteStreamingVerifier ReadOnlySymbol where
  State := FiniteCachedVisitStreamingState
    (cachedInputMachine machine).State H w
  stateFintype := cachedFiniteVisitStreamingStateFintype machine H w
  start := .running remaining start
  halted := finiteCachedVisitPhaseHalted
  requestsInput := finiteCachedVisitPhaseRequestsInput machine n
  step := finiteCachedVisitStreamingStep machine n H w base hbound
  accept := @finiteCachedVisitPhaseAccept
    (cachedInputMachine machine).State (cachedInputStateDecidableEq machine)
    H w expected

/-- Every advertised visit duration fits `Fin (T + 1)`. -/
def fixedAlphaVisitRemaining
    {State : Type} {T : Nat} (visit : FixedAlphaBlockVisit State T) :
    Fin (T + 1) :=
  ⟨visit.steps, by
    have hexit := visit.exitTime.isLt
    unfold FixedAlphaBlockVisit.steps
    omega⟩

/-- Streaming verifier specialized to one advertised fixed-alpha visit. -/
def finiteCachedFixedAlphaVisitStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val) :
    FiniteStreamingVerifier ReadOnlySymbol :=
  finiteCachedVisitStreamingVerifier machine n T
    (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (fixedAlphaVisitRemaining visit)
    (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry)
    visit.exit

/-- Semantic correctness certificate for the streaming phase.  The
executable verifier above does not contain `input` or this unread trace; they
occur only here to compare it with the established visit semantics. -/
def FiniteCachedFixedAlphaVisitStreamingCertificate
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block)) : Prop :=
  ∃ hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val,
    ∃ final : FiniteLocalFinalState (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block),
      FiniteCachedVisitSymbolsAgree machine input T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (cachedRunUnreadSymbols machine input
            (fixedAlphaBlockVisitEntryConfiguration
              alpha block visit carried) visit.steps)
          (finiteCachedStateOfVisitEntry machine alpha block visit carried
            hentry) ∧
      runFiniteCachedVisitStreamingWithUnreads machine input.length T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          (cachedRunUnreadSymbols machine input
            (fixedAlphaBlockVisitEntryConfiguration
              alpha block visit carried) visit.steps)
          (.running (fixedAlphaVisitRemaining visit)
            (finiteCachedStateOfVisitEntry machine alpha block visit carried
              hentry)) =
        .completed final ∧
      visit.exit.state = final.control ∧
        visit.exit.inputHead = final.inputHead ∧
        visit.exit.workHead = final.workHead

/-- The streaming phase certificate is exactly the established semantic
validity predicate for one cached visit. -/
theorem finiteCachedFixedAlphaVisitStreamingCertificate_iff
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block)) :
    FiniteCachedFixedAlphaVisitStreamingCertificate machine input alpha block
        visit carried ↔
      FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried := by
  let base := advertisedBlockLower alpha.offsets block
  let width := advertisedBlockWidth alpha.offsets block
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps
  constructor
  · rintro ⟨hentry, final, hagree, hstream, hstate, hinput, hwork⟩
    let initial := finiteCachedStateOfVisitEntry
      machine alpha block visit carried hentry
    have hrespect : FiniteCachedVisitUnreadsRespectEnd machine input.length
        T width base unreads initial := by
      exact finiteCachedVisitSymbolsAgree_implies_respectEnd
        machine input unreads initial hagree
    have hlength : (fixedAlphaVisitRemaining visit).val = unreads.length := by
      simp [fixedAlphaVisitRemaining, unreads]
    have hrun := runFiniteCachedVisitStreamingWithUnreads_eq_replay
      machine input.length
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      unreads (fixedAlphaVisitRemaining visit) initial
      (by
        apply List.ne_nil_of_length_pos
        simp [unreads, FixedAlphaBlockVisit.steps_pos]) hlength hrespect
    have hmapped : streamingStateOfFiniteReplayResult
        (finiteCachedVisitReplay machine T width base
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          unreads initial) = .completed final := hrun.symm.trans hstream
    have hreplay : finiteCachedVisitReplay machine T width base
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        unreads initial = .completed final := by
      cases hresult : finiteCachedVisitReplay machine T width base
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          unreads initial with
      | completed replayFinal =>
          simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
          subst replayFinal
          rfl
      | emptyTrace =>
          simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
      | intermediateWorkHeadExit =>
          simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
      | inputHorizonExceeded =>
          simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
      | finalWorkHorizonExceeded =>
          simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
    apply (finiteCachedFixedAlphaVisitCertificate_iff
      machine input alpha block visit carried).mp
    exact ⟨hentry, final, by
      simpa [finiteCachedFixedAlphaBlockVisitReplay, initial, base, width,
        unreads] using hreplay,
      hagree, hstate, hinput, hwork⟩
  · intro hvalid
    obtain ⟨hentry, final, hreplay, hagree, hstate, hinput, hwork⟩ :=
      (finiteCachedFixedAlphaVisitCertificate_iff
        machine input alpha block visit carried).mpr hvalid
    let initial := finiteCachedStateOfVisitEntry
      machine alpha block visit carried hentry
    have hrespect : FiniteCachedVisitUnreadsRespectEnd machine input.length
        T width base unreads initial := by
      exact finiteCachedVisitSymbolsAgree_implies_respectEnd
        machine input unreads initial hagree
    have hlength : (fixedAlphaVisitRemaining visit).val = unreads.length := by
      simp [fixedAlphaVisitRemaining, unreads]
    have hrun := runFiniteCachedVisitStreamingWithUnreads_eq_replay
      machine input.length
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      unreads (fixedAlphaVisitRemaining visit) initial
      (by
        apply List.ne_nil_of_length_pos
        simp [unreads, FixedAlphaBlockVisit.steps_pos]) hlength hrespect
    have hreplay' : finiteCachedVisitReplay machine T width base
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        unreads initial = .completed final := by
      simpa [finiteCachedFixedAlphaBlockVisitReplay, initial, base, width,
        unreads] using hreplay
    rw [hreplay'] at hrun
    refine ⟨hentry, final, hagree, ?_, hstate, hinput, hwork⟩
    simpa [streamingStateOfFiniteReplayResult] using hrun

/-- Exact residual condition connecting a supplied fixed variable order to
the microstep comparison semantics.  Proving this equality from the static
timed-alpha permutation is the remaining single-visit scheduling lemma; it is
not built into the executable verifier. -/
def FixedOrderRealizesFiniteCachedVisit
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (order : List (Fin input.length)) (hlength : order.length = input.length)
    (inputBits : Fin input.length → Bool) : Prop :=
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  verifier.finishWithEndSymbol .rightEnd
      (verifier.runFixedOrder T (fun bit => .bit bit)
        (FiniteStreamingVerifier.fixedOrderFunctionOfList order hlength)
        inputBits) =
    runFiniteCachedVisitStreamingWithUnreads machine input.length T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (.running (fixedAlphaVisitRemaining visit)
        (finiteCachedStateOfVisitEntry machine alpha block visit carried
          hentry))

/-- Compile the specialized verifier in any supplied fixed input order. -/
def compileFiniteCachedFixedAlphaVisit
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (order : List (Fin n)) (hlength : order.length = n) :
    LayeredQueryProgram n n :=
  (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
    carried hentry).compileFixedOrderList T
      (fun bit => .bit bit) .rightEnd order hlength

theorem compileFiniteCachedFixedAlphaVisit_queryTrace
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (order : List (Fin n)) (hlength : order.length = n)
    (input : Fin n → Bool) :
    (compileFiniteCachedFixedAlphaVisit machine alpha block visit carried
      hentry order hlength).queryTrace input = order := by
  exact FiniteStreamingVerifier.compileFixedOrderList_queryTrace
    (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
      carried hentry) T (fun bit => .bit bit) .rightEnd
      order hlength input

theorem compileFiniteCachedFixedAlphaVisit_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (order : List (Fin n)) (hlength : order.length = n)
    (hnodup : order.Nodup) :
    (compileFiniteCachedFixedAlphaVisit machine alpha block visit carried
      hentry order hlength).IsReadOnce := by
  exact FiniteStreamingVerifier.compileFixedOrderList_isReadOnce
    (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
      carried hentry) T (fun bit => .bit bit) .rightEnd
      order hlength hnodup

@[simp]
theorem compileFiniteCachedFixedAlphaVisit_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (order : List (Fin n)) (hlength : order.length = n) :
    (compileFiniteCachedFixedAlphaVisit machine alpha block visit carried
      hentry order hlength).width =
      @Fintype.card (FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block))
        (cachedFiniteVisitStreamingStateFintype machine T
          (advertisedBlockWidth alpha.offsets block)) * (T + 1) := by
  exact FiniteStreamingVerifier.compileFixedOrderList_width
    (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
      carried hentry) T (fun bit => .bit bit) .rightEnd order hlength

/-- Conditional semantic theorem for the compiled fixed-order program.

The two explicit premises isolate the remaining scheduling bridge: the
semantic unread trace agrees with the finite replay, and the supplied static
order realizes exactly the streaming microstep run.  Under those premises the
compiled program accepts exactly the old fixed-alpha visit-validity relation.
-/
theorem compileFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_realizes
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (order : List (Fin input.length)) (hlength : order.length = input.length)
    (inputBits : Fin input.length → Bool)
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry))
    (hrealizes : FixedOrderRealizesFiniteCachedVisit machine input alpha block
      visit carried hentry order hlength inputBits) :
    (compileFiniteCachedFixedAlphaVisit machine alpha block visit carried
      hentry order hlength).eval inputBits = true ↔
      FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried := by
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  change (verifier.compileFixedOrderList T (fun bit => .bit bit) .rightEnd
      order hlength).eval inputBits = true ↔ _
  rw [FiniteStreamingVerifier.compileFixedOrderList]
  rw [verifier.compileFixedOrder_eval]
  change @finiteCachedVisitPhaseAccept (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block) visit.exit
      (verifier.finishWithEndSymbol .rightEnd
        (verifier.runFixedOrder T (fun bit => .bit bit)
          (FiniteStreamingVerifier.fixedOrderFunctionOfList order hlength)
          inputBits)) = true ↔ _
  rw [hrealizes]
  constructor
  · intro haccept
    cases hphase : runFiniteCachedVisitStreamingWithUnreads machine
        input.length T (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        (cachedRunUnreadSymbols machine input
          (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
          visit.steps)
        (.running (fixedAlphaVisitRemaining visit)
          (finiteCachedStateOfVisitEntry machine alpha block visit carried
            hentry)) with
    | running remaining live =>
        simp [finiteCachedVisitPhaseAccept, hphase] at haccept
    | rejected failure =>
        simp [finiteCachedVisitPhaseAccept, hphase] at haccept
    | completed final =>
        have hendpoint :=
          (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
            (cachedInputMachine machine).State
            (cachedInputStateDecidableEq machine) T
            (advertisedBlockWidth alpha.offsets block)
            visit.exit final).mp (by simpa [hphase] using haccept)
        apply (finiteCachedFixedAlphaVisitStreamingCertificate_iff
          machine input alpha block visit carried).mp
        exact ⟨hentry, final, hagree, hphase, hendpoint.1,
          hendpoint.2.1, hendpoint.2.2⟩
  · intro hvalid
    obtain ⟨otherEntry, final, _, hstream, hstate, hinput, hwork⟩ :=
      (finiteCachedFixedAlphaVisitStreamingCertificate_iff
        machine input alpha block visit carried).mpr hvalid
    have hproof : otherEntry = hentry := Subsingleton.elim _ _
    subst otherEntry
    rw [hstream]
    exact (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block)
      visit.exit final).2 ⟨hstate, hinput, hwork⟩

end OneTapeMagnification
end Frontier
end Pnp4
