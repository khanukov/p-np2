import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitStreamingVerifier
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaInputPermutation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Realizing one cached visit in a fixed finite input order

For a standalone visit, a permutation of the advertised fresh coordinates is
not enough.  The streaming compiler consumes the first list entry whenever the
visit first requests input.  Consequently the genuine coordinates must occur
as the chronological prefix

`[entry.inputHead, exit.inputHead) \cap [0, n)`.

Only after that prefix may the remaining coordinates be used as dummy layers.
This file records that stronger order, proves that it is a full read-once
finite-input order, and isolates the exact chronological phase equality needed
to connect the prefix to the cached replay.  The dummy suffix is then proved
semantically inert, rather than assumed to be harmless.
-/

/-- Natural-number fresh coordinates advertised by one visit, in chronology. -/
def fixedVisitNaturalFreshOrder {State : Type} {T : Nat}
    (visit : FixedAlphaBlockVisit State T) : List Nat :=
  List.range' visit.entry.inputHead.val
    (visit.exit.inputHead.val - visit.entry.inputHead.val)

/-- The genuine coordinates of a length-`n` input, kept as a fixed prefix. -/
def fixedVisitFiniteFreshOrder {State : Type} {T : Nat}
    (n : Nat) (visit : FixedAlphaBlockVisit State T) : List (Fin n) :=
  finiteInputVariableQueryOrder n (fixedVisitNaturalFreshOrder visit)

/-- Complete standalone order: chronological visit prefix, then dummy suffix. -/
def fixedVisitFiniteQueryOrder {State : Type} {T : Nat}
    (n : Nat) (visit : FixedAlphaBlockVisit State T) : List (Fin n) :=
  finiteInputQueryOrderWithDummySuffix n
    (fixedVisitNaturalFreshOrder visit)

/-- The complete order exposes the chronological part literally as a prefix. -/
theorem fixedVisitFiniteQueryOrder_eq_fresh_append_unread
    {State : Type} {T n : Nat} (visit : FixedAlphaBlockVisit State T) :
    fixedVisitFiniteQueryOrder n visit =
      fixedVisitFiniteFreshOrder n visit ++
        finiteInputUnreadSuffix n (fixedVisitNaturalFreshOrder visit) := by
  rfl

/-- A visit interval is duplicate-free, even before endpoint validity is known. -/
theorem fixedVisitNaturalFreshOrder_nodup
    {State : Type} {T : Nat} (visit : FixedAlphaBlockVisit State T) :
    (fixedVisitNaturalFreshOrder visit).Nodup := by
  exact List.nodup_range'

/-- Completing the chronological prefix yields a permutation of `Fin n`. -/
theorem fixedVisitFiniteQueryOrder_perm_finRange
    {State : Type} {T : Nat} (n : Nat)
    (visit : FixedAlphaBlockVisit State T) :
    List.Perm (fixedVisitFiniteQueryOrder n visit) (List.finRange n) := by
  exact finiteInputQueryOrderWithDummySuffix_perm_finRange_of_nodup
    n (fixedVisitNaturalFreshOrder visit)
      (fixedVisitNaturalFreshOrder_nodup visit)

/-- Hence the standalone order has exactly one layer per input coordinate. -/
@[simp]
theorem fixedVisitFiniteQueryOrder_length
    {State : Type} {T : Nat} (n : Nat)
    (visit : FixedAlphaBlockVisit State T) :
    (fixedVisitFiniteQueryOrder n visit).length = n := by
  have hperm := fixedVisitFiniteQueryOrder_perm_finRange n visit
  simpa using hperm.length_eq

/-- The standalone order is read-once. -/
theorem fixedVisitFiniteQueryOrder_nodup
    {State : Type} {T : Nat} (n : Nat)
    (visit : FixedAlphaBlockVisit State T) :
    (fixedVisitFiniteQueryOrder n visit).Nodup := by
  exact (fixedVisitFiniteQueryOrder_perm_finRange n visit).symm.nodup
    (List.nodup_finRange n)

/-- The visit prefix is exactly the fresh-query list of its crossing segment. -/
theorem fixedVisitNaturalFreshOrder_eq_crossingSegment_freshQueries
    {State : Type} {T b : Nat}
    (scheduled : TimedAlphaScheduledVisit State T b)
    (hmonotone : TimedAlphaScheduledVisitInputMonotone scheduled) :
    fixedVisitNaturalFreshOrder scheduled.visit =
      (timedAlphaScheduledVisitCrossingSegment scheduled hmonotone).freshQueries := by
  rfl

namespace FiniteStreamingVerifier

variable {Symbol : Type}

/-- Silent closure does nothing to a halted verifier state. -/
theorem silentClosureCore_eq_self_of_halted
    (verifier : FiniteStreamingVerifier Symbol) (fuel : Nat)
    (state : verifier.State) (hhalted : verifier.halted state = true) :
    verifier.silentClosureCore fuel state = (state, fuel) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [silentClosureCore, hhalted]

/-- Fixed-horizon silent closure also preserves every halted fueled state. -/
theorem silentClosure_eq_self_of_halted
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (state : verifier.FueledState H)
    (hhalted : verifier.halted state.1 = true) :
    verifier.silentClosure state = state := by
  rcases state with ⟨state, remaining⟩
  simp [silentClosure,
    verifier.silentClosureCore_eq_self_of_halted remaining.val state hhalted]

/-- Every branching-program layer is a dummy after the verifier halts. -/
theorem consumeQuery_eq_self_of_halted
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (encode : Bool -> Symbol) (state : verifier.FueledState H)
    (answer : Bool) (hhalted : verifier.halted state.1 = true) :
    verifier.consumeQuery encode state answer = state := by
  rw [consumeQuery, verifier.silentClosure_eq_self_of_halted state hhalted]
  simp [hhalted]

/-- An arbitrary suffix of query answers is inert after halting. -/
theorem foldl_consumeQuery_eq_self_of_halted
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (encode : Bool -> Symbol) (answers : List Bool)
    (state : verifier.FueledState H)
    (hhalted : verifier.halted state.1 = true) :
    answers.foldl (verifier.consumeQuery encode) state = state := by
  induction answers generalizing state with
  | nil => rfl
  | cons answer rest ih =>
      rw [List.foldl_cons,
        verifier.consumeQuery_eq_self_of_halted encode state answer hhalted]
      exact ih state hhalted

/-- Terminal end-symbol closure is inert after halting as well. -/
theorem terminalClosureCore_eq_self_of_halted
    (verifier : FiniteStreamingVerifier Symbol) (endSymbol : Symbol)
    (fuel : Nat) (state : verifier.State)
    (hhalted : verifier.halted state = true) :
    verifier.terminalClosureCore endSymbol fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [terminalClosureCore, hhalted]

/-- Finishing a halted fueled state returns precisely its verifier state. -/
theorem finishWithEndSymbol_eq_of_halted
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (endSymbol : Symbol) (state : verifier.FueledState H)
    (hhalted : verifier.halted state.1 = true) :
    verifier.finishWithEndSymbol endSymbol state = state.1 := by
  exact verifier.terminalClosureCore_eq_self_of_halted endSymbol
    state.2.val state.1 hhalted

/-- If silent closure reaches a halted state, terminal closure reaches the
same state.  This covers a visit whose final fresh coordinate is the last
finite input coordinate, so that there is no dummy layer available to trigger
the trailing silent steps. -/
theorem terminalClosureCore_eq_of_silentClosureCore_eq_halted
    (verifier : FiniteStreamingVerifier Symbol) (endSymbol : Symbol)
    (fuel : Nat) (state target : verifier.State) (remaining : Nat)
    (hclosed : verifier.silentClosureCore fuel state = (target, remaining))
    (hhalted : verifier.halted target = true) :
    verifier.terminalClosureCore endSymbol fuel state = target := by
  induction fuel generalizing state remaining with
  | zero =>
      simp only [silentClosureCore] at hclosed
      cases hclosed
      rfl
  | succ fuel ih =>
      by_cases hstop :
          (verifier.halted state || verifier.requestsInput state) = true
      · rw [silentClosureCore, if_pos hstop] at hclosed
        have hstate : state = target := congrArg Prod.fst hclosed
        subst state
        simp [terminalClosureCore, hhalted]
      · rw [silentClosureCore, if_neg hstop] at hclosed
        have hhaltedState : verifier.halted state = false := by
          cases h : verifier.halted state <;> simp_all
        have hrequestState : verifier.requestsInput state = false := by
          cases h : verifier.requestsInput state <;> simp_all
        rw [terminalClosureCore, if_neg (by simpa using hhaltedState)]
        simp only [hrequestState, Bool.false_eq_true, if_false]
        exact ih (verifier.step state none) remaining hclosed

/-- Fueled form of the preceding silent/terminal-closure compatibility. -/
theorem finishWithEndSymbol_eq_of_silentClosure_phase_eq_of_halted
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (endSymbol : Symbol) (state : verifier.FueledState H)
    (target : verifier.State)
    (hphase : (verifier.silentClosure state).1 = target)
    (hhalted : verifier.halted target = true) :
    verifier.finishWithEndSymbol endSymbol state = target := by
  rcases state with ⟨state, fuel⟩
  unfold silentClosure at hphase
  dsimp only at hphase
  generalize hcore : verifier.silentClosureCore fuel.val state = closed at hphase
  rcases closed with ⟨closedState, remaining⟩
  dsimp only at hphase
  subst closedState
  exact verifier.terminalClosureCore_eq_of_silentClosureCore_eq_halted
    endSymbol fuel.val state target remaining hcore hhalted

/-- When closure itself is halted, the current query answer is a dummy. -/
theorem consumeQuery_eq_silentClosure_of_halted
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (encode : Bool -> Symbol) (state : verifier.FueledState H)
    (answer : Bool)
    (hhalted : verifier.halted (verifier.silentClosure state).1 = true) :
    verifier.consumeQuery encode state answer = verifier.silentClosure state := by
  unfold consumeQuery
  simp [hhalted]

/-- List-facing execution is the fold of the answers in that list order. -/
theorem runFixedOrder_fixedOrderFunctionOfList
    (verifier : FiniteStreamingVerifier Symbol) (H : Nat)
    (encode : Bool -> Symbol) {n : Nat}
    (order : List (Fin n)) (hlength : order.length = n)
    (input : Fin n -> Bool) :
    verifier.runFixedOrder H encode
        (fixedOrderFunctionOfList order hlength) input =
      (order.map input).foldl (verifier.consumeQuery encode)
        (verifier.initialFueledState H) := by
  unfold runFixedOrder
  have hanswers :
      List.ofFn (fun position =>
        input (fixedOrderFunctionOfList order hlength position)) =
        order.map input := by
    apply List.ext_getElem
    · simp [hlength]
    · intro i hleft hright
      simp [fixedOrderFunctionOfList]
  rw [hanswers]

/-- A prefix whose silent closure reaches a halted target makes every following
order entry dummy.  If the suffix is empty, terminal closure performs those
same trailing silent steps. -/
theorem finish_runFixedOrderList_eq_of_prefix_closure_eq_of_halted
    (verifier : FiniteStreamingVerifier Symbol) (H : Nat)
    (encode : Bool -> Symbol) (endSymbol : Symbol) {n : Nat}
    (freshPrefix dummySuffix order : List (Fin n))
    (hlength : order.length = n) (input : Fin n -> Bool)
    (target : verifier.State)
    (horder : order = freshPrefix ++ dummySuffix)
    (hphase :
      (verifier.silentClosure
        ((freshPrefix.map input).foldl (verifier.consumeQuery encode)
          (verifier.initialFueledState H))).1 = target)
    (hhalted : verifier.halted target = true) :
    verifier.finishWithEndSymbol endSymbol
        (verifier.runFixedOrder H encode
          (fixedOrderFunctionOfList order hlength) input) = target := by
  rw [verifier.runFixedOrder_fixedOrderFunctionOfList]
  rw [horder, List.map_append, List.foldl_append]
  cases dummySuffix with
  | nil =>
      exact verifier.finishWithEndSymbol_eq_of_silentClosure_phase_eq_of_halted
        endSymbol _ target hphase hhalted
  | cons answer rest =>
      rw [List.map_cons, List.foldl_cons]
      rw [verifier.consumeQuery_eq_silentClosure_of_halted encode _
        (input answer) (by simpa [hphase] using hhalted)]
      generalize hclosed :
          verifier.silentClosure
            ((freshPrefix.map input).foldl (verifier.consumeQuery encode)
              (verifier.initialFueledState H)) = closed
      rcases closed with ⟨phase, remaining⟩
      have hphase' : phase = target := by
        rw [hclosed] at hphase
        exact hphase
      subst phase
      rw [verifier.foldl_consumeQuery_eq_self_of_halted encode
        (rest.map input) (target, remaining) hhalted]
      exact verifier.finishWithEndSymbol_eq_of_halted endSymbol
        (target, remaining) hhalted

end FiniteStreamingVerifier

/-- The exact still-local obligation for the chronological standalone prefix.

Unlike `FixedOrderRealizesFiniteCachedVisit`, this proposition contains no
permutation or dummy suffix.  It says only that consuming the advertised
fresh interval and then taking its input-free silent closure reaches the
chronological comparison phase.  The post-prefix closure is essential: the
visit may contain stay transitions after its final fresh read.  All
order-level reasoning is discharged by the theorem below.
-/
def FixedVisitFreshPrefixClosesToComparison
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
    (inputBits : Fin input.length -> Bool) : Prop :=
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  let target := runFiniteCachedVisitStreamingWithUnreads machine
    input.length T (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (cachedRunUnreadSymbols machine input
      (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
      visit.steps)
    (.running (fixedAlphaVisitRemaining visit)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry))
  (verifier.silentClosure
    (((fixedVisitFiniteFreshOrder input.length visit).map inputBits).foldl
      (verifier.consumeQuery (fun bit => .bit bit))
      (verifier.initialFueledState T))).1 = target

/-- The symbol actually resolved by the finite streaming phase.  A genuine
in-range request keeps the supplied unread symbol; a cached stay or a request
at/after the finite endpoint is resolved by the known right-end symbol. -/
def finiteCachedVisitClampedUnread
    (machine : DeterministicMachine) (n : Nat) {H w : Nat}
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) : ReadOnlySymbol :=
  if cachedLocalStepNeedsUnread machine live &&
      decide (live.inputHead.val < n) then unread else .rightEnd

/-- The comparison adapter always performs one resolved phase step; no
semantic symbol-agreement premise is needed for this structural fact. -/
theorem finiteCachedVisitStreamingStep_answerForUnread_eq_clamped
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) :
    finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live)
        (streamingAnswerForUnread machine n live unread) =
      advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        (finiteCachedVisitClampedUnread machine n live unread) := by
  by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
  · by_cases hhead : live.inputHead.val < n
    · simp [streamingAnswerForUnread, finiteCachedVisitClampedUnread,
        finiteCachedVisitStreamingStep, hneeds, hhead]
    · simp [streamingAnswerForUnread, finiteCachedVisitClampedUnread,
        finiteCachedVisitStreamingStep, hneeds, hhead]
  · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
      cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
    simp [streamingAnswerForUnread, finiteCachedVisitClampedUnread,
      finiteCachedVisitStreamingStep, hneedsFalse]

/-- Spending the last advertised transition always leaves a terminal phase,
irrespective of whether the local final step succeeds or rejects. -/
theorem finiteCachedVisitPhaseHalted_advance_of_remaining_eq_one
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) (hone : remaining.val = 1) :
    finiteCachedVisitPhaseHalted
      (advanceFiniteCachedVisitPhase machine H w base hbound remaining live
        unread) = true := by
  unfold advanceFiniteCachedVisitPhase
  rw [dif_neg (by omega), dif_pos hone]
  cases finiteLocalCachedFinalStep machine H w base unread live <;> rfl

/-- A comparison run with exactly as many symbols as the positive phase
counter is terminal.  This is purely structural: invalid local geometry may
reject, but cannot leave a live phase or make the dummy suffix relevant. -/
theorem runFiniteCachedVisitStreamingWithUnreads_halted_of_length
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w <= H + 1)
    (unreads : List ReadOnlySymbol)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (hnonempty : unreads ≠ [])
    (hlength : remaining.val = unreads.length) :
    finiteCachedVisitPhaseHalted
      (runFiniteCachedVisitStreamingWithUnreads machine n H w base hbound
        unreads (.running remaining live)) = true := by
  induction unreads generalizing remaining live with
  | nil => contradiction
  | cons unread rest ih =>
      rw [runFiniteCachedVisitStreamingWithUnreads_cons]
      simp only [streamingAnswerForPhaseUnread]
      rw [finiteCachedVisitStreamingStep_answerForUnread_eq_clamped]
      cases rest with
      | nil =>
          simp only [runFiniteCachedVisitStreamingWithUnreads]
          apply finiteCachedVisitPhaseHalted_advance_of_remaining_eq_one
            machine hbound
          simpa using hlength
      | cons nextUnread tail =>
          have hzero : remaining.val ≠ 0 := by
            have : 2 <= (unread :: nextUnread :: tail).length := by simp
            omega
          have hone : remaining.val ≠ 1 := by
            have : 2 <= (unread :: nextUnread :: tail).length := by simp
            omega
          unfold advanceFiniteCachedVisitPhase
          rw [dif_neg hzero, dif_neg hone]
          cases hstep : finiteLocalCachedStep machine H w base
              (finiteCachedVisitClampedUnread machine n live unread) live with
          | inside next =>
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              exact ih (spendVisitStep remaining) next (by simp)
                htailLength
          | halted outcome =>
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              exact ih (spendVisitStep remaining) live (by simp)
                htailLength
          | workHeadExit =>
              simp [runFiniteCachedVisitStreamingWithUnreads_rejected,
                finiteCachedVisitPhaseHalted]
          | inputHorizonExceeded =>
              simp [runFiniteCachedVisitStreamingWithUnreads_rejected,
                finiteCachedVisitPhaseHalted]

/-- The cached visit comparison target is terminal unconditionally.  The
trace length is definitionally the advertised positive visit duration. -/
theorem finiteCachedVisitComparisonTarget_halted
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
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
    finiteCachedVisitPhaseHalted
      (runFiniteCachedVisitStreamingWithUnreads machine input.length T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        (cachedRunUnreadSymbols machine input
          (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
          visit.steps)
        (.running (fixedAlphaVisitRemaining visit)
          (finiteCachedStateOfVisitEntry machine alpha block visit carried
            hentry))) = true := by
  apply runFiniteCachedVisitStreamingWithUnreads_halted_of_length
    machine input.length
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
  · apply List.ne_nil_of_length_pos
    simp [FixedAlphaBlockVisit.steps_pos]
  · simp [fixedAlphaVisitRemaining]

/-- The canonical chronological-prefix order discharges the old residual
order relation once the genuinely local prefix/replay synchronization is
known.  No additional suffix or permutation hypothesis remains. -/
theorem fixedVisitFiniteQueryOrder_realizes_of_prefix_closes
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
    (inputBits : Fin input.length -> Bool)
    (hprefix : FixedVisitFreshPrefixClosesToComparison machine input alpha
      block visit carried hentry inputBits) :
    FixedOrderRealizesFiniteCachedVisit machine input alpha block visit
      carried hentry (fixedVisitFiniteQueryOrder input.length visit)
      (fixedVisitFiniteQueryOrder_length input.length visit) inputBits := by
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  let target := runFiniteCachedVisitStreamingWithUnreads machine
    input.length T (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (cachedRunUnreadSymbols machine input
      (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
      visit.steps)
    (.running (fixedAlphaVisitRemaining visit)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry))
  have hhalted : verifier.halted target = true := by
    exact finiteCachedVisitComparisonTarget_halted machine input
      alpha block visit carried hentry
  have hphase :
      (verifier.silentClosure
        (((fixedVisitFiniteFreshOrder input.length visit).map inputBits).foldl
          (verifier.consumeQuery (fun bit => .bit bit))
          (verifier.initialFueledState T))).1 = target := by
    exact hprefix
  unfold FixedOrderRealizesFiniteCachedVisit
  change verifier.finishWithEndSymbol .rightEnd
      (verifier.runFixedOrder T (fun bit => .bit bit)
        (FiniteStreamingVerifier.fixedOrderFunctionOfList
          (fixedVisitFiniteQueryOrder input.length visit)
          (fixedVisitFiniteQueryOrder_length input.length visit)) inputBits) =
    target
  apply verifier.finish_runFixedOrderList_eq_of_prefix_closure_eq_of_halted
    T (fun bit => .bit bit) .rightEnd
    (fixedVisitFiniteFreshOrder input.length visit)
    (finiteInputUnreadSuffix input.length
      (fixedVisitNaturalFreshOrder visit))
    (fixedVisitFiniteQueryOrder input.length visit)
    (fixedVisitFiniteQueryOrder_length input.length visit)
    inputBits target
  · exact fixedVisitFiniteQueryOrder_eq_fresh_append_unread visit
  · exact hphase
  · exact hhalted

/-- Semantic visit validity automatically supplies the symbol-agreement
certificate for the particular entry proof used by the compiler.  Thus
symbol agreement is not an additional premise in the canonical-input
completeness corollary below. -/
theorem finiteCachedVisitSymbolsAgree_of_fixedAlphaBlockVisitValid
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
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
    (hvalid : FixedAlphaBlockVisitValid (cachedInputMachine machine) input
      alpha block visit carried) :
    FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry) := by
  obtain ⟨otherEntry, _final, hagree, _⟩ :=
    (finiteCachedFixedAlphaVisitStreamingCertificate_iff
      machine input alpha block visit carried).mpr hvalid
  have hentryProof : otherEntry = hentry := Subsingleton.elim _ _
  subst otherEntry
  exact hagree

/-- Canonical input bits and the canonical standalone order compile every
valid visit to acceptance once the corrected local prefix-closure lemma is
available.  The only non-validity premise left here is
`FixedVisitFreshPrefixClosesToComparison`; `FiniteCachedVisitSymbolsAgree`,
order length, read-once order, terminality, and suffix inertness are all
discharged internally. -/
theorem compileFixedVisitFiniteQueryOrder_eval_eq_true_of_valid_of_prefix_closes
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
    (hvalid : FixedAlphaBlockVisitValid (cachedInputMachine machine) input
      alpha block visit carried)
    (hprefix : FixedVisitFreshPrefixClosesToComparison machine input alpha
      block visit carried hentry (fun position => input.get position)) :
    (compileFiniteCachedFixedAlphaVisit machine alpha block visit carried
      hentry (fixedVisitFiniteQueryOrder input.length visit)
      (fixedVisitFiniteQueryOrder_length input.length visit)).eval
        (fun position => input.get position) = true := by
  let inputBits : Fin input.length -> Bool := fun position => input.get position
  have hagree :=
    finiteCachedVisitSymbolsAgree_of_fixedAlphaBlockVisitValid
      machine input alpha block visit carried hentry hvalid
  have hrealizes : FixedOrderRealizesFiniteCachedVisit machine input alpha
      block visit carried hentry
      (fixedVisitFiniteQueryOrder input.length visit)
      (fixedVisitFiniteQueryOrder_length input.length visit) inputBits := by
    exact fixedVisitFiniteQueryOrder_realizes_of_prefix_closes machine input
      alpha block visit carried hentry inputBits hprefix
  exact (compileFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_realizes
    machine input alpha block visit carried hentry
    (fixedVisitFiniteQueryOrder input.length visit)
    (fixedVisitFiniteQueryOrder_length input.length visit) inputBits
    hagree hrealizes).2 hvalid

end OneTapeMagnification
end Frontier
end Pnp4
