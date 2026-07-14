import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedVisitReadOnce

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Semantic correctness of the adaptive cached-visit compiler

This file connects the executable state-dependent query schedule to the
established finite streaming certificate for one cached fixed-alpha visit.
-/

/-- Exact run-level bridge between the adaptive executable and the established
per-transition comparison semantics. -/
def AdaptiveOrderRealizesFiniteCachedVisit
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
    (inputBits : Fin input.length → Bool) : Prop :=
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive T (fun bit => .bit bit)
        (finiteCachedVisitAdaptiveQueryIndex? machine input.length) inputBits) =
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

/-- Once the exact run-level bridge and symbol agreement are available, the
adaptive program accepts exactly the established one-visit semantics. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_realizes
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
    (inputBits : Fin input.length → Bool)
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry))
    (hrealizes : AdaptiveOrderRealizesFiniteCachedVisit machine input alpha
      block visit carried hentry inputBits) :
    (compileAdaptiveFiniteCachedFixedAlphaVisit machine alpha block visit
      carried hentry).eval inputBits = true ↔
      FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried := by
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  change (verifier.compileAdaptive T input.length (fun bit => .bit bit)
      .rightEnd (finiteCachedVisitAdaptiveQueryIndex? machine input.length)).eval
        inputBits = true ↔ _
  rw [FiniteStreamingVerifier.compileAdaptive_eval]
  change @finiteCachedVisitPhaseAccept (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block) visit.exit
      (verifier.finishWithEndSymbol .rightEnd
        (verifier.runAdaptive T (fun bit => .bit bit)
          (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
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

namespace FiniteStreamingVerifier

/-- Ordinary one-microstep-at-a-time execution driven by the same state
selector and Boolean input as the adaptive compiler. -/
def inputDrivenCore {Symbol : Type}
    (verifier : FiniteStreamingVerifier Symbol) {n : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) : Nat → verifier.State → verifier.State
  | 0, state => state
  | fuel + 1, state =>
      if verifier.halted state then
        state
      else
        verifier.inputDrivenCore encode queryIndex? input fuel
          (verifier.step state
            (if verifier.requestsInput state then
              (queryIndex? state).map (fun index => encode (input index))
            else none))

/-- Silent closure is an exact compression of the leading input-free part of
the ordinary input-driven execution. -/
theorem inputDrivenCore_eq_after_silentClosureCore
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (fuel : Nat) (state : verifier.State) :
    verifier.inputDrivenCore encode queryIndex? input fuel state =
      verifier.inputDrivenCore encode queryIndex? input
        (verifier.silentClosureCore fuel state).2
        (verifier.silentClosureCore fuel state).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [silentClosureCore]
      by_cases hstop :
          (verifier.halted state || verifier.requestsInput state) = true
      · rw [if_pos hstop]
      · rw [if_neg hstop]
        have hhalt : verifier.halted state = false := by
          cases h : verifier.halted state <;> simp_all
        have hrequest : verifier.requestsInput state = false := by
          cases h : verifier.requestsInput state <;> simp_all
        simp only [inputDrivenCore, hhalt, Bool.false_eq_true,
          ↓reduceIte, hrequest]
        exact ih (verifier.step state none)

/-- Fueled-state form of exact silent-prefix compression. -/
theorem inputDrivenCore_eq_after_silentClosure
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n H : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (state : verifier.FueledState H) :
    verifier.inputDrivenCore encode queryIndex? input state.2.val state.1 =
      verifier.inputDrivenCore encode queryIndex? input
        (verifier.silentClosure state).2.val
        (verifier.silentClosure state).1 := by
  exact verifier.inputDrivenCore_eq_after_silentClosureCore encode queryIndex?
    input state.2.val state.1

/-- The recursively defined adaptive iteration may equivalently execute its
first layer first. -/
theorem runAdaptiveFrom_succ_front
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n H : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (layers : Nat)
    (state : verifier.FueledState H) :
    verifier.runAdaptiveFrom encode queryIndex? input (layers + 1) state =
      verifier.runAdaptiveFrom encode queryIndex? input layers
        (verifier.adaptiveInputStep encode queryIndex? input state) := by
  induction layers generalizing state with
  | zero => rfl
  | succ layers ih =>
      simp only [runAdaptiveFrom]
      exact congrArg
        (verifier.adaptiveInputStep encode queryIndex? input) (ih state)

/-- A halted state is fixed by every adaptive layer. -/
theorem adaptiveInputStep_eq_self_of_halted
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n H : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (state : verifier.FueledState H)
    (hhalt : verifier.halted state.1 = true) :
    verifier.adaptiveInputStep encode queryIndex? input state = state := by
  have hclosed := verifier.silentClosure_eq_self_of_halted state hhalt
  simp [adaptiveInputStep, adaptiveNext, adaptiveQuery?, hclosed, hhalt]

/-- Any number of adaptive layers fixes a halted state. -/
theorem runAdaptiveFrom_eq_self_of_halted
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n H : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (layers : Nat)
    (state : verifier.FueledState H)
    (hhalt : verifier.halted state.1 = true) :
    verifier.runAdaptiveFrom encode queryIndex? input layers state = state := by
  induction layers with
  | zero => rfl
  | succ layers ih =>
      simp only [runAdaptiveFrom, ih]
      exact verifier.adaptiveInputStep_eq_self_of_halted encode queryIndex?
        input state hhalt

/-- Ordinary input-driven execution also fixes a halted state. -/
theorem inputDrivenCore_eq_self_of_halted
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (fuel : Nat) (state : verifier.State)
    (hhalt : verifier.halted state = true) :
    verifier.inputDrivenCore encode queryIndex? input fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [inputDrivenCore, hhalt]

/-- One ordinary driven microstep may be taken before the remaining fuel. -/
theorem inputDrivenCore_succ_front
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (fuel : Nat) (state : verifier.State) :
    verifier.inputDrivenCore encode queryIndex? input (fuel + 1) state =
      verifier.inputDrivenCore encode queryIndex? input fuel
        (verifier.inputDrivenCore encode queryIndex? input 1 state) := by
  by_cases hhalt : verifier.halted state = true
  · rw [verifier.inputDrivenCore_eq_self_of_halted encode queryIndex? input
      (fuel + 1) state hhalt]
    rw [verifier.inputDrivenCore_eq_self_of_halted encode queryIndex? input
      1 state hhalt]
    rw [verifier.inputDrivenCore_eq_self_of_halted encode queryIndex? input
      fuel state hhalt]
  · have hhaltFalse : verifier.halted state = false := by
      cases h : verifier.halted state <;> simp_all
    simp [inputDrivenCore, hhaltFalse]

/-- Splitting the microstep fuel splits ordinary driven execution. -/
theorem inputDrivenCore_add
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (firstCount secondCount : Nat)
    (state : verifier.State) :
    verifier.inputDrivenCore encode queryIndex? input
        (firstCount + secondCount) state =
      verifier.inputDrivenCore encode queryIndex? input secondCount
        (verifier.inputDrivenCore encode queryIndex? input firstCount
          state) := by
  induction firstCount generalizing state with
  | zero => simp [inputDrivenCore]
  | succ firstCount ih =>
      rw [Nat.succ_add]
      rw [verifier.inputDrivenCore_succ_front encode queryIndex? input]
      rw [ih]
      rw [← verifier.inputDrivenCore_succ_front encode queryIndex? input]

/-- Zero fuel makes an adaptive layer inert. -/
theorem adaptiveInputStep_eq_self_of_fuel_zero
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n H : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (state : verifier.FueledState H)
    (hzero : state.2.val = 0) :
    verifier.adaptiveInputStep encode queryIndex? input state = state := by
  rcases state with ⟨phase, ⟨fuel, hfuel⟩⟩
  simp only at hzero
  subst fuel
  simp [adaptiveInputStep, adaptiveNext, adaptiveQuery?, silentClosure,
    silentClosureCore]

/-- Any number of adaptive layers is inert at zero fuel. -/
theorem runAdaptiveFrom_eq_self_of_fuel_zero
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n H : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (layers : Nat)
    (state : verifier.FueledState H)
    (hzero : state.2.val = 0) :
    verifier.runAdaptiveFrom encode queryIndex? input layers state = state := by
  induction layers with
  | zero => rfl
  | succ layers ih =>
      simp only [runAdaptiveFrom, ih]
      exact verifier.adaptiveInputStep_eq_self_of_fuel_zero encode queryIndex?
        input state hzero

/-- If the selector is total whenever the verifier requests input, enough
adaptive layers exactly implement the ordinary input-driven microstep run. -/
theorem runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol) {n H : Nat}
    (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool)
    (htotal : ∀ state, verifier.requestsInput state = true →
      ∃ index, queryIndex? state = some index)
    (state : verifier.FueledState H) (layers : Nat)
    (hle : state.2.val ≤ layers) :
    (verifier.runAdaptiveFrom encode queryIndex? input layers state).1 =
      verifier.inputDrivenCore encode queryIndex? input state.2.val state.1 := by
  have go : ∀ fuel : Nat, ∀ (current : verifier.FueledState H)
      (available : Nat), current.2.val = fuel → fuel ≤ available →
      (verifier.runAdaptiveFrom encode queryIndex? input available current).1 =
        verifier.inputDrivenCore encode queryIndex? input fuel current.1 := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
        intro current available hfuel havailable
        by_cases hzeroFuel : fuel = 0
        · have hzeroCurrent : current.2.val = 0 := hfuel.trans hzeroFuel
          rw [verifier.runAdaptiveFrom_eq_self_of_fuel_zero encode queryIndex?
            input available current hzeroCurrent]
          rw [hzeroFuel]
          rfl
        · cases available with
          | zero => omega
          | succ rest =>
              rw [verifier.runAdaptiveFrom_succ_front]
              let closed := verifier.silentClosure current
              have hclosedLe : closed.2.val ≤ fuel := by
                have hremaining := verifier.silentClosureCore_remaining_le
                  current.2.val current.1
                simpa [closed, silentClosure, hfuel] using hremaining
              have hdrive :
                  verifier.inputDrivenCore encode queryIndex? input fuel
                      current.1 =
                    verifier.inputDrivenCore encode queryIndex? input
                      closed.2.val closed.1 := by
                simpa [closed, hfuel] using
                  verifier.inputDrivenCore_eq_after_silentClosure encode
                    queryIndex? input current
              have hstopped := verifier.silentClosure_stopped current
              by_cases hclosedZero : closed.2.val = 0
              · have hquery : verifier.adaptiveQuery? queryIndex? current =
                    none := by
                  simp [adaptiveQuery?, closed, hclosedZero]
                have hadaptive : verifier.adaptiveInputStep encode queryIndex?
                    input current = closed := by
                  simp [adaptiveInputStep, adaptiveNext, hquery, closed]
                have hrecursive := ih 0 (by omega) closed rest hclosedZero
                  (by omega)
                rw [hadaptive]
                calc
                  (verifier.runAdaptiveFrom encode queryIndex? input rest
                      closed).1 =
                      verifier.inputDrivenCore encode queryIndex? input 0
                        closed.1 := hrecursive
                  _ = verifier.inputDrivenCore encode queryIndex? input
                      closed.2.val closed.1 := by rw [hclosedZero]
                  _ = verifier.inputDrivenCore encode queryIndex? input fuel
                      current.1 := hdrive.symm
              · by_cases hclosedHalted : verifier.halted closed.1 = true
                · have hquery : verifier.adaptiveQuery? queryIndex? current =
                      none := by
                    simp [adaptiveQuery?, closed, hclosedHalted]
                  have hadaptive : verifier.adaptiveInputStep encode queryIndex?
                      input current = closed := by
                    simp [adaptiveInputStep, adaptiveNext, hquery, closed]
                  rw [hadaptive]
                  rw [verifier.runAdaptiveFrom_eq_self_of_halted encode
                    queryIndex? input rest closed hclosedHalted]
                  calc
                    closed.1 = verifier.inputDrivenCore encode queryIndex?
                        input closed.2.val closed.1 :=
                      (verifier.inputDrivenCore_eq_self_of_halted encode
                        queryIndex? input closed.2.val closed.1
                        hclosedHalted).symm
                    _ = verifier.inputDrivenCore encode queryIndex? input fuel
                        current.1 := hdrive.symm
                · have hhaltFalse : verifier.halted closed.1 = false := by
                    cases h : verifier.halted closed.1 <;> simp_all
                  have hrequest : verifier.requestsInput closed.1 = true := by
                    rcases hstopped with hzero | hhalt | hrequest
                    · exact (hclosedZero hzero).elim
                    · exact (hclosedHalted hhalt).elim
                    · exact hrequest
                  obtain ⟨index, hselector⟩ := htotal closed.1 hrequest
                  have hquery : verifier.adaptiveQuery? queryIndex? current =
                      some index :=
                    (verifier.adaptiveQuery?_eq_some_iff queryIndex? current
                      index).2 ⟨Nat.pos_of_ne_zero hclosedZero, hhaltFalse,
                        hrequest, hselector⟩
                  let next : verifier.FueledState H :=
                    (verifier.step closed.1
                        (some (encode (input index))),
                      FiniteStreamingVerifier.spendOne closed.2)
                  have hadaptive : verifier.adaptiveInputStep encode queryIndex?
                      input current = next := by
                    simp [adaptiveInputStep, adaptiveNext, hquery, closed, next]
                  have hnextFuel : next.2.val = closed.2.val - 1 := rfl
                  have hnextLt : next.2.val < fuel := by
                    rw [hnextFuel]
                    omega
                  have hnextLe : next.2.val ≤ rest := by
                    rw [hnextFuel]
                    omega
                  have hrecursive := ih next.2.val hnextLt next rest rfl hnextLe
                  have hdriveStep :
                      verifier.inputDrivenCore encode queryIndex? input
                          closed.2.val closed.1 =
                        verifier.inputDrivenCore encode queryIndex? input
                          next.2.val next.1 := by
                    cases hclosedFuel : closed.2.val with
                    | zero => exact (hclosedZero hclosedFuel).elim
                    | succ closedFuel =>
                        simp [inputDrivenCore, hclosedFuel, hhaltFalse,
                          hrequest, hselector, next,
                          FiniteStreamingVerifier.spendOne]
                  rw [hadaptive]
                  calc
                    (verifier.runAdaptiveFrom encode queryIndex? input rest
                        next).1 =
                        verifier.inputDrivenCore encode queryIndex? input
                          next.2.val next.1 := hrecursive
                    _ = verifier.inputDrivenCore encode queryIndex? input
                        closed.2.val closed.1 := hdriveStep.symm
                    _ = verifier.inputDrivenCore encode queryIndex? input fuel
                        current.1 := hdrive.symm
  exact go state.2.val state layers rfl hle

end FiniteStreamingVerifier

/-- The cached head selector is total at every state that genuinely requests
an in-range input symbol. -/
theorem finiteCachedVisitAdaptiveQueryIndex?_total_of_requestsInput
    (machine : DeterministicMachine) (n : Nat) {H w : Nat}
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w)
    (hrequest : finiteCachedVisitPhaseRequestsInput machine n phase = true) :
    ∃ index, finiteCachedVisitAdaptiveQueryIndex? machine n phase =
      some index := by
  cases phase with
  | completed final =>
      simp [finiteCachedVisitPhaseRequestsInput] at hrequest
  | rejected failure =>
      simp [finiteCachedVisitPhaseRequestsInput] at hrequest
  | running remaining live =>
      have hparts :=
        (finiteCachedVisitPhaseRequestsInput_running_eq_true_iff
          machine n remaining live).mp hrequest
      let index : Fin n := ⟨live.inputHead.val, hparts.2.2⟩
      exact ⟨index, by
        simp [finiteCachedVisitAdaptiveQueryIndex?, index, hparts.2.2]⟩

/-- At a positive running phase, the ordinary input-driven answer is exactly
the streaming adapter's answer for the actual immutable-input symbol. -/
theorem finiteCachedVisit_inputDrivenAnswer_eq_streamingAnswer
    (machine : DeterministicMachine) (input : List Bool)
    {H w : Nat} (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) (hpositive : 0 < remaining.val)
    (hread : readOnlySymbol input live.inputHead.val = unread) :
    (if finiteCachedVisitPhaseRequestsInput machine input.length
          (.running remaining live) then
        (finiteCachedVisitAdaptiveQueryIndex? machine input.length
          (.running remaining live)).map
            (fun index => .bit (input.get index))
      else none) =
      streamingAnswerForUnread machine input.length live unread := by
  by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
  · by_cases hhead : live.inputHead.val < input.length
    · let index : Fin input.length := ⟨live.inputHead.val, hhead⟩
      have hunread : unread = .bit (input.get index) := by
        calc
          unread = readOnlySymbol input live.inputHead.val := hread.symm
          _ = .bit (input.get index) := readOnlySymbol_eq_bit_get input index
      simp [finiteCachedVisitPhaseRequestsInput,
        finiteCachedVisitAdaptiveQueryIndex?, streamingAnswerForUnread,
        hpositive, hneeds, hhead, index, hunread]
    · simp [finiteCachedVisitPhaseRequestsInput,
        streamingAnswerForUnread, hpositive, hneeds, hhead]
  · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
      cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
    simp [finiteCachedVisitPhaseRequestsInput,
      streamingAnswerForUnread, hpositive, hneedsFalse]

/-- Ordinary canonical-input microstep execution of the finite cached phase,
independent of the verifier's expected endpoint and start field. -/
def runFiniteCachedVisitInputDriven
    (machine : DeterministicMachine) (input : List Bool)
    (H w base : Nat) (hbound : base + w ≤ H + 1) :
    Nat → FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w →
      FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State H w
  | 0, phase => phase
  | fuel + 1, phase =>
      if finiteCachedVisitPhaseHalted phase then
        phase
      else
        runFiniteCachedVisitInputDriven machine input H w base hbound fuel
          (finiteCachedVisitStreamingStep machine input.length H w base hbound
            phase
            (if finiteCachedVisitPhaseRequestsInput machine input.length phase
              then
                (finiteCachedVisitAdaptiveQueryIndex? machine input.length
                  phase).map (fun index => .bit (input.get index))
              else none))

/-- The generic ordinary input-driven core specializes definitionally to the
cached phase runner above. -/
theorem finiteCachedVisitStreamingVerifier_inputDrivenCore_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (H w base : Nat) (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (start : LocalReplayState (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    (fuel : Nat)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w) :
    (finiteCachedVisitStreamingVerifier machine input.length H w base hbound
      remaining start expected).inputDrivenCore (fun bit => .bit bit)
        (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) fuel phase =
      runFiniteCachedVisitInputDriven machine input H w base hbound fuel
        phase := by
  induction fuel generalizing phase with
  | zero => rfl
  | succ fuel ih =>
      simp only [FiniteStreamingVerifier.inputDrivenCore,
        runFiniteCachedVisitInputDriven]
      change
        (if finiteCachedVisitPhaseHalted phase then phase
        else
          (finiteCachedVisitStreamingVerifier machine input.length H w base
            hbound remaining start expected).inputDrivenCore
              (fun bit => .bit bit)
              (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
              (fun index => input.get index) fuel
              (finiteCachedVisitStreamingStep machine input.length H w base
                hbound phase
                (if finiteCachedVisitPhaseRequestsInput machine input.length
                    phase then
                  (finiteCachedVisitAdaptiveQueryIndex? machine input.length
                    phase).map (fun index => .bit (input.get index))
                else none))) = _
      split
      · rfl
      · exact ih _

/-- Whenever an explicit unread trace agrees with the immutable input, the
canonical input-driven phase runner equals the established streaming
comparison run on that trace. -/
theorem runFiniteCachedVisitInputDriven_eq_streaming_of_symbolsAgree
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (unreads : List ReadOnlySymbol)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (hnonempty : unreads ≠ [])
    (hlength : remaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input H w base
      unreads live) :
    runFiniteCachedVisitInputDriven machine input H w base hbound
        unreads.length (.running remaining live) =
      runFiniteCachedVisitStreamingWithUnreads machine input.length H w base
        hbound unreads (.running remaining live) := by
  induction unreads generalizing remaining live with
  | nil => contradiction
  | cons unread rest ih =>
      have hpositive : 0 < remaining.val := by
        rw [hlength]
        simp
      have hphaseNotHalted :
          finiteCachedVisitPhaseHalted (.running remaining live) = false := by
        simp [finiteCachedVisitPhaseHalted, Nat.ne_of_gt hpositive]
      have hread : readOnlySymbol input live.inputHead.val = unread := by
        cases rest with
        | nil => simpa [FiniteCachedVisitSymbolsAgree] using hagree
        | cons nextUnread tail =>
            exact (finiteCachedVisitSymbolsAgree_cons_cons machine input H w
              base unread nextUnread tail live).mp hagree |>.1
      have hanswer :=
        finiteCachedVisit_inputDrivenAnswer_eq_streamingAnswer machine input
          remaining live unread hpositive hread
      simp only [List.length_cons]
      rw [runFiniteCachedVisitInputDriven]
      simp only [hphaseNotHalted, Bool.false_eq_true, ↓reduceIte]
      rw [runFiniteCachedVisitStreamingWithUnreads_cons]
      simp only [streamingAnswerForPhaseUnread]
      rw [hanswer]
      cases rest with
      | nil =>
          rfl
      | cons nextUnread tail =>
          have hend : cachedLocalStepNeedsUnread machine live = true →
              ¬ live.inputHead.val < input.length → unread = .rightEnd := by
            intro _ hhead
            calc
              unread = readOnlySymbol input live.inputHead.val := hread.symm
              _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le input
                live.inputHead.val (Nat.le_of_not_gt hhead)
          have hstreamStep := finiteCachedVisitStreamingStep_answerForUnread
            machine input.length hbound remaining live unread hend
          rw [hstreamStep]
          have hzero : remaining.val ≠ 0 := by omega
          have hone : remaining.val ≠ 1 := by
            rw [hlength]
            simp
          cases hlocal : finiteLocalCachedStep machine H w base unread live with
          | inside next =>
              have htailAgree : FiniteCachedVisitSymbolsAgree machine input
                  H w base (nextUnread :: tail) next := by
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
                exact hagree.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal] using
                ih (spendVisitStep remaining) next (by simp) htailLength
                  htailAgree
          | halted outcome =>
              have htailAgree : FiniteCachedVisitSymbolsAgree machine input
                  H w base (nextUnread :: tail) live := by
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
                exact hagree.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal] using
                ih (spendVisitStep remaining) live (by simp) htailLength
                  htailAgree
          | workHeadExit =>
              rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
              have hfalse : False := by simpa using hagree.2
              exact hfalse.elim
          | inputHorizonExceeded =>
              rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
              have hfalse : False := by simpa using hagree.2
              exact hfalse.elim

/-- The canonical phase runner fixes every terminal phase. -/
theorem runFiniteCachedVisitInputDriven_eq_self_of_halted
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (fuel : Nat)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w)
    (hhalted : finiteCachedVisitPhaseHalted phase = true) :
    runFiniteCachedVisitInputDriven machine input H w base hbound fuel phase =
      phase := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [runFiniteCachedVisitInputDriven, hhalted]

/-- If canonical input-driven execution completes, it produces an explicit
agreeing unread trace of exactly the advertised remaining length. -/
theorem runFiniteCachedVisitInputDriven_completed_has_agreeing_trace
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (hcompleted :
      runFiniteCachedVisitInputDriven machine input H w base hbound
        remaining.val (.running remaining live) = .completed final) :
    ∃ unreads : List ReadOnlySymbol,
      unreads.length = remaining.val ∧
        FiniteCachedVisitSymbolsAgree machine input H w base unreads live ∧
        runFiniteCachedVisitStreamingWithUnreads machine input.length H w base
          hbound unreads (.running remaining live) = .completed final := by
  have go : ∀ fuel : Nat, ∀ (currentRemaining : Fin (H + 1))
      (currentLive : LocalReplayState
        (cachedInputMachine machine).State H w)
      (target : FiniteLocalFinalState
        (cachedInputMachine machine).State H w),
      currentRemaining.val = fuel →
      runFiniteCachedVisitInputDriven machine input H w base hbound fuel
          (.running currentRemaining currentLive) = .completed target →
      ∃ unreads : List ReadOnlySymbol,
        unreads.length = fuel ∧
          FiniteCachedVisitSymbolsAgree machine input H w base unreads
            currentLive ∧
          runFiniteCachedVisitStreamingWithUnreads machine input.length H w
            base hbound unreads (.running currentRemaining currentLive) =
              .completed target := by
    intro fuel
    induction fuel with
    | zero =>
        intro currentRemaining currentLive target hremaining hrun
        simp [runFiniteCachedVisitInputDriven] at hrun
    | succ fuel ih =>
        intro currentRemaining currentLive target hremaining hrun
        let unread := readOnlySymbol input currentLive.inputHead.val
        have hpositive : 0 < currentRemaining.val := by omega
        have hphaseNotHalted :
            finiteCachedVisitPhaseHalted
              (.running currentRemaining currentLive) = false := by
          simp [finiteCachedVisitPhaseHalted, Nat.ne_of_gt hpositive]
        have hanswer :=
          finiteCachedVisit_inputDrivenAnswer_eq_streamingAnswer machine input
            currentRemaining currentLive unread hpositive rfl
        simp only [runFiniteCachedVisitInputDriven, hphaseNotHalted,
          Bool.false_eq_true, ↓reduceIte] at hrun
        rw [hanswer] at hrun
        have hend : cachedLocalStepNeedsUnread machine currentLive = true →
            ¬ currentLive.inputHead.val < input.length →
              unread = .rightEnd := by
          intro _ hhead
          exact readOnlySymbol_eq_rightEnd_of_length_le input
            currentLive.inputHead.val (Nat.le_of_not_gt hhead)
        have hstreamStep := finiteCachedVisitStreamingStep_answerForUnread
          machine input.length hbound currentRemaining currentLive unread hend
        by_cases htailZero : fuel = 0
        · subst fuel
          have hnext : finiteCachedVisitStreamingStep machine input.length H w
              base hbound (.running currentRemaining currentLive)
                (streamingAnswerForUnread machine input.length currentLive
                  unread) = .completed target := by
            simpa [runFiniteCachedVisitInputDriven] using hrun
          refine ⟨[unread], by simp, ?_, ?_⟩
          · simp [FiniteCachedVisitSymbolsAgree, unread]
          · rw [runFiniteCachedVisitStreamingWithUnreads_cons]
            simp only [streamingAnswerForPhaseUnread]
            rw [hnext]
            rfl
        · have hzero : currentRemaining.val ≠ 0 := by omega
          have hone : currentRemaining.val ≠ 1 := by omega
          rw [hstreamStep] at hrun
          cases hlocal : finiteLocalCachedStep machine H w base unread
              currentLive with
          | inside next =>
              have htailRemaining : (spendVisitStep currentRemaining).val =
                  fuel := by
                simp only [spendVisitStep]
                omega
              have htailRun :
                  runFiniteCachedVisitInputDriven machine input H w base hbound
                    fuel (.running (spendVisitStep currentRemaining) next) =
                      .completed target := by
                simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
                  using hrun
              obtain ⟨tail, htailLength, htailAgree, htailStream⟩ :=
                ih (spendVisitStep currentRemaining) next target htailRemaining
                  htailRun
              refine ⟨unread :: tail, by simp [htailLength], ?_, ?_⟩
              · cases tail with
                | nil =>
                    exact (htailZero htailLength.symm).elim
                | cons nextUnread rest =>
                    rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal]
                    exact ⟨rfl, htailAgree⟩
              · rw [runFiniteCachedVisitStreamingWithUnreads_cons]
                simp only [streamingAnswerForPhaseUnread]
                rw [hstreamStep]
                simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
                  using htailStream
          | halted outcome =>
              have htailRemaining : (spendVisitStep currentRemaining).val =
                  fuel := by
                simp only [spendVisitStep]
                omega
              have htailRun :
                  runFiniteCachedVisitInputDriven machine input H w base hbound
                    fuel (.running (spendVisitStep currentRemaining)
                      currentLive) = .completed target := by
                simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
                  using hrun
              obtain ⟨tail, htailLength, htailAgree, htailStream⟩ :=
                ih (spendVisitStep currentRemaining) currentLive target
                  htailRemaining htailRun
              refine ⟨unread :: tail, by simp [htailLength], ?_, ?_⟩
              · cases tail with
                | nil =>
                    exact (htailZero htailLength.symm).elim
                | cons nextUnread rest =>
                    rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal]
                    exact ⟨rfl, htailAgree⟩
              · rw [runFiniteCachedVisitStreamingWithUnreads_cons]
                simp only [streamingAnswerForPhaseUnread]
                rw [hstreamStep]
                simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
                  using htailStream
          | workHeadExit =>
              have hrunRejected :
                  runFiniteCachedVisitInputDriven machine input H w base hbound
                      fuel (.rejected .intermediateWorkHeadExit) =
                    .completed target := by
                simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
                  using hrun
              have hfixed := runFiniteCachedVisitInputDriven_eq_self_of_halted
                machine input hbound fuel
                  (.rejected .intermediateWorkHeadExit) rfl
              rw [hfixed] at hrunRejected
              contradiction
          | inputHorizonExceeded =>
              have hrunRejected :
                  runFiniteCachedVisitInputDriven machine input H w base hbound
                      fuel (.rejected .inputHorizonExceeded) =
                    .completed target := by
                simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
                  using hrun
              have hfixed := runFiniteCachedVisitInputDriven_eq_self_of_halted
                machine input hbound fuel (.rejected .inputHorizonExceeded) rfl
              rw [hfixed] at hrunRejected
              contradiction
  exact go remaining.val remaining live final rfl hcompleted

/-- Canonical execution for exactly the phase's remaining counter always
ends in a terminal phase, whether it completes successfully or rejects. -/
theorem runFiniteCachedVisitInputDriven_halted_of_remaining
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w) :
    finiteCachedVisitPhaseHalted
      (runFiniteCachedVisitInputDriven machine input H w base hbound
        remaining.val (.running remaining live)) = true := by
  have go : ∀ fuel : Nat, ∀ (currentRemaining : Fin (H + 1))
      (currentLive : LocalReplayState
        (cachedInputMachine machine).State H w),
      currentRemaining.val = fuel →
      finiteCachedVisitPhaseHalted
        (runFiniteCachedVisitInputDriven machine input H w base hbound fuel
          (.running currentRemaining currentLive)) = true := by
    intro fuel
    induction fuel with
    | zero =>
        intro currentRemaining currentLive hremaining
        simp [runFiniteCachedVisitInputDriven,
          finiteCachedVisitPhaseHalted, hremaining]
    | succ fuel ih =>
        intro currentRemaining currentLive hremaining
        let unread := readOnlySymbol input currentLive.inputHead.val
        have hpositive : 0 < currentRemaining.val := by omega
        have hphaseNotHalted :
            finiteCachedVisitPhaseHalted
              (.running currentRemaining currentLive) = false := by
          simp [finiteCachedVisitPhaseHalted, Nat.ne_of_gt hpositive]
        have hanswer :=
          finiteCachedVisit_inputDrivenAnswer_eq_streamingAnswer machine input
            currentRemaining currentLive unread hpositive rfl
        simp only [runFiniteCachedVisitInputDriven, hphaseNotHalted,
          Bool.false_eq_true, ↓reduceIte]
        rw [hanswer]
        have hend : cachedLocalStepNeedsUnread machine currentLive = true →
            ¬ currentLive.inputHead.val < input.length →
              unread = .rightEnd := by
          intro _ hhead
          exact readOnlySymbol_eq_rightEnd_of_length_le input
            currentLive.inputHead.val (Nat.le_of_not_gt hhead)
        rw [finiteCachedVisitStreamingStep_answerForUnread machine input.length
          hbound currentRemaining currentLive unread hend]
        by_cases htailZero : fuel = 0
        · subst fuel
          simp only [runFiniteCachedVisitInputDriven]
          apply finiteCachedVisitPhaseHalted_advance_of_remaining_eq_one
            machine hbound
          omega
        · have hzero : currentRemaining.val ≠ 0 := by omega
          have hone : currentRemaining.val ≠ 1 := by omega
          cases hlocal : finiteLocalCachedStep machine H w base unread
              currentLive with
          | inside next =>
              have htailRemaining : (spendVisitStep currentRemaining).val =
                  fuel := by
                simp only [spendVisitStep]
                omega
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal] using
                ih (spendVisitStep currentRemaining) next htailRemaining
          | halted outcome =>
              have htailRemaining : (spendVisitStep currentRemaining).val =
                  fuel := by
                simp only [spendVisitStep]
                omega
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal] using
                ih (spendVisitStep currentRemaining) currentLive htailRemaining
          | workHeadExit =>
              simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                runFiniteCachedVisitInputDriven_eq_self_of_halted,
                finiteCachedVisitPhaseHalted]
          | inputHorizonExceeded =>
              simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                runFiniteCachedVisitInputDriven_eq_self_of_halted,
                finiteCachedVisitPhaseHalted]
  exact go remaining.val remaining live rfl

/-- Symbol agreement alone discharges the adaptive run-level realization
bridge for the canonical Boolean view of the immutable input. -/
theorem adaptiveOrderRealizesFiniteCachedVisit_of_symbolsAgree
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
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry)) :
    AdaptiveOrderRealizesFiniteCachedVisit machine input alpha block visit
      carried hentry (fun index => input.get index) := by
  let width := advertisedBlockWidth alpha.offsets block
  let base := advertisedBlockLower alpha.offsets block
  let hbound :=
    advertisedBlockLower_add_width_le_horizon alpha.offsets block
  let remaining := fixedAlphaVisitRemaining visit
  let initial := finiteCachedStateOfVisitEntry machine alpha block visit
    carried hentry
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedVisitAdaptiveQueryIndex? (H := T) (w := width) machine
      input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let target := runFiniteCachedVisitStreamingWithUnreads machine input.length T
    width base hbound unreads (.running remaining initial)
  have hnonempty : unreads ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [unreads, FixedAlphaBlockVisit.steps_pos]
  have hlength : remaining.val = unreads.length := by
    simp [remaining, unreads, fixedAlphaVisitRemaining]
  have hrunner :
      runFiniteCachedVisitInputDriven machine input T width base hbound
          unreads.length (.running remaining initial) = target := by
    exact runFiniteCachedVisitInputDriven_eq_streaming_of_symbolsAgree
      machine input hbound unreads remaining initial hnonempty hlength
        (by simpa [width, base, unreads, initial] using hagree)
  have hcoreShort :
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          unreads.length (.running remaining initial) = target := by
    change
      (finiteCachedVisitStreamingVerifier machine input.length T width base
        hbound remaining initial visit.exit).inputDrivenCore
          (fun bit => .bit bit) selector inputBits unreads.length
            (.running remaining initial) = target
    rw [finiteCachedVisitStreamingVerifier_inputDrivenCore_eq]
    exact hrunner
  have htargetHalted : verifier.halted target = true := by
    change finiteCachedVisitPhaseHalted target = true
    simpa [target, width, base, hbound, unreads, remaining, initial] using
      finiteCachedVisitComparisonTarget_halted machine input alpha block visit
        carried hentry
  have hlengthLe : unreads.length ≤ T := by
    have hremaining := remaining.isLt
    rw [hlength] at hremaining
    omega
  have hcoreFull :
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits T
          verifier.start = target := by
    have hstart : verifier.start = .running remaining initial := rfl
    rw [hstart]
    have hsplit : T = unreads.length + (T - unreads.length) := by omega
    calc
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits T
          (.running remaining initial) =
        verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (unreads.length + (T - unreads.length))
          (.running remaining initial) :=
            congrArg (fun fuel => verifier.inputDrivenCore
              (fun bit => .bit bit) selector inputBits fuel
                (.running remaining initial)) hsplit
      _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (T - unreads.length)
          (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
            unreads.length (.running remaining initial)) :=
        verifier.inputDrivenCore_add (fun bit => .bit bit) selector inputBits
          unreads.length (T - unreads.length) _
      _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (T - unreads.length) target := by rw [hcoreShort]
      _ = target := verifier.inputDrivenCore_eq_self_of_halted
        (fun bit => .bit bit) selector inputBits (T - unreads.length) target
          htargetHalted
  have htotal : ∀ phase, verifier.requestsInput phase = true →
      ∃ index, selector phase = some index := by
    intro phase hrequest
    change finiteCachedVisitPhaseRequestsInput machine input.length phase =
      true at hrequest
    exact finiteCachedVisitAdaptiveQueryIndex?_total_of_requestsInput machine
      input.length phase hrequest
  have hrunPhase :
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 =
        verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits T
          verifier.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        verifier.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) selector inputBits htotal
          (verifier.initialFueledState T) T le_rfl
  have hphase :
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 =
        target := hrunPhase.trans hcoreFull
  have hhaltedRun : verifier.halted
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 =
        true := by
    rw [hphase]
    exact htargetHalted
  unfold AdaptiveOrderRealizesFiniteCachedVisit
  change verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits) = target
  calc
    verifier.finishWithEndSymbol .rightEnd
        (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits) =
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 :=
        verifier.finishWithEndSymbol_eq_of_halted .rightEnd _ hhaltedRun
    _ = target := hphase

/-- After discharging adaptive scheduling internally, symbol agreement is the
only remaining premise for a full semantic equivalence. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_symbolsAgree
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
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry)) :
    (compileAdaptiveFiniteCachedFixedAlphaVisit machine alpha block visit
      carried hentry).eval (fun index => input.get index) = true ↔
      FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried := by
  exact compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_realizes
    machine input alpha block visit carried hentry (fun index => input.get index)
      hagree
      (adaptiveOrderRealizesFiniteCachedVisit_of_symbolsAgree machine input
        alpha block visit carried hentry hagree)

/-- Soundness of the adaptive compiler under the exact remaining local
symbol-agreement premise. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_valid_of_eval_eq_true_of_symbolsAgree
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
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry))
    (heval : (compileAdaptiveFiniteCachedFixedAlphaVisit machine alpha block
      visit carried hentry).eval (fun index => input.get index) = true) :
    FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
      visit carried :=
  (compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_symbolsAgree
    machine input alpha block visit carried hentry hagree).mp heval

/-- Unconditional completeness: every semantically valid cached visit is
accepted by the adaptive compiler on the canonical Boolean input view. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_of_valid
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
      alpha block visit carried) :
    (compileAdaptiveFiniteCachedFixedAlphaVisit machine alpha block visit
      carried hentry).eval (fun index => input.get index) = true := by
  have hagree := finiteCachedVisitSymbolsAgree_of_fixedAlphaBlockVisitValid
    machine input alpha block visit carried hentry hvalid
  exact
    (compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_iff_of_symbolsAgree
      machine input alpha block visit carried hentry hagree).mpr hvalid

/-- Unconditional soundness on the canonical Boolean input view.  A successful
adaptive execution generates its own agreeing unread trace, so no external
symbol-agreement or scheduling premise is required. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_valid_of_eval_eq_true
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
    (heval : (compileAdaptiveFiniteCachedFixedAlphaVisit machine alpha block
      visit carried hentry).eval (fun index => input.get index) = true) :
    FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
      visit carried := by
  let width := advertisedBlockWidth alpha.offsets block
  let base := advertisedBlockLower alpha.offsets block
  let hbound :=
    advertisedBlockLower_add_width_le_horizon alpha.offsets block
  let remaining := fixedAlphaVisitRemaining visit
  let initial := finiteCachedStateOfVisitEntry machine alpha block visit
    carried hentry
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedVisitAdaptiveQueryIndex? (H := T) (w := width) machine
      input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let shortPhase := runFiniteCachedVisitInputDriven machine input T width base
    hbound remaining.val (.running remaining initial)
  have hshortHalted : finiteCachedVisitPhaseHalted shortPhase = true := by
    exact runFiniteCachedVisitInputDriven_halted_of_remaining machine input
      hbound remaining initial
  have hcoreShort :
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          remaining.val verifier.start = shortPhase := by
    change
      (finiteCachedVisitStreamingVerifier machine input.length T width base
        hbound remaining initial visit.exit).inputDrivenCore
          (fun bit => .bit bit) selector inputBits remaining.val
            (.running remaining initial) = shortPhase
    rw [finiteCachedVisitStreamingVerifier_inputDrivenCore_eq]
  have hremainingLe : remaining.val ≤ T := by
    exact Nat.le_of_lt_succ remaining.isLt
  have hshortVerifierHalted : verifier.halted shortPhase = true := by
    exact hshortHalted
  have hcoreFull :
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits T
          verifier.start = shortPhase := by
    have hsplit : T = remaining.val + (T - remaining.val) := by omega
    calc
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits T
          verifier.start =
        verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (remaining.val + (T - remaining.val)) verifier.start :=
            congrArg (fun fuel => verifier.inputDrivenCore
              (fun bit => .bit bit) selector inputBits fuel verifier.start)
                hsplit
      _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (T - remaining.val)
          (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
            remaining.val verifier.start) :=
        verifier.inputDrivenCore_add (fun bit => .bit bit) selector inputBits
          remaining.val (T - remaining.val) _
      _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (T - remaining.val) shortPhase := by rw [hcoreShort]
      _ = shortPhase := verifier.inputDrivenCore_eq_self_of_halted
        (fun bit => .bit bit) selector inputBits (T - remaining.val)
          shortPhase hshortVerifierHalted
  have htotal : ∀ phase, verifier.requestsInput phase = true →
      ∃ index, selector phase = some index := by
    intro phase hrequest
    change finiteCachedVisitPhaseRequestsInput machine input.length phase =
      true at hrequest
    exact finiteCachedVisitAdaptiveQueryIndex?_total_of_requestsInput machine
      input.length phase hrequest
  have hrunPhase :
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 =
        verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits T
          verifier.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        verifier.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) selector inputBits htotal
          (verifier.initialFueledState T) T le_rfl
  have hphase :
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 =
        shortPhase := hrunPhase.trans hcoreFull
  have hhaltedRun : verifier.halted
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 =
        true := by
    rw [hphase]
    exact hshortVerifierHalted
  have hfinish : verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits) =
        shortPhase := by
    calc
      verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits) =
        (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits).1 :=
          verifier.finishWithEndSymbol_eq_of_halted .rightEnd _ hhaltedRun
      _ = shortPhase := hphase
  change (verifier.compileAdaptive T input.length (fun bit => .bit bit)
      .rightEnd selector).eval inputBits = true at heval
  rw [FiniteStreamingVerifier.compileAdaptive_eval] at heval
  change @finiteCachedVisitPhaseAccept (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T width visit.exit
      (verifier.finishWithEndSymbol .rightEnd
        (verifier.runAdaptive T (fun bit => .bit bit) selector inputBits)) =
          true at heval
  rw [hfinish] at heval
  cases hshort : shortPhase with
  | running otherRemaining otherLive =>
      simp [finiteCachedVisitPhaseAccept, hshort] at heval
  | rejected failure =>
      simp [finiteCachedVisitPhaseAccept, hshort] at heval
  | completed final =>
      have hendpoint :=
        (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T width visit.exit final).mp
            (by simpa [hshort] using heval)
      have hcompleted :
          runFiniteCachedVisitInputDriven machine input T width base hbound
            remaining.val (.running remaining initial) = .completed final := by
        simpa [shortPhase] using hshort
      obtain ⟨unreads, htraceLength, hagree, hstream⟩ :=
        runFiniteCachedVisitInputDriven_completed_has_agreeing_trace
          machine input hbound remaining initial final hcompleted
      have hnonempty : unreads ≠ [] := by
        apply List.ne_nil_of_length_pos
        rw [htraceLength]
        simp [remaining, fixedAlphaVisitRemaining,
          FixedAlphaBlockVisit.steps_pos]
      have hremainingLength : remaining.val = unreads.length :=
        htraceLength.symm
      have hrespect : FiniteCachedVisitUnreadsRespectEnd machine input.length
          T width base unreads initial :=
        finiteCachedVisitSymbolsAgree_implies_respectEnd machine input unreads
          initial hagree
      have hstreamReplay := runFiniteCachedVisitStreamingWithUnreads_eq_replay
        machine input.length hbound unreads remaining initial hnonempty
          hremainingLength hrespect
      have hmapped : streamingStateOfFiniteReplayResult
          (finiteCachedVisitReplay machine T width base hbound unreads initial) =
            .completed final := hstreamReplay.symm.trans hstream
      have hreplay : finiteCachedVisitReplay machine T width base hbound
          unreads initial = .completed final := by
        cases hresult : finiteCachedVisitReplay machine T width base hbound
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
      have htraceVisitLength : unreads.length = visit.steps := by
        rw [htraceLength]
        rfl
      have hreplayFixed : finiteCachedFixedAlphaBlockVisitReplay machine alpha
          block visit carried hentry unreads = .completed final := by
        simpa [finiteCachedFixedAlphaBlockVisitReplay, width, base, hbound,
          initial] using hreplay
      exact (finiteCachedFixedAlphaBlockVisitReplay_completed_sound machine
        input alpha block visit carried hentry unreads final htraceVisitLength
          hagree hreplayFixed ⟨hendpoint.1, hendpoint.2.1,
            hendpoint.2.2⟩).1

/-- Full unconditional semantic correctness of the adaptive cached-visit
compiler on the canonical Boolean view of the immutable input. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_iff
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
      visit.entry.workHead.val) :
    (compileAdaptiveFiniteCachedFixedAlphaVisit machine alpha block visit
      carried hentry).eval (fun index => input.get index) = true ↔
      FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried := by
  constructor
  · exact compileAdaptiveFiniteCachedFixedAlphaVisit_valid_of_eval_eq_true
      machine input alpha block visit carried hentry
  · exact compileAdaptiveFiniteCachedFixedAlphaVisit_eval_eq_true_of_valid
      machine input alpha block visit carried hentry

end OneTapeMagnification
end Frontier
end Pnp4
