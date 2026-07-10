import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaPrefixClosure

/-!
# A one-tick accepting pulse and the exact missing clock delay

The current `taggedGamma` front end accepts every finite continuation of a
canonical tag-plus-three-gamma prefix because its accepting state is
absorbing.  This module tests the smallest possible local repair: keep the
same finite control and every parsing transition, but make `done` an accepting
pulse that moves to the absorbing `reject` state after one step.

The pulse removes the already-formalized absorbing-prefix failure.  It does
not by itself produce an exact-length parser: the canonical three-field trace
finishes strictly before the quartic clock at which `OperationalTM.accepts`
observes the state.  Consequently even an exact canonical input is rejected.
The final definitions isolate the positive, exact amount of delay that a
completion preserving this trace and adding a post-parse filler would have to
realize.  No length advice, contract, provider, or unproved machine is
introduced.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalTaggedGamma

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity
open OperationalGammaZipper

/-! ## The fixed 181-state pulse machine -/

/-- The same parser as `taggedGamma`, except that the accepting state lasts
for exactly one configuration and then enters the absorbing reject state. -/
def taggedGammaPulse : OperationalTM where
  state := TaggedState
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := .tag0
  step := fun state scanned =>
    match state with
    | .done => (.reject, scanned, .stay)
    | other => taggedGamma.step other scanned
  exponent := 4
  output := fun state => state == .done

@[simp] theorem taggedGammaPulse_state_card :
    Fintype.card taggedGammaPulse.state = 181 := by
  change Fintype.card TaggedState = 181
  exact taggedGamma_state_card

@[simp] theorem taggedGammaPulse_clock (inputLength : Nat) :
    taggedGammaPulse.executionTM.runTime inputLength = inputLength ^ 4 + 4 :=
  rfl

@[simp] theorem taggedGammaPulse_step_done (scanned : Bool) :
    taggedGammaPulse.step .done scanned = (.reject, scanned, .stay) := rfl

@[simp] theorem taggedGammaPulse_step_reject (scanned : Bool) :
    taggedGammaPulse.step .reject scanned = (.reject, scanned, .stay) := rfl

theorem taggedGammaPulse_step_eq (state : TaggedState) (scanned : Bool)
    (hstate : state ≠ .done) :
    taggedGammaPulse.step state scanned = taggedGamma.step state scanned := by
  cases state <;> simp_all [taggedGammaPulse]

/-! ## Natural-coordinate trace and first hit -/

def pulseNatStep (config : TaggedNatConfig) : TaggedNatConfig :=
  let result := taggedGammaPulse.step config.state (config.tape config.head)
  ⟨result.1, moveNat config.head result.2.2,
    writeNat config.tape config.head result.2.1⟩

def pulseNatRun (config : TaggedNatConfig) (steps : Nat) : TaggedNatConfig :=
  Nat.iterate pulseNatStep steps config

@[simp] theorem pulseNatRun_zero (config : TaggedNatConfig) :
    pulseNatRun config 0 = config := rfl

theorem pulseNatRun_add (config : TaggedNatConfig) (first second : Nat) :
    pulseNatRun config (first + second) =
      pulseNatRun (pulseNatRun config first) second := by
  unfold pulseNatRun
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem pulseNatRun_succ (config : TaggedNatConfig) (steps : Nat) :
    pulseNatRun config (steps + 1) =
      pulseNatStep (pulseNatRun config steps) := by
  unfold pulseNatRun
  exact Function.iterate_succ_apply' pulseNatStep steps config

theorem pulseNatStep_eq_taggedNatStep (config : TaggedNatConfig)
    (hstate : config.state ≠ .done) :
    pulseNatStep config = taggedNatStep config := by
  rcases config with ⟨state, head, tape⟩
  simp only [pulseNatStep, taggedNatStep]
  rw [taggedGammaPulse_step_eq state (tape head) hstate]

/-- A pulse run agrees with the original parser for as long as the original
run has not yet entered `done`.  This theorem contains no assumption about a
particular input or clock. -/
theorem pulseNatRun_eq_taggedNatRun (config : TaggedNatConfig) (steps : Nat)
    (hactive : forall elapsed, elapsed < steps ->
      (taggedNatRun config elapsed).state ≠ .done) :
    pulseNatRun config steps = taggedNatRun config steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [pulseNatRun_succ, taggedNatRun_succ]
      rw [ih (fun elapsed helapsed => hactive elapsed (by omega))]
      exact pulseNatStep_eq_taggedNatStep (taggedNatRun config steps)
        (hactive steps (by omega))

/-- During the eight correct tag transitions neither terminal state is
visited. -/
theorem taggedNatRun_requestTag_active (tape : Nat -> Bool)
    (h0 : tape 0 = true) (h1 : tape 1 = false)
    (h2 : tape 2 = true) (h3 : tape 3 = true)
    (h4 : tape 4 = false) (h5 : tape 5 = false)
    (h6 : tape 6 = true)
    (elapsed : Nat) (helapsed : elapsed < 8) :
    let config := taggedNatRun ⟨.tag0, 0, tape⟩ elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  dsimp only
  interval_cases elapsed <;>
    simp [taggedNatRun, Function.iterate_succ_apply', taggedNatStep,
      taggedGamma, tagStep, h0, h1, h2, h3, h4, h5, h6, moveNat]

theorem taggedNatRun_canonicalTag_active
    (k₁ k₂ k₃ : Nat) (payload₁ payload₂ payload₃ : List Bool)
    (suffix : Nat -> Bool) (elapsed : Nat) (helapsed : elapsed < 8) :
    let config := taggedNatRun
      ⟨.tag0, 0,
        framedTape
          (tripleInitialFrame k₁ payload₁ k₂ payload₂ k₃ payload₃) suffix⟩
      elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  refine taggedNatRun_requestTag_active _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ elapsed
    helapsed
  all_goals simp [framedTape, tripleInitialFrame, requestTagPrefix]

theorem liftCoreTarget_active (phase : GammaPhase) (state : ZipperState)
    (hdone : state ≠ .done) (hreject : state ≠ .reject) :
    liftCoreTarget phase state ≠ .done ∧
      liftCoreTarget phase state ≠ .reject := by
  cases state <;> simp_all [liftCoreTarget]

/-- The tagged wrapper inherits the zipper's contextual first-hit theorem in
each fixed phase. -/
theorem taggedNatRun_contextualPhase_active (phase : GammaPhase)
    (front payload tail : List Bool) (suffix : Nat -> Bool)
    (elapsed : Nat) (helapsed : elapsed < gammaBodyTime payload.length) :
    let config := taggedNatRun
      (liftNatConfig phase
        (contextualScanFirstConfig front payload tail suffix)) elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  dsimp only
  rw [taggedNatRun_lift]
  · exact liftCoreTarget_active phase _
      (natRun_contextualScanFirst_active front payload tail suffix elapsed
        helapsed).1
      (natRun_contextualScanFirst_active front payload tail suffix elapsed
        helapsed).2
  · intro earlier hearlier
    exact natRun_contextualScanFirst_active front payload tail suffix earlier
      (lt_trans hearlier helapsed)

theorem taggedNatRun_firstField_active
    (payload₁ payload₂ payload₃ : List Bool) (suffix : Nat -> Bool)
    (elapsed : Nat) (helapsed : elapsed < gammaBodyTime payload₁.length) :
    let config := taggedNatRun
      ⟨.core .first .scanFirst, 8,
        framedTape
          (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
            payload₃.length payload₃) suffix⟩ elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  have h := taggedNatRun_contextualPhase_active .first requestTagPrefix payload₁
    (gammaBody payload₂.length payload₂ ++
      gammaBody payload₃.length payload₃) suffix elapsed helapsed
  simpa [liftNatConfig, contextualScanFirstConfig, contextualTape,
    initialFrame_eq_sentinel_body, tripleInitialFrame, List.append_assoc]
    using h

theorem taggedNatRun_secondField_active
    (payload₁ payload₂ payload₃ : List Bool) (suffix : Nat -> Bool)
    (elapsed : Nat) (helapsed : elapsed < gammaBodyTime payload₂.length) :
    let config := taggedNatRun
      ⟨.core .second .scanFirst, secondGammaStart payload₁.length,
        framedTape
          (tripleAfterFirstFrame payload₁ payload₂.length payload₂
            payload₃.length payload₃) suffix⟩ elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  have h := taggedNatRun_contextualPhase_active .second
    (secondFieldFront payload₁) payload₂
    (gammaBody payload₃.length payload₃) suffix elapsed helapsed
  have hstart :
      secondGammaStart payload₁.length =
        (secondFieldFront payload₁).length + 1 := by
    simp [secondGammaStart, secondFieldFront]
    omega
  rw [hstart]
  simpa [liftNatConfig, contextualScanFirstConfig, contextualTape,
    secondFieldFront, initialFrame_eq_sentinel_body,
    zippedBody_dropLast_append_sentinel, tripleAfterFirstFrame,
    secondGammaStart, List.append_assoc] using h

theorem taggedNatRun_thirdField_active
    (payload₁ payload₂ payload₃ : List Bool) (suffix : Nat -> Bool)
    (elapsed : Nat) (helapsed : elapsed < gammaBodyTime payload₃.length) :
    let config := taggedNatRun
      ⟨.core .third .scanFirst,
        thirdGammaStart payload₁.length payload₂.length,
        framedTape
          (tripleAfterSecondFrame payload₁ payload₂ payload₃.length payload₃)
          suffix⟩ elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  have h := taggedNatRun_contextualPhase_active .third
    (thirdFieldFront payload₁ payload₂) payload₃ [] suffix elapsed helapsed
  have hstart :
      thirdGammaStart payload₁.length payload₂.length =
        (thirdFieldFront payload₁ payload₂).length + 1 := by
    simp [thirdGammaStart, thirdFieldFront]
    omega
  rw [hstart]
  simpa [liftNatConfig, contextualScanFirstConfig, contextualTape,
    thirdFieldFront, initialFrame_eq_sentinel_body,
    zippedBody_dropLast_append_sentinel, tripleAfterSecondFrame,
    thirdGammaStart, List.append_assoc] using h

/-- The composed tagged endpoint is a first hit: on a canonical tagged triple,
no earlier state is either terminal outcome. -/
theorem taggedNatRun_triple_active
    (payload₁ payload₂ payload₃ : List Bool) (suffix : Nat -> Bool)
    (elapsed : Nat)
    (helapsed : elapsed <
      taggedTripleTime payload₁.length payload₂.length payload₃.length) :
    let config := taggedNatRun
      ⟨.tag0, 0,
        framedTape
          (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
            payload₃.length payload₃) suffix⟩ elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  dsimp only
  by_cases htag : elapsed < 8
  · exact taggedNatRun_canonicalTag_active payload₁.length payload₂.length
      payload₃.length payload₁ payload₂ payload₃ suffix elapsed htag
  by_cases hfirst : elapsed < 8 + gammaBodyTime payload₁.length
  · have heq : elapsed = 8 + (elapsed - 8) := by omega
    rw [heq, taggedNatRun_add, taggedNatRun_canonicalTag]
    exact taggedNatRun_firstField_active payload₁ payload₂ payload₃ suffix
      (elapsed - 8) (by omega)
  by_cases hsecond :
      elapsed < 8 + gammaBodyTime payload₁.length +
        gammaBodyTime payload₂.length
  · have heq : elapsed =
        8 + (gammaBodyTime payload₁.length +
          (elapsed - (8 + gammaBodyTime payload₁.length))) := by omega
    rw [heq, taggedNatRun_add, taggedNatRun_canonicalTag,
      taggedNatRun_add, taggedNatRun_firstField]
    exact taggedNatRun_secondField_active payload₁ payload₂ payload₃ suffix
      (elapsed - (8 + gammaBodyTime payload₁.length)) (by omega)
  · have heq : elapsed =
        8 + (gammaBodyTime payload₁.length +
          (gammaBodyTime payload₂.length +
            (elapsed - (8 + gammaBodyTime payload₁.length +
              gammaBodyTime payload₂.length)))) := by omega
    rw [heq, taggedNatRun_add, taggedNatRun_canonicalTag,
      taggedNatRun_add, taggedNatRun_firstField,
      taggedNatRun_add, taggedNatRun_secondField]
    exact taggedNatRun_thirdField_active payload₁ payload₂ payload₃ suffix
      (elapsed - (8 + gammaBodyTime payload₁.length +
        gammaBodyTime payload₂.length)) (by
          simp [taggedTripleTime] at helapsed
          omega)

/-- The pulse machine reaches `done` at precisely the same useful endpoint as
the original parser. -/
theorem pulseNatRun_triple (payload₁ payload₂ payload₃ : List Bool)
    (suffix : Nat -> Bool) :
    pulseNatRun
        ⟨.tag0, 0,
          framedTape
            (tripleInitialFrame payload₁.length payload₁ payload₂.length
              payload₂ payload₃.length payload₃) suffix⟩
        (taggedTripleTime payload₁.length payload₂.length payload₃.length) =
      ⟨.done,
        tripleFootprint payload₁.length payload₂.length payload₃.length,
        framedTape (tripleFinalFrame payload₁ payload₂ payload₃) suffix⟩ := by
  rw [pulseNatRun_eq_taggedNatRun]
  · exact taggedNatRun_triple payload₁ payload₂ payload₃ suffix
  · intro elapsed helapsed
    exact (taggedNatRun_triple_active payload₁ payload₂ payload₃ suffix elapsed
      helapsed).1

/-- One transition after the useful endpoint, the pulse has expired. -/
theorem pulseNatRun_triple_succ (payload₁ payload₂ payload₃ : List Bool)
    (suffix : Nat -> Bool) :
    (pulseNatRun
      ⟨.tag0, 0,
        framedTape
          (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
            payload₃.length payload₃) suffix⟩
      (taggedTripleTime payload₁.length payload₂.length payload₃.length + 1)).state
        = .reject := by
  rw [pulseNatRun_succ, pulseNatRun_triple]
  rfl

@[simp] theorem pulseNatStep_reject (head : Nat) (tape : Nat -> Bool) :
    pulseNatStep ⟨.reject, head, tape⟩ = ⟨.reject, head, tape⟩ := by
  simp [pulseNatStep, taggedGammaPulse, moveNat]

@[simp] theorem pulseNatRun_reject (head : Nat) (tape : Nat -> Bool)
    (steps : Nat) :
    pulseNatRun ⟨.reject, head, tape⟩ steps = ⟨.reject, head, tape⟩ := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [pulseNatRun_succ, ih]
      exact pulseNatStep_reject head tape

/-! ## Finite-tape execution bridge -/

abbrev PulseExecutionTM := taggedGammaPulse.executionTM

/-- Agreement between the actual finite pulse-machine tape and the natural
coordinate facade on every allocated cell. -/
def PulseFiniteNatAgree {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (natural : TaggedNatConfig) : Prop :=
  actual.state = natural.state /\
    actual.head.val = natural.head /\
      forall index, actual.tape index = natural.tape index.val

theorem pulseMoveHead_val_eq_moveNat {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (naturalHead : Nat) (move : Move)
    (hhead : actual.head.val = naturalHead)
    (hroom : naturalHead + 1 < PulseExecutionTM.tapeLength inputLength) :
    (actual.moveHead move).val = moveNat naturalHead move := by
  cases move with
  | left =>
      by_cases hzero : naturalHead = 0
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
  | stay => simp [TM.Configuration.moveHead, moveNat, hhead]
  | right => simp [TM.Configuration.moveHead, moveNat, hhead, hroom]

theorem pulseNatStep_head_le_succ (natural : TaggedNatConfig) :
    (pulseNatStep natural).head <= natural.head + 1 := by
  unfold pulseNatStep
  generalize
    taggedGammaPulse.step natural.state (natural.tape natural.head) = result
  rcases result with ⟨nextState, written, move⟩
  cases move <;> (simp [moveNat] <;> omega)

theorem pulseNatRun_head_le (natural : TaggedNatConfig) (steps : Nat) :
    (pulseNatRun natural steps).head <= natural.head + steps := by
  induction steps with
  | zero => simp [pulseNatRun]
  | succ steps ih =>
      rw [pulseNatRun_succ]
      exact le_trans (pulseNatStep_head_le_succ _) (by omega)

theorem pulseFiniteNatAgree_step {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (natural : TaggedNatConfig)
    (hagrees : PulseFiniteNatAgree actual natural)
    (hroom : natural.head + 1 < PulseExecutionTM.tapeLength inputLength) :
    PulseFiniteNatAgree (PulseExecutionTM.stepConfig actual)
      (pulseNatStep natural) := by
  rcases hagrees with ⟨hstate, hhead, htape⟩
  have hscan :
      actual.tape actual.head = natural.tape natural.head := by
    rw [htape actual.head, hhead]
  generalize hresult :
    taggedGammaPulse.step natural.state (natural.tape natural.head) = result
  rcases result with ⟨nextState, written, move⟩
  unfold PulseFiniteNatAgree
  simp only [TM.stepConfig, pulseNatStep, OperationalTM.executionTM]
  rw [hstate, hscan, hresult]
  refine ⟨rfl,
    pulseMoveHead_val_eq_moveNat actual natural.head move hhead hroom, ?_⟩
  intro index
  by_cases hindex : index = actual.head
  · subst index
    simp [TM.Configuration.write, writeNat, hhead]
  · have hval : index.val ≠ natural.head := by
      intro heq
      apply hindex
      apply Fin.ext
      exact heq.trans hhead.symm
    simp [TM.Configuration.write, writeNat, hindex, hval, htape index]

theorem pulseRunConfig_succ_front {inputLength steps : Nat}
    (actual : PulseExecutionTM.Configuration inputLength) :
    PulseExecutionTM.runConfig actual (steps + 1) =
      PulseExecutionTM.runConfig (PulseExecutionTM.stepConfig actual) steps := by
  unfold TM.runConfig
  simpa [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply
      (TM.stepConfig (M := PulseExecutionTM)) steps actual

theorem pulseNatRun_succ_front (natural : TaggedNatConfig) (steps : Nat) :
    pulseNatRun natural (steps + 1) =
      pulseNatRun (pulseNatStep natural) steps := by
  unfold pulseNatRun
  simpa [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply pulseNatStep steps natural

theorem pulseFiniteNatAgree_run {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (natural : TaggedNatConfig) (steps : Nat)
    (hagrees : PulseFiniteNatAgree actual natural)
    (hroom : natural.head + steps <
      PulseExecutionTM.tapeLength inputLength) :
    PulseFiniteNatAgree (PulseExecutionTM.runConfig actual steps)
      (pulseNatRun natural steps) := by
  induction steps generalizing actual natural with
  | zero => simpa [TM.runConfig, pulseNatRun] using hagrees
  | succ steps ih =>
      rw [pulseRunConfig_succ_front, pulseNatRun_succ_front]
      apply ih
      · exact pulseFiniteNatAgree_step actual natural hagrees (by omega)
      · have hstep := pulseNatStep_head_le_succ natural
        omega

theorem pulseInitialConfig_finiteNatAgree
    (payload₁ payload₂ payload₃ : List Bool) :
    PulseFiniteNatAgree
      (PulseExecutionTM.initialConfig
        (taggedTripleInput payload₁ payload₂ payload₃))
      ⟨.tag0, 0,
        framedTape
          (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
            payload₃.length payload₃)
          (fun _ => false)⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  unfold TM.initialConfig
  dsimp only
  unfold framedTape
  by_cases hinput : index.val <
      tripleFootprint payload₁.length payload₂.length payload₃.length
  · simp only [hinput, dite_true, taggedTripleInput]
    have hframe : index.val <
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃).length := by
      rw [tripleInitialFrame_length rfl rfl rfl]
      exact hinput
    rw [List.getElem?_eq_getElem hframe]
  · have hframe :
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃)[index.val]? = none := by
      rw [List.getElem?_eq_none_iff]
      rw [tripleInitialFrame_length rfl rfl rfl]
      omega
    simp [hinput, hframe]

theorem pulseTripleTime_lt_tapeLength (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ <
      PulseExecutionTM.tapeLength (tripleFootprint k₁ k₂ k₃) := by
  change taggedTripleTime k₁ k₂ k₃ <
    tripleFootprint k₁ k₂ k₃ +
      (tripleFootprint k₁ k₂ k₃ ^ 4 + 4) + 1
  simpa [TaggedExecutionTM, TM.tapeLength, OperationalTM.executionTM,
    taggedGamma] using taggedTripleTime_lt_tapeLength k₁ k₂ k₃

/-- Actual finite-tape execution reaches the one-tick accepting state at the
exact useful time. -/
theorem pulseExecution_runConfig_triple
    (payload₁ payload₂ payload₃ : List Bool) :
    PulseFiniteNatAgree
      (PulseExecutionTM.runConfig
        (PulseExecutionTM.initialConfig
          (taggedTripleInput payload₁ payload₂ payload₃))
        (taggedTripleTime payload₁.length payload₂.length payload₃.length))
      ⟨.done,
        tripleFootprint payload₁.length payload₂.length payload₃.length,
        framedTape (tripleFinalFrame payload₁ payload₂ payload₃)
          (fun _ => false)⟩ := by
  have hagrees := pulseFiniteNatAgree_run
    (PulseExecutionTM.initialConfig
      (taggedTripleInput payload₁ payload₂ payload₃))
    ⟨.tag0, 0,
      framedTape
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃)
        (fun _ => false)⟩
    (taggedTripleTime payload₁.length payload₂.length payload₃.length)
    (pulseInitialConfig_finiteNatAgree payload₁ payload₂ payload₃)
    (by
      simpa using pulseTripleTime_lt_tapeLength payload₁.length payload₂.length
        payload₃.length)
  rw [pulseNatRun_triple] at hagrees
  exact hagrees

/-! ## The exact delay required by the quartic observation clock -/

/-- Closed-form delay between the useful three-field endpoint and the
canonical quartic clock.  It depends on the three decoded field lengths, not
only on their total footprint. -/
def taggedClockDelay (k₁ k₂ k₃ : Nat) : Nat :=
  let total := k₁ + k₂ + k₃
  let cross := k₁ * k₂ + k₁ * k₃ + k₂ * k₃
  16 * total ^ 4 + 352 * total ^ 3 + 2899 * total ^ 2 +
    10644 * total + 14634 + 10 * cross

theorem taggedTripleTime_add_clockDelay (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ + taggedClockDelay k₁ k₂ k₃ =
      PulseExecutionTM.runTime (tripleFootprint k₁ k₂ k₃) := by
  rw [taggedTripleTime_closed]
  simp only [taggedClockDelay, PulseExecutionTM,
    OperationalTM.executionTM, taggedGammaPulse]
  simp [tripleFootprint]
  ring

theorem taggedClockDelay_pos (k₁ k₂ k₃ : Nat) :
    0 < taggedClockDelay k₁ k₂ k₃ := by
  simp only [taggedClockDelay]
  omega

theorem taggedTripleTime_lt_pulseRunTime (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ <
      PulseExecutionTM.runTime (tripleFootprint k₁ k₂ k₃) := by
  have heq := taggedTripleTime_add_clockDelay k₁ k₂ k₃
  have hpos := taggedClockDelay_pos k₁ k₂ k₃
  omega

theorem taggedClockDelay_eq_sub (k₁ k₂ k₃ : Nat) :
    taggedClockDelay k₁ k₂ k₃ =
      PulseExecutionTM.runTime (tripleFootprint k₁ k₂ k₃) -
        taggedTripleTime k₁ k₂ k₃ := by
  have heq := taggedTripleTime_add_clockDelay k₁ k₂ k₃
  have hpos := taggedClockDelay_pos k₁ k₂ k₃
  omega

/-! The delay has a useful exact arithmetic decomposition.  The first term
equalizes traces with the same total unary length but different distributions
among the three fields.  The remaining term depends only on that total. -/

def taggedDistributionEqualizer (k₁ k₂ k₃ : Nat) : Nat :=
  10 * (k₁ * k₂ + k₁ * k₃ + k₂ * k₃)

def taggedEqualizedTime (total : Nat) : Nat :=
  5 * total ^ 2 + 4 * total + 11

def taggedQuarticLengthFiller (total : Nat) : Nat :=
  16 * total ^ 4 + 352 * total ^ 3 + 2899 * total ^ 2 +
    10644 * total + 14634

def taggedCubicLengthFiller (total : Nat) : Nat :=
  8 * total ^ 3 + 127 * total ^ 2 + 722 * total + 1323

theorem taggedTripleTime_add_distributionEqualizer (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ +
        taggedDistributionEqualizer k₁ k₂ k₃ =
      taggedEqualizedTime (k₁ + k₂ + k₃) := by
  rw [taggedTripleTime_closed]
  simp [taggedDistributionEqualizer, taggedEqualizedTime]
  ring

theorem taggedClockDelay_decomposition (k₁ k₂ k₃ : Nat) :
    taggedClockDelay k₁ k₂ k₃ =
      taggedDistributionEqualizer k₁ k₂ k₃ +
        taggedQuarticLengthFiller (k₁ + k₂ + k₃) := by
  simp [taggedClockDelay, taggedDistributionEqualizer,
    taggedQuarticLengthFiller]
  ring

theorem taggedEqualizedTime_add_quarticFiller (total : Nat) :
    taggedEqualizedTime total + taggedQuarticLengthFiller total =
      (11 + 2 * total) ^ 4 + 4 := by
  simp [taggedEqualizedTime, taggedQuarticLengthFiller]
  ring

/-- A cubic clock is arithmetically sufficient after the same distribution
equalizer.  This is an exact target count, not an implementation of a timer. -/
theorem taggedEqualizedTime_add_cubicFiller (total : Nat) :
    taggedEqualizedTime total + taggedCubicLengthFiller total =
      (11 + 2 * total) ^ 3 + 3 := by
  simp [taggedEqualizedTime, taggedCubicLengthFiller]
  ring

/-- No additive post-parse delay depending only on the aggregate three-field
footprint can align all of the current, unmodified canonical traces with the
quartic clock.  This does not exclude retiming the parser or first adding the
distribution equalizer above.  The equal-footprint instances `(2,0,0)` and
`(1,1,0)` have different useful times. -/
theorem no_postParse_lengthOnlyTaggedClockDelay :
    ¬ exists delay : Nat -> Nat, forall k₁ k₂ k₃,
      taggedTripleTime k₁ k₂ k₃ +
          delay (tripleFootprint k₁ k₂ k₃) =
        PulseExecutionTM.runTime (tripleFootprint k₁ k₂ k₃) := by
  rintro ⟨delay, hdelay⟩
  have hleft := hdelay 2 0 0
  have hright := hdelay 1 1 0
  norm_num [taggedTripleTime, gammaBodyTime, tripleFootprint,
    PulseExecutionTM, OperationalTM.executionTM, taggedGammaPulse] at hleft hright
  omega

/-! ## Expiration before the actual observation time -/

theorem pulseRunConfig_add {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (first second : Nat) :
    PulseExecutionTM.runConfig actual (first + second) =
      PulseExecutionTM.runConfig
        (PulseExecutionTM.runConfig actual first) second := by
  unfold TM.runConfig
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem pulseRunConfig_succ {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength) (steps : Nat) :
    PulseExecutionTM.runConfig actual (steps + 1) =
      PulseExecutionTM.stepConfig
        (PulseExecutionTM.runConfig actual steps) := by
  unfold TM.runConfig
  exact Function.iterate_succ_apply'
    (TM.stepConfig (M := PulseExecutionTM)) steps actual

theorem pulseStepConfig_state_done_to_reject {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (hdone : actual.state = .done) :
    (PulseExecutionTM.stepConfig actual).state = .reject := by
  unfold TM.stepConfig
  simp [OperationalTM.executionTM, taggedGammaPulse, hdone]

theorem pulseStepConfig_state_reject {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (hreject : actual.state = .reject) :
    (PulseExecutionTM.stepConfig actual).state = .reject := by
  unfold TM.stepConfig
  simp [OperationalTM.executionTM, taggedGammaPulse, hreject]

theorem pulseRunConfig_state_reject {inputLength : Nat}
    (actual : PulseExecutionTM.Configuration inputLength)
    (steps : Nat) (hreject : actual.state = .reject) :
    (PulseExecutionTM.runConfig actual steps).state = .reject := by
  induction steps generalizing actual with
  | zero => simpa [TM.runConfig] using hreject
  | succ steps ih =>
      rw [pulseRunConfig_succ_front]
      exact ih (PulseExecutionTM.stepConfig actual)
        (pulseStepConfig_state_reject actual hreject)

theorem pulseExecution_runConfig_triple_succ
    (payload₁ payload₂ payload₃ : List Bool) :
    (PulseExecutionTM.runConfig
      (PulseExecutionTM.initialConfig
        (taggedTripleInput payload₁ payload₂ payload₃))
      (taggedTripleTime payload₁.length payload₂.length payload₃.length + 1)).state
        = .reject := by
  rw [pulseRunConfig_succ]
  exact pulseStepConfig_state_done_to_reject _
    (pulseExecution_runConfig_triple payload₁ payload₂ payload₃).1

/-- The no-delay pulse rejects even the exact canonical tagged triple at the
machine's actual quartic observation time. -/
theorem taggedGammaPulse_run_state_reject
    (payload₁ payload₂ payload₃ : List Bool) :
    (PulseExecutionTM.run
      (taggedTripleInput payload₁ payload₂ payload₃)).state = .reject := by
  let inputLength :=
    tripleFootprint payload₁.length payload₂.length payload₃.length
  let initial := PulseExecutionTM.initialConfig
    (taggedTripleInput payload₁ payload₂ payload₃)
  let finish :=
    taggedTripleTime payload₁.length payload₂.length payload₃.length
  have hfinish :
      (PulseExecutionTM.runConfig initial (finish + 1)).state = .reject := by
    exact pulseExecution_runConfig_triple_succ payload₁ payload₂ payload₃
  have hle : finish + 1 <= PulseExecutionTM.runTime inputLength := by
    have hlt := taggedTripleTime_lt_pulseRunTime payload₁.length payload₂.length
      payload₃.length
    have hlt' : finish < PulseExecutionTM.runTime inputLength := by
      simpa [finish, inputLength] using hlt
    omega
  unfold TM.run
  change
    (PulseExecutionTM.runConfig initial
      (PulseExecutionTM.runTime inputLength)).state = .reject
  rw [show PulseExecutionTM.runTime inputLength =
      (finish + 1) + (PulseExecutionTM.runTime inputLength - (finish + 1)) by
    omega]
  rw [pulseRunConfig_add]
  exact pulseRunConfig_state_reject _ _ hfinish

theorem taggedGammaPulse_rejects_canonical_triple
    (payload₁ payload₂ payload₃ : List Bool) :
    taggedGammaPulse.accepts
      (tripleFootprint payload₁.length payload₂.length payload₃.length)
      (taggedTripleInput payload₁ payload₂ payload₃) = false := by
  unfold OperationalTM.accepts
  rw [taggedGammaPulse_run_state_reject]
  rfl

/-! ## Arbitrary finite suffixes -/

theorem pulseExtendedInitialConfig_finiteNatAgree
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    PulseFiniteNatAgree
      (PulseExecutionTM.initialConfig
        (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix))
      ⟨.tag0, 0,
        framedTape
          (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
            payload₃.length payload₃)
          (finiteSuffixTape suffix)⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  unfold TM.initialConfig
  dsimp only
  by_cases hinput : index.val <
      tripleFootprint payload₁.length payload₂.length payload₃.length +
        suffix.length
  · simp only [hinput, dite_true, taggedTripleExtendedInput]
  · have hframeLength :
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃).length =
            tripleFootprint payload₁.length payload₂.length payload₃.length :=
      tripleInitialFrame_length rfl rfl rfl
    have hbeyond :
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃).length + suffix.length <= index.val := by
      rw [hframeLength]
      omega
    simp only [hinput, dite_false]
    exact (framedTape_finiteSuffixTape_blank
      (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
        payload₃.length payload₃) suffix index.val hbeyond).symm

theorem pulseTripleTime_lt_extendedTapeLength
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    taggedTripleTime payload₁.length payload₂.length payload₃.length <
      PulseExecutionTM.tapeLength
        (tripleFootprint payload₁.length payload₂.length payload₃.length +
          suffix.length) := by
  let footprint :=
    tripleFootprint payload₁.length payload₂.length payload₃.length
  have hbase :
      taggedTripleTime payload₁.length payload₂.length payload₃.length <
        footprint + (footprint ^ 4 + 4) + 1 := by
    simpa [footprint, PulseExecutionTM, TM.tapeLength,
      OperationalTM.executionTM, taggedGammaPulse] using
      pulseTripleTime_lt_tapeLength payload₁.length payload₂.length
        payload₃.length
  have hfootprint : footprint <= footprint + suffix.length := by omega
  have hpow : footprint ^ 4 <= (footprint + suffix.length) ^ 4 :=
    Nat.pow_le_pow_left hfootprint 4
  change taggedTripleTime payload₁.length payload₂.length payload₃.length <
    (footprint + suffix.length) +
      ((footprint + suffix.length) ^ 4 + 4) + 1
  omega

theorem pulseExecution_runConfig_extendedTriple
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    PulseFiniteNatAgree
      (PulseExecutionTM.runConfig
        (PulseExecutionTM.initialConfig
          (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix))
        (taggedTripleTime payload₁.length payload₂.length payload₃.length))
      ⟨.done,
        tripleFootprint payload₁.length payload₂.length payload₃.length,
        framedTape (tripleFinalFrame payload₁ payload₂ payload₃)
          (finiteSuffixTape suffix)⟩ := by
  have hagrees := pulseFiniteNatAgree_run
    (PulseExecutionTM.initialConfig
      (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix))
    ⟨.tag0, 0,
      framedTape
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃)
        (finiteSuffixTape suffix)⟩
    (taggedTripleTime payload₁.length payload₂.length payload₃.length)
    (pulseExtendedInitialConfig_finiteNatAgree payload₁ payload₂ payload₃ suffix)
    (by simpa using
      pulseTripleTime_lt_extendedTapeLength payload₁ payload₂ payload₃ suffix)
  rw [pulseNatRun_triple] at hagrees
  exact hagrees

theorem taggedTripleTime_lt_pulseExtendedRunTime
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    taggedTripleTime payload₁.length payload₂.length payload₃.length <
      PulseExecutionTM.runTime
        (tripleFootprint payload₁.length payload₂.length payload₃.length +
          suffix.length) := by
  let footprint :=
    tripleFootprint payload₁.length payload₂.length payload₃.length
  have hbase :
      taggedTripleTime payload₁.length payload₂.length payload₃.length <
        footprint ^ 4 + 4 := by
    simpa [footprint, PulseExecutionTM, OperationalTM.executionTM,
      taggedGammaPulse] using
      taggedTripleTime_lt_pulseRunTime payload₁.length payload₂.length
        payload₃.length
  have hfootprint : footprint <= footprint + suffix.length := by omega
  have hpow : footprint ^ 4 <= (footprint + suffix.length) ^ 4 :=
    Nat.pow_le_pow_left hfootprint 4
  change taggedTripleTime payload₁.length payload₂.length payload₃.length <
    (footprint + suffix.length) ^ 4 + 4
  omega

theorem pulseExecution_runConfig_extendedTriple_succ
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    (PulseExecutionTM.runConfig
      (PulseExecutionTM.initialConfig
        (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix))
      (taggedTripleTime payload₁.length payload₂.length payload₃.length + 1)).state
        = .reject := by
  rw [pulseRunConfig_succ]
  exact pulseStepConfig_state_done_to_reject _
    (pulseExecution_runConfig_extendedTriple payload₁ payload₂ payload₃ suffix).1

theorem taggedGammaPulse_extended_run_state_reject
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    (PulseExecutionTM.run
      (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix)).state =
        .reject := by
  let inputLength :=
    tripleFootprint payload₁.length payload₂.length payload₃.length +
      suffix.length
  let initial := PulseExecutionTM.initialConfig
    (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix)
  let finish :=
    taggedTripleTime payload₁.length payload₂.length payload₃.length
  have hfinish :
      (PulseExecutionTM.runConfig initial (finish + 1)).state = .reject := by
    exact pulseExecution_runConfig_extendedTriple_succ payload₁ payload₂ payload₃
      suffix
  have hle : finish + 1 <= PulseExecutionTM.runTime inputLength := by
    have hlt := taggedTripleTime_lt_pulseExtendedRunTime payload₁ payload₂
      payload₃ suffix
    have hlt' : finish < PulseExecutionTM.runTime inputLength := by
      simpa [finish, inputLength] using hlt
    omega
  unfold TM.run
  change
    (PulseExecutionTM.runConfig initial
      (PulseExecutionTM.runTime inputLength)).state = .reject
  rw [show PulseExecutionTM.runTime inputLength =
      (finish + 1) + (PulseExecutionTM.runTime inputLength - (finish + 1)) by
    omega]
  rw [pulseRunConfig_add]
  exact pulseRunConfig_state_reject _ _ hfinish

/-- The immediate pulse is not an ambient-length repair: it rejects every
canonical prefix with any finite suffix, including the empty suffix. -/
theorem taggedGammaPulse_rejects_canonical_prefix_with_suffix
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    taggedGammaPulse.accepts
      (tripleFootprint payload₁.length payload₂.length payload₃.length +
        suffix.length)
      (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix) = false := by
  unfold OperationalTM.accepts
  rw [taggedGammaPulse_extended_run_state_reject]
  rfl

end OperationalTaggedGamma
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_triple_active
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.pulseNatRun_triple
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.pulseNatRun_triple_succ
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.pulseExecution_runConfig_triple
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedTripleTime_add_clockDelay
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.no_postParse_lengthOnlyTaggedClockDelay
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedGammaPulse_rejects_canonical_triple
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedGammaPulse_rejects_canonical_prefix_with_suffix
