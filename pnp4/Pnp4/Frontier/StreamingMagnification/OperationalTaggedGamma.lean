import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper
import Pnp4.Frontier.StreamingMagnification.StreamMergeRequestCodec
import Mathlib.Tactic.DeriveFintype

/-!
# A fixed-control tag and three-gamma front end

The global Stream-Merge request starts with the byte `179 = 10110011₂` and
then three consecutive canonical gamma words.  This module wraps the
value-preserving gamma zipper in one finite transition table.  The final tag
bit (cell `7`) is retained as the left sentinel for the first zipper run.

Only the transition action of `OperationalGammaZipper.gammaZipper` is used in
the three core phases.  A core transition whose target is `done` is intercepted:
the first two such transitions restart `scanFirst` in the next fixed phase,
whereas the third enters an absorbing accepting state.  A core transition to
`reject` enters an absorbing rejecting state.  Thus no decoded value, unary
length, input offset, or ambient input length occurs in the finite control.

The exact frame definitions below record how the zipper's trailing `C = 1`
is shared as the sentinel immediately to the left of the next gamma word.
They do not claim full-machine correctness.  That theorem still needs (i) the
global induction from a valid gamma frame to the zipper's final frame, which
is intentionally not postulated here, and (ii) a final exact ambient-length
check so that an accepted request cannot ignore a suffix.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalTaggedGamma

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity
open OperationalGammaZipper

/-! ## One fixed transition table -/

/-- The three gamma invocations are fixed syntax, not input-dependent data. -/
inductive GammaPhase where
  | first
  | second
  | third
  deriving DecidableEq, Fintype

/--
Eight byte-checking states, three tagged copies of the 57-state zipper core,
and two absorbing outcomes.
-/
inductive TaggedState where
  | tag0
  | tag1
  | tag2
  | tag3
  | tag4
  | tag5
  | tag6
  | tag7
  | core (phase : GammaPhase) (state : ZipperState)
  | done
  | reject
  deriving DecidableEq, Fintype

/-- Change only the state component of a delegated zipper transition. -/
def liftCoreTarget (phase : GammaPhase) (target : ZipperState) : TaggedState :=
  match target with
  | .done =>
      match phase with
      | .first => .core .second .scanFirst
      | .second => .core .third .scanFirst
      | .third => .done
  | .reject => .reject
  | running => .core phase running

/--
Delegate the tape write and head move literally to the zipper, intercepting
only its target state.
-/
def delegatedStep (phase : GammaPhase) (state : ZipperState) (scanned : Bool) :
    TaggedState × Bool × Move :=
  match state with
  | .done => (.reject, scanned, .stay)
  | .reject => (.reject, scanned, .stay)
  | running =>
      let result := gammaZipper.step running scanned
      (liftCoreTarget phase result.1, result.2.1, result.2.2)

/-- Validate one forced tag bit, preserving it on the tape. -/
def tagStep (expected scanned : Bool) (next : TaggedState) :
    TaggedState × Bool × Move :=
  if scanned = expected then (next, scanned, .right)
  else (.reject, scanned, .stay)

/--
The tag-plus-three-gamma machine.  The expected byte is big-endian
`10110011`; its last `1` is simultaneously the first zipper sentinel.
-/
def taggedGamma : OperationalTM where
  state := TaggedState
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := .tag0
  step := fun state scanned =>
    match state with
    | .tag0 => tagStep true scanned .tag1
    | .tag1 => tagStep false scanned .tag2
    | .tag2 => tagStep true scanned .tag3
    | .tag3 => tagStep true scanned .tag4
    | .tag4 => tagStep false scanned .tag5
    | .tag5 => tagStep false scanned .tag6
    | .tag6 => tagStep true scanned .tag7
    | .tag7 => tagStep true scanned (.core .first .scanFirst)
    | .core phase coreState => delegatedStep phase coreState scanned
    | .done => (.done, scanned, .stay)
    | .reject => (.reject, scanned, .stay)
  exponent := 4
  output := fun state => state == .done

/-- The complete control has a constant 181 states. -/
@[simp] theorem taggedGamma_state_card :
    Fintype.card taggedGamma.state = 181 := by
  set_option maxRecDepth 100000 in
    decide

/-- The chosen quartic canonical clock.  Its slack over the fully composed
three-field run will follow only after the global zipper induction. -/
@[simp] theorem taggedGamma_clock (inputLength : Nat) :
    taggedGamma.executionTM.runTime inputLength = inputLength ^ 4 + 4 :=
  rfl

/-! ## Exact tag and core handoffs -/

@[simp] theorem step_tag0_one :
    taggedGamma.step .tag0 true = (.tag1, true, .right) := rfl

@[simp] theorem step_tag0_zero :
    taggedGamma.step .tag0 false = (.reject, false, .stay) := rfl

@[simp] theorem step_tag1_zero :
    taggedGamma.step .tag1 false = (.tag2, false, .right) := rfl

@[simp] theorem step_tag1_one :
    taggedGamma.step .tag1 true = (.reject, true, .stay) := rfl

@[simp] theorem step_tag2_one :
    taggedGamma.step .tag2 true = (.tag3, true, .right) := rfl

@[simp] theorem step_tag2_zero :
    taggedGamma.step .tag2 false = (.reject, false, .stay) := rfl

@[simp] theorem step_tag3_one :
    taggedGamma.step .tag3 true = (.tag4, true, .right) := rfl

@[simp] theorem step_tag3_zero :
    taggedGamma.step .tag3 false = (.reject, false, .stay) := rfl

@[simp] theorem step_tag4_zero :
    taggedGamma.step .tag4 false = (.tag5, false, .right) := rfl

@[simp] theorem step_tag4_one :
    taggedGamma.step .tag4 true = (.reject, true, .stay) := rfl

@[simp] theorem step_tag5_zero :
    taggedGamma.step .tag5 false = (.tag6, false, .right) := rfl

@[simp] theorem step_tag5_one :
    taggedGamma.step .tag5 true = (.reject, true, .stay) := rfl

@[simp] theorem step_tag6_one :
    taggedGamma.step .tag6 true = (.tag7, true, .right) := rfl

@[simp] theorem step_tag6_zero :
    taggedGamma.step .tag6 false = (.reject, false, .stay) := rfl

/-- Cell 7 is validated and retained as the first zipper sentinel. -/
@[simp] theorem step_tag7_one :
    taggedGamma.step .tag7 true =
      (.core .first .scanFirst, true, .right) := rfl

@[simp] theorem step_tag7_zero :
    taggedGamma.step .tag7 false = (.reject, false, .stay) := rfl

@[simp] theorem step_done (scanned : Bool) :
    taggedGamma.step .done scanned = (.done, scanned, .stay) := rfl

@[simp] theorem step_reject (scanned : Bool) :
    taggedGamma.step .reject scanned = (.reject, scanned, .stay) := rfl

/-- Delegation preserves the zipper's write and movement exactly. -/
theorem delegatedStep_action (phase : GammaPhase) (state : ZipperState)
    (scanned : Bool) :
    (delegatedStep phase state scanned).2 =
      (gammaZipper.step state scanned).2 := by
  cases state <;> simp [delegatedStep, gammaZipper, liftCoreTarget]

/-- The wrapper's core branch uses precisely the delegated transition. -/
@[simp] theorem step_core (phase : GammaPhase) (state : ZipperState)
    (scanned : Bool) :
    taggedGamma.step (.core phase state) scanned =
      delegatedStep phase state scanned := by
  rfl

/-- A first-phase `done` target restarts the same core at gamma word two. -/
theorem delegatedStep_first_done (state : ZipperState) (scanned : Bool)
    (hstateDone : state ≠ .done) (hstateReject : state ≠ .reject)
    (hdone : (gammaZipper.step state scanned).1 = .done) :
    delegatedStep .first state scanned =
      (.core .second .scanFirst,
        (gammaZipper.step state scanned).2.1,
        (gammaZipper.step state scanned).2.2) := by
  cases state <;>
    simp_all [delegatedStep, gammaZipper, liftCoreTarget]

/-- A second-phase `done` target restarts the same core at gamma word three. -/
theorem delegatedStep_second_done (state : ZipperState) (scanned : Bool)
    (hstateDone : state ≠ .done) (hstateReject : state ≠ .reject)
    (hdone : (gammaZipper.step state scanned).1 = .done) :
    delegatedStep .second state scanned =
      (.core .third .scanFirst,
        (gammaZipper.step state scanned).2.1,
        (gammaZipper.step state scanned).2.2) := by
  cases state <;>
    simp_all [delegatedStep, gammaZipper, liftCoreTarget]

/-- A third-phase `done` target enters the absorbing accepting state. -/
theorem delegatedStep_third_done (state : ZipperState) (scanned : Bool)
    (hstateDone : state ≠ .done) (hstateReject : state ≠ .reject)
    (hdone : (gammaZipper.step state scanned).1 = .done) :
    delegatedStep .third state scanned =
      (.done,
        (gammaZipper.step state scanned).2.1,
        (gammaZipper.step state scanned).2.2) := by
  cases state <;>
    simp_all [delegatedStep, gammaZipper, liftCoreTarget]

/-- Any zipper rejection propagates to the wrapper's absorbing rejection. -/
theorem delegatedStep_reject (phase : GammaPhase) (state : ZipperState)
    (scanned : Bool)
    (hreject : (gammaZipper.step state scanned).1 = .reject) :
    delegatedStep phase state scanned =
      (.reject,
        (gammaZipper.step state scanned).2.1,
        (gammaZipper.step state scanned).2.2) := by
  cases state <;>
    simp_all [delegatedStep, gammaZipper, liftCoreTarget]

/-- Embedded terminal core states are unreachable and fail closed. -/
@[simp] theorem step_embedded_done (phase : GammaPhase) (scanned : Bool) :
    taggedGamma.step (.core phase .done) scanned =
      (.reject, scanned, .stay) := rfl

/-- Embedded zipper rejection is represented only by the wrapper rejection. -/
@[simp] theorem step_embedded_reject (phase : GammaPhase) (scanned : Bool) :
    taggedGamma.step (.core phase .reject) scanned =
      (.reject, scanned, .stay) := rfl

/-- The zero-length first gamma hands off without changing its terminator. -/
@[simp] theorem step_first_empty_gamma :
    taggedGamma.step (.core .first .scanFirst) true =
      (.core .second .scanFirst, true, .right) := rfl

/-- The zero-length second gamma hands off in exactly the same way. -/
@[simp] theorem step_second_empty_gamma :
    taggedGamma.step (.core .second .scanFirst) true =
      (.core .third .scanFirst, true, .right) := rfl

/-- The zero-length third gamma completes the fixed three-field front end. -/
@[simp] theorem step_third_empty_gamma :
    taggedGamma.step (.core .third .scanFirst) true =
      (.done, true, .right) := rfl

/-- A nonempty first field preserves the final `C` and starts field two. -/
@[simp] theorem step_first_finalC (x : Bool) :
    taggedGamma.step (.core .first (.forwardBlockStart true x)) true =
      (.core .second .scanFirst, true, .right) := rfl

/-- A nonempty second field preserves the final `C` and starts field three. -/
@[simp] theorem step_second_finalC (x : Bool) :
    taggedGamma.step (.core .second (.forwardBlockStart true x)) true =
      (.core .third .scanFirst, true, .right) := rfl

/-- A nonempty third field preserves the final `C` and accepts. -/
@[simp] theorem step_third_finalC (x : Bool) :
    taggedGamma.step (.core .third (.forwardBlockStart true x)) true =
      (.done, true, .right) := rfl

/-! ## Semantic frame algebra for three consecutive gamma words -/

/-- The first seven bits of request tag 179; the eighth bit is the sentinel. -/
def requestTagPrefix : List Bool :=
  [true, false, true, true, false, false, true]

/-- The full big-endian byte `179 = 10110011₂`. -/
def requestTagList : List Bool := requestTagPrefix ++ [true]

@[simp] theorem requestTagPrefix_length : requestTagPrefix.length = 7 := rfl

@[simp] theorem requestTagList_length : requestTagList.length = 8 := rfl

/-- The explicit byte is exactly the request codec's fixed-width tag field. -/
theorem requestTagList_eq_codec :
    requestTagList =
      List.ofFn StreamMergeRequestCodec.requestTagBits := by
  decide

/-- In the codec itself, zero-based tag bit seven is the retained sentinel. -/
@[simp] theorem requestTagBits_bit7 :
    StreamMergeRequestCodec.requestTagBits ⟨7, by
      norm_num [Pnp4.Frontier.ContractExpansion.tagLen]⟩ = true := by
  decide

/-- A raw gamma word after (and excluding) its shared left sentinel. -/
def gammaBody (k : Nat) (payload : List Bool) : List Bool :=
  List.replicate k false ++ true :: payload

@[simp] theorem gammaBody_length (k : Nat) (payload : List Bool) :
    (gammaBody k payload).length = k + payload.length + 1 := by
  simp [gammaBody]
  omega

/-- The transformed body after a successful zipper pass. -/
def zippedBody (payload : List Bool) : List Bool := encChain payload

@[simp] theorem zippedBody_length (payload : List Bool) :
    (zippedBody payload).length = 2 * payload.length + 1 := by
  simp [zippedBody, encChain]

/-- The unmodified tag followed by three raw, consecutive gamma words. -/
def tripleInitialFrame (k₁ : Nat) (payload₁ : List Bool)
    (k₂ : Nat) (payload₂ : List Bool)
    (k₃ : Nat) (payload₃ : List Bool) : List Bool :=
  requestTagPrefix ++ [true] ++
    gammaBody k₁ payload₁ ++
    gammaBody k₂ payload₂ ++
    gammaBody k₃ payload₃

/-- Frame after word one, with its trailing sentinel shared with word two. -/
def tripleAfterFirstFrame (payload₁ : List Bool)
    (k₂ : Nat) (payload₂ : List Bool)
    (k₃ : Nat) (payload₃ : List Bool) : List Bool :=
  requestTagPrefix ++ [true] ++
    zippedBody payload₁ ++
    gammaBody k₂ payload₂ ++
    gammaBody k₃ payload₃

/-- Frame after word two, sharing both internal sentinels exactly once. -/
def tripleAfterSecondFrame (payload₁ payload₂ : List Bool)
    (k₃ : Nat) (payload₃ : List Bool) : List Bool :=
  requestTagPrefix ++ [true] ++
    zippedBody payload₁ ++
    zippedBody payload₂ ++
    gammaBody k₃ payload₃

/-- Frame after all three gamma words have been value-preservingly zipped. -/
def tripleFinalFrame (payload₁ payload₂ payload₃ : List Bool) : List Bool :=
  requestTagPrefix ++ [true] ++
    zippedBody payload₁ ++
    zippedBody payload₂ ++
    zippedBody payload₃

/-- Common footprint of every phase when payload `i` has length `kᵢ`. -/
def tripleFootprint (k₁ k₂ k₃ : Nat) : Nat :=
  11 + 2 * (k₁ + k₂ + k₃)

theorem tripleInitialFrame_length {k₁ k₂ k₃ : Nat}
    {payload₁ payload₂ payload₃ : List Bool}
    (h₁ : payload₁.length = k₁)
    (h₂ : payload₂.length = k₂)
    (h₃ : payload₃.length = k₃) :
    (tripleInitialFrame k₁ payload₁ k₂ payload₂ k₃ payload₃).length =
      tripleFootprint k₁ k₂ k₃ := by
  simp [tripleInitialFrame, tripleFootprint, h₁, h₂, h₃]
  omega

theorem tripleAfterFirstFrame_length {k₁ k₂ k₃ : Nat}
    {payload₁ payload₂ payload₃ : List Bool}
    (h₁ : payload₁.length = k₁)
    (h₂ : payload₂.length = k₂)
    (h₃ : payload₃.length = k₃) :
    (tripleAfterFirstFrame payload₁ k₂ payload₂ k₃ payload₃).length =
      tripleFootprint k₁ k₂ k₃ := by
  simp [tripleAfterFirstFrame, tripleFootprint, h₁, h₂, h₃]
  omega

theorem tripleAfterSecondFrame_length {k₁ k₂ k₃ : Nat}
    {payload₁ payload₂ payload₃ : List Bool}
    (h₁ : payload₁.length = k₁)
    (h₂ : payload₂.length = k₂)
    (h₃ : payload₃.length = k₃) :
    (tripleAfterSecondFrame payload₁ payload₂ k₃ payload₃).length =
      tripleFootprint k₁ k₂ k₃ := by
  simp [tripleAfterSecondFrame, tripleFootprint, h₁, h₂, h₃]
  omega

theorem tripleFinalFrame_length {k₁ k₂ k₃ : Nat}
    {payload₁ payload₂ payload₃ : List Bool}
    (h₁ : payload₁.length = k₁)
    (h₂ : payload₂.length = k₂)
    (h₃ : payload₃.length = k₃) :
    (tripleFinalFrame payload₁ payload₂ payload₃).length =
      tripleFootprint k₁ k₂ k₃ := by
  simp [tripleFinalFrame, tripleFootprint, h₁, h₂, h₃]
  omega

/-- Start cell of the first gamma body, immediately right of tag bit seven. -/
def firstGammaStart : Nat := 8

/-- Start cell of gamma body two after the first field's exact footprint. -/
def secondGammaStart (k₁ : Nat) : Nat := 9 + 2 * k₁

/-- Start cell of gamma body three after the first two exact footprints. -/
def thirdGammaStart (k₁ k₂ : Nat) : Nat :=
  10 + 2 * (k₁ + k₂)

theorem afterFirst_drop {k₁ : Nat} {payload₁ : List Bool}
    (h₁ : payload₁.length = k₁)
    (k₂ : Nat) (payload₂ : List Bool)
    (k₃ : Nat) (payload₃ : List Bool) :
    (tripleAfterFirstFrame payload₁ k₂ payload₂ k₃ payload₃).drop
        (secondGammaStart k₁) =
      gammaBody k₂ payload₂ ++ gammaBody k₃ payload₃ := by
  let fieldPrefix := requestTagPrefix ++ [true] ++ zippedBody payload₁
  have hp : fieldPrefix.length = secondGammaStart k₁ := by
    simp [fieldPrefix, secondGammaStart, h₁]
    omega
  have hframe :
      tripleAfterFirstFrame payload₁ k₂ payload₂ k₃ payload₃ =
        fieldPrefix ++ (gammaBody k₂ payload₂ ++ gammaBody k₃ payload₃) := by
    simp [tripleAfterFirstFrame, fieldPrefix, List.append_assoc]
  rw [hframe, ← hp]
  simp

theorem afterSecond_drop {k₁ k₂ : Nat} {payload₁ payload₂ : List Bool}
    (h₁ : payload₁.length = k₁) (h₂ : payload₂.length = k₂)
    (k₃ : Nat) (payload₃ : List Bool) :
    (tripleAfterSecondFrame payload₁ payload₂ k₃ payload₃).drop
        (thirdGammaStart k₁ k₂) =
      gammaBody k₃ payload₃ := by
  let fieldPrefix := requestTagPrefix ++ [true] ++ zippedBody payload₁ ++
    zippedBody payload₂
  have hp : fieldPrefix.length = thirdGammaStart k₁ k₂ := by
    simp [fieldPrefix, thirdGammaStart, h₁, h₂]
    omega
  have hframe :
      tripleAfterSecondFrame payload₁ payload₂ k₃ payload₃ =
        fieldPrefix ++ gammaBody k₃ payload₃ := by
    simp [tripleAfterSecondFrame, fieldPrefix, List.append_assoc]
  rw [hframe, ← hp]
  simp

/-!
The preceding length and drop theorems are the strongest unconditional
composition facts currently available: in the defined intermediate frames,
the next raw gamma body begins at the stated offset and no cell is inserted or
lost.  They are frame algebra, not a machine-run theorem.  A run theorem from
`tripleInitialFrame` to `tripleFinalFrame` is not stated conditionally.  Its
honest next obligations are the missing global zipper induction and, after the
third handoff, exact comparison with the ambient finite input length.
-/

end OperationalTaggedGamma
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedGamma_state_card
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.requestTagList_eq_codec
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.tripleFinalFrame_length
