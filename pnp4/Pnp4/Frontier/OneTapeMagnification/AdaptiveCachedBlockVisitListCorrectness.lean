import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaBlockVisitInputOrder
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedVisitCorrectness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Operational correctness of the adaptive cached block-visit list

This file connects the single executable list verifier to the recursively
slab-threaded semantic certificate.  The key bookkeeping device is an exact
embedding of the tail verifier into the verifier for a list with one visit
prepended: tail cursors are shifted by one, while completed and rejected
states are unchanged.
-/

/-- Embed the verifier for `rest` into the verifier for `first :: rest` by
shifting every active cursor by one. -/
def prependFiniteCachedBlockVisitListState
    {State : Type} {H w : Nat}
    (first : FixedAlphaBlockVisit State H)
    (rest : List (FixedAlphaBlockVisit State H)) :
    FiniteCachedBlockVisitListStreamingState State H w rest.length →
      FiniteCachedBlockVisitListStreamingState State H w
        (first :: rest).length
  | .active cursor phase =>
      .active ⟨cursor.val + 1, by simp⟩ phase
  | .completed slab => .completed slab
  | .rejected => .rejected

@[simp]
theorem prependFiniteCachedBlockVisitListState_completed
    {State : Type} {H w : Nat}
    (first : FixedAlphaBlockVisit State H)
    (rest : List (FixedAlphaBlockVisit State H))
    (slab : WorkSlab w) :
    prependFiniteCachedBlockVisitListState first rest (.completed slab) =
      .completed slab := rfl

@[simp]
theorem prependFiniteCachedBlockVisitListState_rejected
    {State : Type} {H w : Nat}
    (first : FixedAlphaBlockVisit State H)
    (rest : List (FixedAlphaBlockVisit State H)) :
    prependFiniteCachedBlockVisitListState (w := w) first rest (.rejected) =
      .rejected := rfl

@[simp]
theorem finiteCachedBlockVisitListHalted_prepend
    {State : Type} {H w : Nat}
    (first : FixedAlphaBlockVisit State H)
    (rest : List (FixedAlphaBlockVisit State H))
    (state : FiniteCachedBlockVisitListStreamingState State H w rest.length) :
    finiteCachedBlockVisitListHalted
        (prependFiniteCachedBlockVisitListState first rest state) =
      finiteCachedBlockVisitListHalted state := by
  cases state <;> rfl

@[simp]
theorem finiteCachedBlockVisitListRequestsInput_prepend
    (machine : DeterministicMachine) (n : Nat)
    {H w : Nat}
    (first : FixedAlphaBlockVisit (cachedInputMachine machine).State H)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State H))
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State H w rest.length) :
    finiteCachedBlockVisitListRequestsInput machine n
        (prependFiniteCachedBlockVisitListState first rest state) =
      finiteCachedBlockVisitListRequestsInput machine n state := by
  cases state <;> rfl

@[simp]
theorem finiteCachedBlockVisitListAdaptiveQueryIndex?_prepend
    (machine : DeterministicMachine) (n : Nat)
    {H w : Nat}
    (first : FixedAlphaBlockVisit (cachedInputMachine machine).State H)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State H))
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State H w rest.length) :
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
        (prependFiniteCachedBlockVisitListState first rest state) =
      finiteCachedBlockVisitListAdaptiveQueryIndex? machine n state := by
  cases state <;> rfl

/-- Prepending one advertised visit merely shifts the cursor of every tail
transition.  This is the operational simulation used by the list induction. -/
theorem finiteCachedBlockVisitListStreamingStep_prepend
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (first : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hcons : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (htail : FixedAlphaBlockVisitEntriesInside alpha block rest)
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) rest.length)
    (supplied : Option ReadOnlySymbol) :
    finiteCachedBlockVisitListStreamingStep machine n alpha block
        (first :: rest) hcons
        (prependFiniteCachedBlockVisitListState first rest state) supplied =
      prependFiniteCachedBlockVisitListState first rest
        (finiteCachedBlockVisitListStreamingStep machine n alpha block rest
          htail state supplied) := by
  cases state with
  | completed slab => rfl
  | rejected => rfl
  | active cursor phase =>
      cases phase with
      | running remaining live =>
          simp only [prependFiniteCachedBlockVisitListState,
            finiteCachedBlockVisitListStreamingStep]
          generalize finiteCachedVisitStreamingStep machine n T
            (advertisedBlockWidth alpha.offsets block)
            (advertisedBlockLower alpha.offsets block)
            (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
            (.running remaining live) supplied = next
          cases next <;> rfl
      | rejected failure =>
          simp [prependFiniteCachedBlockVisitListState,
            finiteCachedBlockVisitListStreamingStep]
      | completed final =>
          simp only [prependFiniteCachedBlockVisitListState,
            finiteCachedBlockVisitListStreamingStep]
          by_cases haccept : @finiteCachedVisitPhaseAccept
              (cachedInputMachine machine).State
              (cachedInputStateDecidableEq machine) T
              (advertisedBlockWidth alpha.offsets block)
              (rest.get cursor).exit (.completed final) = true
          · cases supplied with
            | some symbol =>
                have haccept' : @finiteCachedVisitPhaseAccept
                    (cachedInputMachine machine).State
                    (cachedInputStateDecidableEq machine) T
                    (advertisedBlockWidth alpha.offsets block)
                    rest[cursor.val].exit (.completed final) = true := by
                  simpa [List.get_eq_getElem] using haccept
                simp [haccept']
            | none =>
                have haccept' : @finiteCachedVisitPhaseAccept
                    (cachedInputMachine machine).State
                    (cachedInputStateDecidableEq machine) T
                    (advertisedBlockWidth alpha.offsets block)
                    rest[cursor.val].exit (.completed final) = true := by
                  simpa [List.get_eq_getElem] using haccept
                by_cases hnext : cursor.val + 1 < rest.length
                · simp [haccept', hnext,
                    finiteCachedBlockVisitListActiveState]
                · simp [haccept', hnext]
          · have haccept' : ¬ @finiteCachedVisitPhaseAccept
                (cachedInputMachine machine).State
                (cachedInputStateDecidableEq machine) T
                (advertisedBlockWidth alpha.offsets block)
                rest[cursor.val].exit (.completed final) = true := by
              simpa [List.get_eq_getElem] using haccept
            simp [haccept']

/-- Ordinary state-driven execution commutes exactly with the tail embedding
for every amount of microstep fuel. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_prepend
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (first : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hcons : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (htail : FixedAlphaBlockVisitEntriesInside alpha block rest)
    (fuel : Nat)
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) rest.length) :
    let consVerifier :=
      finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block initialSlab (first :: rest) hcons
    let tailVerifier :=
      finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block initialSlab rest htail
    consVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) fuel
        (prependFiniteCachedBlockVisitListState first rest state) =
      prependFiniteCachedBlockVisitListState first rest
        (tailVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index) fuel state) := by
  dsimp only
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [FiniteStreamingVerifier.inputDrivenCore]
      simp only [finiteCachedFixedAlphaBlockVisitListStreamingVerifier]
      rw [finiteCachedBlockVisitListHalted_prepend]
      by_cases hhalt : finiteCachedBlockVisitListHalted state = true
      · simp [hhalt]
      · have hhaltFalse : finiteCachedBlockVisitListHalted state = false := by
          cases h : finiteCachedBlockVisitListHalted state <;> simp_all
        simp only [hhaltFalse, Bool.false_eq_true, ↓reduceIte]
        simp only [finiteCachedBlockVisitListRequestsInput_prepend,
          finiteCachedBlockVisitListAdaptiveQueryIndex?_prepend]
        rw [finiteCachedBlockVisitListStreamingStep_prepend]
        exact ih _

/-- The empty-list base case is already globally completed, independently
of the supplied microstep fuel. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_empty
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block [])
    (fuel : Nat) :
    let verifier :=
      finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block initialSlab [] hentries
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) fuel verifier.start =
      .completed initialSlab := by
  dsimp only
  apply FiniteStreamingVerifier.inputDrivenCore_eq_self_of_halted
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
