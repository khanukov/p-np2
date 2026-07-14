import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksOuterCompiler
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaMultiVisitStateCount

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Embedding the dependent outer carrier in the homogeneous counted carrier

The executable all-block compiler keeps a dependent slab width and a
dependent visit-list length at its active block.  The state-count module uses
one homogeneous width `2 * b` and one uniform visit cursor `Fin (T + 1)`.
This file gives the missing explicit lossless encoding between those two
presentations, while simultaneously retaining the rolling two-window state.

The only hypotheses are the sharp geometric width bound (`0 < b`) and the
semantic fact that every block contains at most `T` positive-length visits.
No transition or acceptance theorem is asserted here: installing the rolling
counter update in the executable outer transition remains a separate task.
-/

/-- Outer all-block state paired with the rolling counter state, with one
global rejection sink.  Keeping rejection outside the product avoids storing
irrelevant counter data after failure. -/
inductive FiniteCachedAllBlocksWithFoldState
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) where
  | active (block : Fin (T / b + 1))
      (phase : FiniteCachedBlockVisitListStreamingState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length)
      (fold : InPlaceTwoWindowFoldState T b)
  | completed (fold : InPlaceTwoWindowFoldState T b)
  | rejected

/-- Encode one dependent fixed-block list phase into a uniform visit cursor
and a single padded visit phase.  Cursor `visits.length` is reserved for the
list terminal states; genuine active cursors are strictly smaller. -/
def encodeFiniteCachedBlockVisitListPhase
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hlength : visits.length <= T) :
    FiniteCachedBlockVisitListStreamingState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block) visits.length ->
      Fin (T + 1) ×
        FiniteCachedVisitStreamingState
          (cachedInputMachine machine).State T (2 * b)
  | .active cursor phase =>
      (⟨cursor.val, by omega⟩,
        padAdvertisedFiniteCachedVisitStreamingState hb alpha.offsets block
          phase)
  | .completed slab =>
      (⟨visits.length, by omega⟩,
        .completed
          { control := none
            inputHead := ⟨0, Nat.zero_lt_succ T⟩
            workHead := ⟨0, Nat.zero_lt_succ T⟩
            workSlab := padWorkSlab
              (advertisedBlockWidth_le_two_mul hb alpha.offsets block) slab })
  | .rejected =>
      (⟨visits.length, by omega⟩,
        .rejected .missingFreshInput)

/-- The dependent list phase is recovered losslessly from its uniform cursor
and padded phase. -/
theorem encodeFiniteCachedBlockVisitListPhase_injective
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hlength : visits.length <= T) :
    Function.Injective
      (encodeFiniteCachedBlockVisitListPhase machine hb alpha block visits
        hlength) := by
  intro left right heq
  cases left with
  | active leftCursor leftPhase =>
      cases right with
      | active rightCursor rightPhase =>
          have hcursorVal : leftCursor.val = rightCursor.val :=
            congrArg (fun encoded => encoded.1.val) heq
          have hcursor : leftCursor = rightCursor := Fin.ext hcursorVal
          subst rightCursor
          have hphase :
              padAdvertisedFiniteCachedVisitStreamingState hb alpha.offsets
                  block leftPhase =
                padAdvertisedFiniteCachedVisitStreamingState hb alpha.offsets
                  block rightPhase :=
            congrArg Prod.snd heq
          have := padAdvertisedFiniteCachedVisitStreamingState_injective
            hb alpha.offsets block hphase
          subst rightPhase
          rfl
      | completed rightSlab =>
          have hcursor : leftCursor.val = visits.length :=
            congrArg (fun encoded => encoded.1.val) heq
          omega
      | rejected =>
          have hcursor : leftCursor.val = visits.length :=
            congrArg (fun encoded => encoded.1.val) heq
          omega
  | completed leftSlab =>
      cases right with
      | active rightCursor rightPhase =>
          have hcursor : visits.length = rightCursor.val :=
            congrArg (fun encoded => encoded.1.val) heq
          omega
      | completed rightSlab =>
          have hphase := congrArg Prod.snd heq
          simp only [encodeFiniteCachedBlockVisitListPhase,
            FiniteCachedVisitStreamingState.completed.injEq,
            FiniteLocalFinalState.mk.injEq] at hphase
          have hslab := hphase.2.2.2
          have := padWorkSlab_injective
            (advertisedBlockWidth_le_two_mul hb alpha.offsets block) hslab
          subst rightSlab
          rfl
      | rejected =>
          have hphase := congrArg Prod.snd heq
          simp [encodeFiniteCachedBlockVisitListPhase] at hphase
  | rejected =>
      cases right with
      | active rightCursor rightPhase =>
          have hcursor : visits.length = rightCursor.val :=
            congrArg (fun encoded => encoded.1.val) heq
          omega
      | completed rightSlab =>
          have hphase := congrArg Prod.snd heq
          simp [encodeFiniteCachedBlockVisitListPhase] at hphase
      | rejected => rfl

/-- The code of a genuine list phase never uses the reserved global-completion
marker `(cursor = T, failure = zeroRemaining)`. -/
theorem encodeFiniteCachedBlockVisitListPhase_ne_globalCompleted
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hlength : visits.length <= T)
    (phase : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length) :
    encodeFiniteCachedBlockVisitListPhase machine hb alpha block visits
        hlength phase ≠
      (⟨T, Nat.lt_succ_self T⟩,
        .rejected .zeroRemaining) := by
  cases phase with
  | active cursor localPhase =>
      intro heq
      have hcursor : cursor.val = T :=
        congrArg (fun encoded => encoded.1.val) heq
      omega
  | completed slab =>
      intro heq
      have hphase := congrArg Prod.snd heq
      simp [encodeFiniteCachedBlockVisitListPhase] at hphase
  | rejected =>
      intro heq
      have hphase := congrArg Prod.snd heq
      simp [encodeFiniteCachedBlockVisitListPhase] at hphase

/-- Explicit encoding of the executable dependent outer carrier plus rolling
state into the homogeneous carrier whose cardinality was counted earlier. -/
def encodeFiniteCachedAllBlocksWithFoldState
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hlength : forall block, (blockVisits block).length <= T) :
    FiniteCachedAllBlocksWithFoldState machine alpha blockVisits ->
      FixedAlphaMultiVisitValidatorState machine T b
  | .rejected => .inl ()
  | .active block phase fold =>
      let encoded := encodeFiniteCachedBlockVisitListPhase machine hb alpha
        block (blockVisits block) (hlength block) phase
      .inr (block, encoded.1, encoded.2, fold)
  | .completed fold =>
      .inr
        (⟨0, Nat.zero_lt_succ (T / b)⟩,
          ⟨T, Nat.lt_succ_self T⟩,
          .rejected .zeroRemaining,
          fold)

/-- The whole outer-plus-fold carrier embeds losslessly in the homogeneous
counted carrier. -/
theorem encodeFiniteCachedAllBlocksWithFoldState_injective
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hlength : forall block, (blockVisits block).length <= T) :
    Function.Injective
      (encodeFiniteCachedAllBlocksWithFoldState machine hb alpha blockVisits
        hlength) := by
  intro left right heq
  cases left with
  | rejected =>
      cases right <;>
        simp [encodeFiniteCachedAllBlocksWithFoldState] at heq ⊢
  | completed leftFold =>
      cases right with
      | rejected =>
          simp [encodeFiniteCachedAllBlocksWithFoldState] at heq
      | completed rightFold =>
          have hfold := congrArg (fun encoded =>
            match encoded with
            | .inl _ => initialInPlaceTwoWindowFoldState T b
            | .inr fields => fields.2.2.2) heq
          have hfold' : leftFold = rightFold := by
            simpa [encodeFiniteCachedAllBlocksWithFoldState] using hfold
          subst rightFold
          rfl
      | active rightBlock rightPhase rightFold =>
          have hblock : rightBlock = ⟨0, Nat.zero_lt_succ (T / b)⟩ := by
            apply Fin.ext
            exact congrArg (fun encoded =>
              match encoded with
              | .inl _ => 0
              | .inr fields => fields.1.val) heq |>.symm
          subst rightBlock
          have hphase :
              encodeFiniteCachedBlockVisitListPhase machine hb alpha
                  ⟨0, Nat.zero_lt_succ (T / b)⟩
                  (blockVisits ⟨0, Nat.zero_lt_succ (T / b)⟩)
                  (hlength ⟨0, Nat.zero_lt_succ (T / b)⟩) rightPhase =
                (⟨T, Nat.lt_succ_self T⟩,
                  .rejected .zeroRemaining) := by
            apply Prod.ext
            · apply Fin.ext
              exact congrArg (fun encoded =>
                match encoded with
                | .inl _ => 0
                | .inr fields => fields.2.1.val) heq |>.symm
            · exact congrArg (fun encoded =>
                match encoded with
                | .inl _ =>
                    (FiniteCachedVisitStreamingState.rejected
                      .zeroRemaining)
                | .inr fields => fields.2.2.1) heq |>.symm
          exact (encodeFiniteCachedBlockVisitListPhase_ne_globalCompleted
            machine hb alpha ⟨0, Nat.zero_lt_succ (T / b)⟩
            (blockVisits ⟨0, Nat.zero_lt_succ (T / b)⟩)
            (hlength ⟨0, Nat.zero_lt_succ (T / b)⟩) rightPhase hphase).elim
  | active leftBlock leftPhase leftFold =>
      cases right with
      | rejected =>
          simp [encodeFiniteCachedAllBlocksWithFoldState] at heq
      | completed rightFold =>
          have hblock : leftBlock = ⟨0, Nat.zero_lt_succ (T / b)⟩ := by
            apply Fin.ext
            exact congrArg (fun encoded =>
              match encoded with
              | .inl _ => 0
              | .inr fields => fields.1.val) heq
          subst leftBlock
          have hphase :
              encodeFiniteCachedBlockVisitListPhase machine hb alpha
                  ⟨0, Nat.zero_lt_succ (T / b)⟩
                  (blockVisits ⟨0, Nat.zero_lt_succ (T / b)⟩)
                  (hlength ⟨0, Nat.zero_lt_succ (T / b)⟩) leftPhase =
                (⟨T, Nat.lt_succ_self T⟩,
                  .rejected .zeroRemaining) := by
            apply Prod.ext
            · apply Fin.ext
              exact congrArg (fun encoded =>
                match encoded with
                | .inl _ => 0
                | .inr fields => fields.2.1.val) heq
            · exact congrArg (fun encoded =>
                match encoded with
                | .inl _ =>
                    (FiniteCachedVisitStreamingState.rejected
                      .zeroRemaining)
                | .inr fields => fields.2.2.1) heq
          exact (encodeFiniteCachedBlockVisitListPhase_ne_globalCompleted
            machine hb alpha ⟨0, Nat.zero_lt_succ (T / b)⟩
            (blockVisits ⟨0, Nat.zero_lt_succ (T / b)⟩)
            (hlength ⟨0, Nat.zero_lt_succ (T / b)⟩) leftPhase hphase).elim
      | active rightBlock rightPhase rightFold =>
          have hblock : leftBlock = rightBlock := by
            apply Fin.ext
            exact congrArg (fun encoded =>
              match encoded with
              | .inl _ => 0
              | .inr fields => fields.1.val) heq
          subst rightBlock
          have hencoded :
              encodeFiniteCachedBlockVisitListPhase machine hb alpha leftBlock
                  (blockVisits leftBlock) (hlength leftBlock) leftPhase =
                encodeFiniteCachedBlockVisitListPhase machine hb alpha leftBlock
                  (blockVisits leftBlock) (hlength leftBlock) rightPhase := by
            apply Prod.ext
            · apply Fin.ext
              exact congrArg (fun encoded =>
                match encoded with
                | .inl _ => 0
                | .inr fields => fields.2.1.val) heq
            · exact congrArg (fun encoded =>
                match encoded with
                | .inl _ =>
                    (FiniteCachedVisitStreamingState.rejected
                      .zeroRemaining)
                | .inr fields => fields.2.2.1) heq
          have hphase := encodeFiniteCachedBlockVisitListPhase_injective
            machine hb alpha leftBlock (blockVisits leftBlock)
            (hlength leftBlock) hencoded
          subst rightPhase
          have hfold := congrArg (fun encoded =>
            match encoded with
            | .inl _ => initialInPlaceTwoWindowFoldState T b
            | .inr fields => fields.2.2.2) heq
          have hfold' : leftFold = rightFold := by
            simpa [encodeFiniteCachedAllBlocksWithFoldState] using hfold
          subst rightFold
          rfl

/-- Timed schedule validity supplies the visit-count hypothesis required by
the embedding. -/
theorem timedAlphaSchedule_blockVisits_length_le_horizon
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    forall block,
      (timedAlphaBlockVisits block scheduled).length <= T := by
  intro block
  exact le_trans
    (fixedAlphaBlockVisits_length_le_totalSteps
      (timedAlphaBlockVisits block scheduled))
    (hschedule.blockVisitsTotalSteps_le_horizon
      (cachedInputMachine machine) block)

/-- A valid timed schedule therefore has a first-class embedding into the
previously counted homogeneous multi-visit carrier. -/
def finiteCachedTimedAlphaScheduleWithFoldEmbedding
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    FiniteCachedAllBlocksWithFoldState machine alpha
        (fun block => timedAlphaBlockVisits block scheduled) ↪
      FixedAlphaMultiVisitValidatorState machine T b where
  toFun := encodeFiniteCachedAllBlocksWithFoldState machine hb alpha
    (fun block => timedAlphaBlockVisits block scheduled)
    (timedAlphaSchedule_blockVisits_length_le_horizon machine alpha scheduled
      hschedule)
  inj' := encodeFiniteCachedAllBlocksWithFoldState_injective machine hb alpha
    (fun block => timedAlphaBlockVisits block scheduled)
    (timedAlphaSchedule_blockVisits_length_le_horizon machine alpha scheduled
      hschedule)

end OneTapeMagnification
end Frontier
end Pnp4
