import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AcceptedMasterOrderExecution
import Pnp4.Frontier.OneTapeMagnification.GuardedFiniteCachedAllBlocksReadOnce

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Accepted all-block execution follows the static master order

This module composes the exact accepted fixed-block query traces through the
finite all-block outer verifier.  Each local trace is mapped into the dependent
outer state, its silent block boundary is appended, and the construction is
iterated through the remaining finite block suffix.  The resulting raw outer
query trace is the schedule-fixed grouped master order on the canonical input.
-/

local instance cachedInputMachineStateDecidableEqForAcceptedAllBlocksMaster
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Advertised coordinate order of the suffix of blocks beginning at the
natural block cursor `start`. -/
def finiteCachedAllBlocksAdvertisedQueryOrderFrom
    {State : Type} {n T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) (start : Nat) : List (Fin n) :=
  ((List.finRange (T / b + 1)).drop start).flatMap fun block =>
    finiteCachedBlockVisitListAdvertisedQueryOrder n (blockVisits block)

@[simp]
theorem finiteCachedAllBlocksAdvertisedQueryOrderFrom_all
    {State : Type} {n T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) :
    finiteCachedAllBlocksAdvertisedQueryOrderFrom
        (n := n) blockVisits (T / b + 1) = [] := by
  unfold finiteCachedAllBlocksAdvertisedQueryOrderFrom
  have hdrop : (List.finRange (T / b + 1)).drop (T / b + 1) = [] := by
    simp
  rw [hdrop]
  rfl

/-- Dropping one in-range block exposes its advertised local order followed by
the successor suffix. -/
theorem finiteCachedAllBlocksAdvertisedQueryOrderFrom_eq_cons
    {State : Type} {n T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T))
    (start : Nat) (hstart : start < T / b + 1) :
    finiteCachedAllBlocksAdvertisedQueryOrderFrom
        (n := n) blockVisits start =
      finiteCachedBlockVisitListAdvertisedQueryOrder n
          (blockVisits ⟨start, hstart⟩) ++
        finiteCachedAllBlocksAdvertisedQueryOrderFrom
          (n := n) blockVisits (start + 1) := by
  unfold finiteCachedAllBlocksAdvertisedQueryOrderFrom
  rw [List.drop_eq_getElem_cons (by simpa using hstart)]
  simp only [List.flatMap_cons]
  congr 1
  apply congrArg (fun block =>
    finiteCachedBlockVisitListAdvertisedQueryOrder n (blockVisits block))
  simp

/-- Remaining all-block microstep budget after the first `start` complete
block budgets. -/
def finiteCachedAllBlocksSuffixFuel
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) (start : Nat) : Nat :=
  finiteCachedAllBlocksFuel blockVisits -
    finiteCachedAllBlocksPrefixFuel blockVisits start

@[simp]
theorem finiteCachedAllBlocksSuffixFuel_all
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) :
    finiteCachedAllBlocksSuffixFuel blockVisits (T / b + 1) = 0 := by
  simp [finiteCachedAllBlocksSuffixFuel,
    finiteCachedAllBlocksPrefixFuel_all]

theorem finiteCachedAllBlocksPrefixFuel_le_all
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) (count : Nat) :
    finiteCachedAllBlocksPrefixFuel blockVisits count ≤
      finiteCachedAllBlocksFuel blockVisits := by
  unfold finiteCachedAllBlocksPrefixFuel finiteCachedAllBlocksFuel
  apply Finset.sum_le_sum
  intro block _
  split <;> omega

/-- Suffix fuel peels off the current block's exact list budget and its one
silent boundary step. -/
theorem finiteCachedAllBlocksSuffixFuel_eq_current_add
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T))
    (start : Nat) (hstart : start < T / b + 1) :
    finiteCachedAllBlocksSuffixFuel blockVisits start =
      (finiteCachedBlockVisitListFuel (blockVisits ⟨start, hstart⟩) + 1) +
        finiteCachedAllBlocksSuffixFuel blockVisits (start + 1) := by
  have hprefix := finiteCachedAllBlocksPrefixFuel_succ
    blockVisits start hstart
  have hle := finiteCachedAllBlocksPrefixFuel_le_all
    blockVisits (start + 1)
  unfold finiteCachedAllBlocksSuffixFuel
  omega

/-- Map one exact fixed-block trace into the dependent outer verifier and
append an arbitrary exact continuation beginning at the lifted local terminal
state. -/
theorem finiteCachedBlockVisitListExactAdaptiveQueryOrder_map_append_outer
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    {firstSteps : Nat}
    {firstQueries : List (Fin input.length)}
    {middle : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block)
      (blockVisits block).length}
    (first :
      let source := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) (hentries block)
      FiniteStreamingVerifier.ExactAdaptiveQueryOrder source
        (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) firstSteps source.start
        firstQueries middle)
    {secondSteps : Nat} {secondQueries : List (Fin input.length)}
    {final : FiniteCachedTimedAlphaAllBlocksStreamingState
      machine alpha blockVisits}
    (second :
      let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
        machine input.length alpha blockVisits
      FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
        (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) secondSteps
        (liftFiniteCachedAllBlocksPhase machine block middle)
        secondQueries final) :
    let source := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
      (fun bit => .bit bit)
      (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) (firstSteps + secondSteps)
      (liftFiniteCachedAllBlocksPhase machine block source.start)
      (firstQueries ++ secondQueries) final := by
  dsimp only at first second ⊢
  let source := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits block) (hentries block)
  let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let sourceSelector : source.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let outerSelector : outer.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  let embed : source.State -> outer.State :=
    liftFiniteCachedAllBlocksPhase machine block
  have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true :=
    (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
      alpha blockVisits).2 hentries
  have hhalted : ∀ state, source.halted state = false →
      outer.halted (embed state) = false := by
    intro state hlive
    cases state with
    | active cursor phase => rfl
    | completed slab =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
    | rejected =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
  have hrequests : ∀ state, source.halted state = false →
      outer.requestsInput (embed state) = source.requestsInput state := by
    intro state hlive
    cases state with
    | active cursor phase => rfl
    | completed slab =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
    | rejected =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
  have hselector : ∀ state, source.halted state = false →
      outerSelector (embed state) = sourceSelector state := by
    intro state hlive
    cases state with
    | active cursor phase => rfl
    | completed slab =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
    | rejected =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
  have hstep : ∀ state supplied, source.halted state = false →
      outer.step (embed state) supplied =
        embed (source.step state supplied) := by
    intro state supplied hlive
    cases state with
    | active cursor phase =>
        simp [outer, source, embed,
          finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
          finiteCachedAllBlocksTotalStreamingStep, hcheck,
          finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedAllBlocksStreamingStep,
          liftFiniteCachedAllBlocksPhase]
    | completed slab =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
    | rejected =>
        simp [source, finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted] at hlive
  exact FiniteStreamingVerifier.ExactAdaptiveQueryOrder.map_append
    source outer (fun bit => .bit bit) sourceSelector outerSelector inputBits
    embed hhalted hrequests hselector hstep first second

/-- Exact accepted execution of every block in the suffix beginning at
`start`.  The microstep count is the exact remaining outer budget, and the
coordinate list is the concatenation of the advertised per-block orders. -/
theorem finiteCachedAllBlocks_exactAdaptiveQueryOrder_from_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block))
    (tail start : Nat) (hstart : start < T / b + 1)
    (hspan : start + (tail + 1) = T / b + 1) :
    let block : Fin (T / b + 1) := ⟨start, hstart⟩
    let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
      (fun bit => .bit bit)
      (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index)
      (finiteCachedAllBlocksSuffixFuel blockVisits start)
      (.active block listVerifier.start)
      (finiteCachedAllBlocksAdvertisedQueryOrderFrom
        (n := input.length) blockVisits start)
      .completed := by
  induction tail generalizing start with
  | zero =>
      let block : Fin (T / b + 1) := ⟨start, hstart⟩
      let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) (hentries block)
      let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
        machine input.length alpha blockVisits
      have hcertificate :=
        (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
          machine input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block)).2 (haccepted block)
      obtain ⟨finalSlab, localTrace⟩ :=
        finiteCachedBlockVisitList_exactAdaptiveQueryOrder_of_certificate
          machine input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) (hentries block) hcertificate
      have hlast : ¬ block.val + 1 < T / b + 1 := by
        dsimp [block]
        omega
      have terminal : FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
          (fun bit => .bit bit)
          (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index) 0 .completed [] .completed := by
        apply FiniteStreamingVerifier.ExactAdaptiveQueryOrder.halted
        rfl
      have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
            alpha blockVisits = true :=
        (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
          alpha blockVisits).2 hentries
      have hboundaryStep : outer.step
          (.active block (.completed finalSlab)) none = .completed := by
        have hstep := finiteCachedAllBlocksStreamingStep_completed_last
          machine input.length alpha blockVisits hentries block finalSlab hlast
        simpa [outer,
          finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
          finiteCachedAllBlocksTotalStreamingStep, hcheck] using hstep
      have boundary : FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
          (fun bit => .bit bit)
          (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index) 1
          (.active block (.completed finalSlab)) [] .completed := by
        apply FiniteStreamingVerifier.ExactAdaptiveQueryOrder.silent
        · rfl
        · rfl
        · rw [hboundaryStep]
          exact terminal
      have combined :=
        finiteCachedBlockVisitListExactAdaptiveQueryOrder_map_append_outer
          machine input alpha blockVisits hentries block localTrace boundary
      have hsuffix := finiteCachedAllBlocksSuffixFuel_eq_current_add
        blockVisits start hstart
      have horder := finiteCachedAllBlocksAdvertisedQueryOrderFrom_eq_cons
        (n := input.length) blockVisits start hstart
      have hsuffixNext : finiteCachedAllBlocksSuffixFuel blockVisits
          (start + 1) = 0 := by
        rw [show start + 1 = T / b + 1 by omega]
        exact finiteCachedAllBlocksSuffixFuel_all blockVisits
      have hnextEq : start + 1 = T / b + 1 := by omega
      have hliftStart : liftFiniteCachedAllBlocksPhase machine block
          listVerifier.start = .active block listVerifier.start := by
        dsimp [listVerifier,
          finiteCachedFixedAlphaBlockVisitListStreamingVerifier]
        unfold finiteCachedBlockVisitListStart
        split <;> rfl
      dsimp only at combined ⊢
      rw [hliftStart] at combined
      rw [hsuffix, horder, hsuffixNext, hnextEq]
      simpa [block, listVerifier, outer, Nat.add_assoc] using combined
  | succ tail ih =>
      let block : Fin (T / b + 1) := ⟨start, hstart⟩
      have hnext : start + 1 < T / b + 1 := by omega
      let next : Fin (T / b + 1) := ⟨start + 1, hnext⟩
      let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) (hentries block)
      let nextVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha next
        (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
        (blockVisits next) (hentries next)
      let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
        machine input.length alpha blockVisits
      have hcertificate :=
        (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
          machine input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block)).2 (haccepted block)
      obtain ⟨finalSlab, localTrace⟩ :=
        finiteCachedBlockVisitList_exactAdaptiveQueryOrder_of_certificate
          machine input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) (hentries block) hcertificate
      have rest := ih (start + 1) hnext (by omega)
      have rest' : FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
          (fun bit => .bit bit)
          (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index)
          (finiteCachedAllBlocksSuffixFuel blockVisits (start + 1))
          (.active next nextVerifier.start)
          (finiteCachedAllBlocksAdvertisedQueryOrderFrom
            (n := input.length) blockVisits (start + 1))
          .completed := by
        simpa [next, nextVerifier, outer] using rest
      have hnextBlock : block.val + 1 < T / b + 1 := by
        simpa [block] using hnext
      have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
            alpha blockVisits = true :=
        (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
          alpha blockVisits).2 hentries
      have hboundaryStep : outer.step
          (.active block (.completed finalSlab)) none =
            .active next nextVerifier.start := by
        have hstep := finiteCachedAllBlocksStreamingStep_completed_next
          machine input.length alpha blockVisits hentries block finalSlab
            hnextBlock
        simpa [outer, block, next, nextVerifier,
          finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
          finiteCachedAllBlocksTotalStreamingStep, hcheck] using hstep
      have boundary : FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
          (fun bit => .bit bit)
          (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index)
          (finiteCachedAllBlocksSuffixFuel blockVisits (start + 1) + 1)
          (.active block (.completed finalSlab))
          (finiteCachedAllBlocksAdvertisedQueryOrderFrom
            (n := input.length) blockVisits (start + 1))
          .completed := by
        apply FiniteStreamingVerifier.ExactAdaptiveQueryOrder.silent
        · rfl
        · rfl
        · rw [hboundaryStep]
          exact rest'
      have combined :=
        finiteCachedBlockVisitListExactAdaptiveQueryOrder_map_append_outer
          machine input alpha blockVisits hentries block localTrace boundary
      have hsuffix := finiteCachedAllBlocksSuffixFuel_eq_current_add
        blockVisits start hstart
      have horder := finiteCachedAllBlocksAdvertisedQueryOrderFrom_eq_cons
        (n := input.length) blockVisits start hstart
      have hliftStart : liftFiniteCachedAllBlocksPhase machine block
          listVerifier.start = .active block listVerifier.start := by
        dsimp [listVerifier,
          finiteCachedFixedAlphaBlockVisitListStreamingVerifier]
        unfold finiteCachedBlockVisitListStart
        split <;> rfl
      dsimp only at combined ⊢
      rw [hliftStart] at combined
      rw [hsuffix, horder]
      simpa [block, listVerifier, outer, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using combined

/-- Accepted replay in every advertised block gives one exact global trace
from the total verifier's literal start state to global completion. -/
theorem finiteCachedAllBlocks_exactAdaptiveQueryOrder_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)) :
    let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
      (fun bit => .bit bit)
      (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index)
      (finiteCachedAllBlocksFuel blockVisits) outer.start
      ((List.finRange (T / b + 1)).flatMap fun block =>
        finiteCachedBlockVisitListAdvertisedQueryOrder
          input.length (blockVisits block))
      .completed := by
  let hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits :=
    fun block => fixedAlphaBlockVisitEntriesInside_of_replayAccepted
      (cachedInputMachine machine) input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (haccepted block)
  have htrace :=
    finiteCachedAllBlocks_exactAdaptiveQueryOrder_from_replayAccepted
      machine input alpha blockVisits hentries haccepted (T / b) 0
        (Nat.zero_lt_succ _) (by omega)
  have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
        alpha blockVisits = true :=
    (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
      alpha blockVisits).2 hentries
  dsimp only at htrace ⊢
  simpa [finiteCachedAllBlocksSuffixFuel,
    finiteCachedAllBlocksAdvertisedQueryOrderFrom,
    finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
    finiteCachedAllBlocksTotalStart, hcheck, finiteCachedAllBlocksStart]
    using htrace

/-- The compiled total outer verifier exposes exactly the concatenation of
the accepted blocks' advertised query orders. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_queryTrace_eq_blockVisits_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal
      (n := input.length) machine alpha blockVisits).queryTrace
        (fun index => input.get index) =
      (List.finRange (T / b + 1)).flatMap (fun block =>
        finiteCachedBlockVisitListAdvertisedQueryOrder
          input.length (blockVisits block)) := by
  let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : outer.State → Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  have htrace := finiteCachedAllBlocks_exactAdaptiveQueryOrder_of_replayAccepted
    machine input alpha blockVisits haccepted
  dsimp only at htrace
  have hqueryTrace := htrace.compileAdaptive_queryTrace_eq outer
    (fun bit => .bit bit) .rightEnd selector inputBits le_rfl
  simpa [compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal,
    outer, selector, inputBits] using hqueryTrace

/-- For the schedule specialization, accepted block replays identify the raw
compiled trace with the static grouped master order. -/
theorem compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_queryTrace_eq_master_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    let hmonotone :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        (cachedInputMachine machine) input alpha scheduled haccepted
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      (n := input.length) machine alpha scheduled).queryTrace
        (fun index => input.get index) =
      finiteCachedTimedAlphaScheduleMasterQueryOrder
        scheduled hmonotone := by
  dsimp only
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) input alpha scheduled haccepted
  have hreplay : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (timedAlphaBlockVisits block scheduled) := by
    intro block
    exact (haccepted block).2
  have htrace :=
    compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_queryTrace_eq_blockVisits_of_replayAccepted
      machine input alpha (fun block => timedAlphaBlockVisits block scheduled)
        hreplay
  have hmaster := finiteCachedTimedAlphaScheduleMasterQueryOrder_eq_blockVisits
    (n := input.length) scheduled hmonotone
  simpa [compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks, hmonotone]
    using htrace.trans hmaster.symm

/-- Accepted schedule semantics now discharges the guarded compiler's former
`follows-master` premise on the canonical finite input. -/
theorem finiteCachedTimedAlphaScheduleExecutionQueriesFollowMaster_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    let hmonotone :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        (cachedInputMachine machine) input alpha scheduled haccepted
    FiniteCachedTimedAlphaScheduleExecutionQueriesFollowMaster
      machine alpha scheduled hmonotone (fun index => input.get index) := by
  dsimp only
  apply LayeredQueryProgram.executionQueriesFollowMaster_of_queryTrace_eq
  exact
    compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_queryTrace_eq_master_of_acceptedFromBlank
      machine input alpha scheduled haccepted

/-- On the canonical finite input, a valid accepted schedule makes the total
master guard observationally invisible, with no separate operational premise. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_base_of_valid_acceptedFromBlank_canonical
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
        (n := input.length) machine alpha scheduled).eval
          (fun index => input.get index) := by
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) input alpha scheduled haccepted
  apply
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_base_of_follows
      machine alpha scheduled (fun index => input.get index) hschedule hmonotone
  simpa [hmonotone] using
    finiteCachedTimedAlphaScheduleExecutionQueriesFollowMaster_of_acceptedFromBlank
      machine input alpha scheduled haccepted

/-- Completeness of the total guarded schedule compiler on the canonical input
now needs only schedule validity and the semantic per-block acceptance
certificate; the former `hreflect` and `hfollows` parameters are eliminated. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_true_of_valid_acceptedFromBlank_canonical
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) = true := by
  rw [compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_base_of_valid_acceptedFromBlank_canonical
    machine input alpha scheduled hschedule haccepted]
  have hbase :=
    compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval_eq_true_of_acceptedFromBlank
      machine input alpha (fun block => timedAlphaBlockVisits block scheduled)
        haccepted
  simpa [compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks] using hbase

end OneTapeMagnification
end Frontier
end Pnp4
