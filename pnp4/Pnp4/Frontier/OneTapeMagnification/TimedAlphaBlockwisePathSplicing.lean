import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AcceptedMasterOrderExecution
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSoundness
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksReadOnce

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Blockwise path splicing for one fixed timed alpha

For a valid timed-alpha schedule, the accepted adaptive trace of each fixed
work-block replay is already known exactly: it is the static concatenation of
the fresh input intervals advertised by that block's visits.  Different
blocks occupy disjoint pieces of the schedule's grouped master order.

This file proves the first cross-input consequence.  Choose, independently
for each work block, an input on which that block's replay is accepted.  Any
candidate input agreeing with the chosen source on that block's advertised
query path makes every block replay accept simultaneously.  The proof uses
the path-cylinder theorem for layered programs and the existing exact
compiler semantics; it does not assume a new replay or rectangle property.

The conclusion is deliberately the all-block local replay predicate.  It does
not yet assert that the candidate has the same canonical cut offsets.  That
next step must preserve the replayed leftmost-minimum crossing counters; local
product closure alone is insufficient to hide that obligation.
-/

/-- Coordinatewise agreement with one source on the static advertised query
order of a named work block. -/
def TimedAlphaBlockAdvertisedAgreement
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (block : Fin (T / b + 1))
    (source candidate : Fin n → Bool) : Prop :=
  ∀ coordinate ∈ finiteCachedBlockVisitListAdvertisedQueryOrder n
      (timedAlphaBlockVisits block scheduled),
    candidate coordinate = source coordinate

/-- View a list of a certified length as a Boolean assignment on that fixed
finite coordinate type. -/
private def inputViewAtLength {n : Nat} (input : List Bool)
    (hlength : input.length = n) : Fin n → Bool :=
  fun coordinate => input.get (Fin.cast hlength.symm coordinate)

private theorem compileBlockList_eval_eq_true_iff_replayAccepted_atLength
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (input : List Bool) (hlength : input.length = n)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList
        (n := n) machine alpha block initialSlab visits hentries).eval
        (inputViewAtLength input hlength) = true ↔
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block initialSlab visits := by
  subst n
  simpa [inputViewAtLength] using
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval_eq_true_iff_replayAccepted
      machine input alpha block initialSlab visits hentries)

private theorem compileBlockList_queryTrace_eq_advertised_atLength
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (input : List Bool) (hlength : input.length = n)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList
        (n := n) machine alpha block initialSlab visits hentries).queryTrace
        (inputViewAtLength input hlength) =
      finiteCachedBlockVisitListAdvertisedQueryOrder n visits := by
  subst n
  simpa [inputViewAtLength] using
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_queryTrace_eq_advertised_of_replayAccepted
      machine input alpha block initialSlab visits hentries haccepted)

/-- One-block cross-input path cylinder.  An accepted fixed-block replay is
preserved by changing arbitrary input coordinates outside its exact
advertised query order. -/
theorem fixedAlphaBlockVisitReplayAccepted_of_advertisedAgreement
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (source candidate : Fin n → Bool)
    (hsource : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) (List.ofFn source) alpha block
        initialSlab visits)
    (hagreement : ∀ coordinate ∈
      finiteCachedBlockVisitListAdvertisedQueryOrder n visits,
        candidate coordinate = source coordinate) :
    FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) (List.ofFn candidate) alpha block
        initialSlab visits := by
  let sourceInput := List.ofFn source
  let candidateInput := List.ofFn candidate
  have hsourceLength : sourceInput.length = n := by
    simp [sourceInput]
  have hcandidateLength : candidateInput.length = n := by
    simp [candidateInput]
  have hsourceReplay : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) sourceInput alpha block initialSlab
      visits := by
    simpa [sourceInput] using hsource
  let hentries : FixedAlphaBlockVisitEntriesInside alpha block visits :=
    fixedAlphaBlockVisitEntriesInside_of_replayAccepted
      (cachedInputMachine machine) sourceInput alpha block initialSlab visits
        hsourceReplay
  let program := compileAdaptiveFiniteCachedFixedAlphaBlockVisitList
    (n := n) machine alpha block initialSlab visits hentries
  have hsourceView : inputViewAtLength sourceInput hsourceLength = source := by
    funext coordinate
    simp [inputViewAtLength, sourceInput]
  have hcandidateView :
      inputViewAtLength candidateInput hcandidateLength = candidate := by
    funext coordinate
    simp [inputViewAtLength, candidateInput]
  have hsourceEval : program.eval source = true := by
    have hcorrect :=
      (compileBlockList_eval_eq_true_iff_replayAccepted_atLength
        machine sourceInput hsourceLength alpha block initialSlab visits
          hentries).2 hsourceReplay
    simpa [program, hsourceView] using hcorrect
  have hsourceTrace : program.queryTrace source =
      finiteCachedBlockVisitListAdvertisedQueryOrder n visits := by
    have htrace :=
      compileBlockList_queryTrace_eq_advertised_atLength
        machine sourceInput hsourceLength alpha block initialSlab visits
          hentries hsourceReplay
    simpa [program, hsourceView] using htrace
  have hpathAgreement : program.InputsAgreeOnQueryTrace source candidate := by
    intro coordinate hcoordinate
    apply hagreement coordinate
    simpa [hsourceTrace] using hcoordinate
  have hcandidateEval : program.eval candidate = true := by
    rw [program.eval_eq_of_inputsAgreeOnQueryTrace
      source candidate hpathAgreement]
    exact hsourceEval
  have hcorrect :=
    (compileBlockList_eval_eq_true_iff_replayAccepted_atLength
      machine candidateInput hcandidateLength alpha block initialSlab visits
        hentries).1 (by
          simpa [program, hcandidateView] using hcandidateEval)
  exact hcorrect

/-- Exact cross-input transfer for all fixed-block local replays.

Each block may use a different source input.  The only candidate/source
agreement required is on that block's already-proved accepted query path.
Schedule validity supplies the input-independent chronological clauses. -/
theorem allFixedAlphaBlockVisitListsAcceptedFromBlank_of_blockwise_pathAgreement
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (sources : Fin (T / b + 1) → Fin n → Bool)
    (candidate : Fin n → Bool)
    (hsources : ∀ block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) (List.ofFn (sources block)) alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (timedAlphaBlockVisits block scheduled))
    (hagrees : ∀ block : Fin (T / b + 1),
      TimedAlphaBlockAdvertisedAgreement scheduled block
        (sources block) candidate) :
    AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn candidate) alpha scheduled := by
  intro block
  exact ⟨hschedule.blockVisitsChronological
      (cachedInputMachine machine) block,
    fixedAlphaBlockVisitReplayAccepted_of_advertisedAgreement
      machine alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (timedAlphaBlockVisits block scheduled) (sources block) candidate
        (hsources block) (hagrees block)⟩

/-- Extract disjointness of two distinct fibers from a pairwise-disjoint
index list.  This small helper avoids imposing an order on the two indices. -/
private theorem pairwiseOnDisjoint_of_mem_ne
    {Index Coordinate : Type}
    {indices : List Index} {coordinates : Index → List Coordinate}
    (hpairwise : indices.Pairwise
      (Function.onFun List.Disjoint coordinates))
    {left right : Index}
    (hleft : left ∈ indices) (hright : right ∈ indices)
    (hne : left ≠ right) :
    (coordinates left).Disjoint (coordinates right) := by
  induction indices generalizing left right with
  | nil =>
      simp at hleft
  | cons head tail ih =>
      rw [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · exact False.elim (hne rfl)
        · exact hpairwise.1 right hright
      · rcases hright with rfl | hright
        · exact (hpairwise.1 left hleft).symm
        · exact ih hpairwise.2 hleft hright hne

/-- Replace exactly the advertised coordinates owned by `selected` with the
corresponding bits of `donor`, leaving every other coordinate at `base`. -/
def finiteCachedTimedAlphaSingleBlockSplice
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (selected : Fin (T / b + 1))
    (donor base : Fin n → Bool) : Fin n → Bool :=
  fun coordinate =>
    if coordinate ∈ finiteCachedBlockVisitListAdvertisedQueryOrder n
        (timedAlphaBlockVisits selected scheduled) then
      donor coordinate
    else
      base coordinate

@[simp] theorem finiteCachedTimedAlphaSingleBlockSplice_eq_donor
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (selected : Fin (T / b + 1))
    (donor base : Fin n → Bool) (coordinate : Fin n)
    (hcoordinate : coordinate ∈
      finiteCachedBlockVisitListAdvertisedQueryOrder n
        (timedAlphaBlockVisits selected scheduled)) :
    finiteCachedTimedAlphaSingleBlockSplice scheduled selected donor base
        coordinate = donor coordinate := by
  simp [finiteCachedTimedAlphaSingleBlockSplice, hcoordinate]

@[simp] theorem finiteCachedTimedAlphaSingleBlockSplice_eq_base
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (selected : Fin (T / b + 1))
    (donor base : Fin n → Bool) (coordinate : Fin n)
    (hcoordinate : coordinate ∉
      finiteCachedBlockVisitListAdvertisedQueryOrder n
        (timedAlphaBlockVisits selected scheduled)) :
    finiteCachedTimedAlphaSingleBlockSplice scheduled selected donor base
        coordinate = base coordinate := by
  simp [finiteCachedTimedAlphaSingleBlockSplice, hcoordinate]

/-- **Unconditional one-block path splice.**

Two inputs that realize every local replay for the same timed alpha may be
hybridized by taking one advertised block path from the donor and all other
coordinates from the base.  The hybrid still realizes every block replay.
The required separation of block coordinates is derived from schedule
chaining plus accepted-run input monotonicity; it is not a premise. -/
theorem allFixedAlphaBlockVisitListsAcceptedFromBlank_singleBlockSplice
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (selected : Fin (T / b + 1))
    (donor base : Fin n → Bool)
    (hdonor : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn donor) alpha scheduled)
    (hbase : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn base) alpha scheduled) :
    AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine)
      (List.ofFn (finiteCachedTimedAlphaSingleBlockSplice
        scheduled selected donor base)) alpha scheduled := by
  let blockOrder : Fin (T / b + 1) → List (Fin n) := fun block =>
    finiteCachedBlockVisitListAdvertisedQueryOrder n
      (timedAlphaBlockVisits block scheduled)
  have hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) (List.ofFn base) alpha scheduled hbase
  have hscheduleForTransfer := hschedule
  obtain ⟨_syntactic, _finalCursor, _visitsSoFar, _hfold, _hfinish,
    hchained⟩ := hschedule
  have hmasterNodup :
      (finiteCachedTimedAlphaScheduleMasterQueryOrder
        (n := n) scheduled hmonotone).Nodup :=
    finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
      scheduled hchained hmonotone
  have hflatNodup :
      ((List.finRange (T / b + 1)).flatMap blockOrder).Nodup := by
    rw [← finiteCachedTimedAlphaScheduleMasterQueryOrder_eq_blockVisits
      (n := n) scheduled hmonotone]
    exact hmasterNodup
  have hpairwise : (List.finRange (T / b + 1)).Pairwise
      (Function.onFun List.Disjoint blockOrder) :=
    (List.nodup_flatMap.mp hflatNodup).2
  let sources : Fin (T / b + 1) → Fin n → Bool := fun block =>
    if block = selected then donor else base
  apply
    allFixedAlphaBlockVisitListsAcceptedFromBlank_of_blockwise_pathAgreement
      machine alpha scheduled hscheduleForTransfer sources
        (finiteCachedTimedAlphaSingleBlockSplice
          scheduled selected donor base)
  · intro block
    by_cases hblock : block = selected
    · subst block
      simpa [sources] using hdonor selected |>.2
    · simpa [sources, hblock] using hbase block |>.2
  · intro block coordinate hcoordinate
    by_cases hblock : block = selected
    · subst block
      simp [sources, finiteCachedTimedAlphaSingleBlockSplice,
        hcoordinate]
    · have hdisjoint : (blockOrder block).Disjoint
          (blockOrder selected) :=
        pairwiseOnDisjoint_of_mem_ne hpairwise
          (List.mem_finRange block) (List.mem_finRange selected) hblock
      have hnotSelected : coordinate ∉ blockOrder selected :=
        (List.disjoint_left.mp hdisjoint) hcoordinate
      simp [sources, hblock, finiteCachedTimedAlphaSingleBlockSplice,
        blockOrder, hnotSelected]

/-- Iterate single-block splicing over an explicit block list.  Repeated
coordinates would merely be overwritten; the accepted-schedule theorem below
uses the duplicate-free canonical `finRange` traversal. -/
def finiteCachedTimedAlphaBlockSpliceFold
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (sources : Fin (T / b + 1) → Fin n → Bool) :
    List (Fin (T / b + 1)) → (Fin n → Bool) → Fin n → Bool
  | [], base => base
  | block :: blocks, base =>
      finiteCachedTimedAlphaBlockSpliceFold scheduled sources blocks
        (finiteCachedTimedAlphaSingleBlockSplice
          scheduled block (sources block) base)

/-- The concrete all-block splice: traverse every advertised block once and
install the path bits of that block's chosen source.  Coordinates outside the
schedule master order retain the fallback value. -/
def finiteCachedTimedAlphaAllBlockSplice
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (sources : Fin (T / b + 1) → Fin n → Bool)
    (fallback : Fin n → Bool) : Fin n → Bool :=
  finiteCachedTimedAlphaBlockSpliceFold scheduled sources
    (List.finRange (T / b + 1)) fallback

/-- Every finite sequence of same-alpha block replacements preserves all
local replays, provided each donor and the starting base realize that same
schedule. -/
theorem allFixedAlphaBlockVisitListsAcceptedFromBlank_blockSpliceFold
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (sources : Fin (T / b + 1) → Fin n → Bool)
    (hsources : ∀ block : Fin (T / b + 1),
      AllFixedAlphaBlockVisitListsAcceptedFromBlank
        (cachedInputMachine machine) (List.ofFn (sources block))
          alpha scheduled)
    (blocks : List (Fin (T / b + 1)))
    (base : Fin n → Bool)
    (hbase : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn base) alpha scheduled) :
    AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine)
      (List.ofFn (finiteCachedTimedAlphaBlockSpliceFold
        scheduled sources blocks base)) alpha scheduled := by
  induction blocks generalizing base with
  | nil =>
      simpa [finiteCachedTimedAlphaBlockSpliceFold] using hbase
  | cons block blocks ih =>
      apply ih
      exact allFixedAlphaBlockVisitListsAcceptedFromBlank_singleBlockSplice
        machine alpha scheduled hschedule block (sources block) base
          (hsources block) hbase

/-- **Unconditional rectangular closure of the advertised replay fiber.**

For each work block choose an arbitrary input realizing the same valid timed
alpha schedule.  Splicing all of their advertised path bits into any other
realizing fallback input again realizes every local block replay.  This is
the exact product-fiber statement available before proving stability of the
global leftmost-cut check. -/
theorem allFixedAlphaBlockVisitListsAcceptedFromBlank_allBlockSplice
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (sources : Fin (T / b + 1) → Fin n → Bool)
    (fallback : Fin n → Bool)
    (hsources : ∀ block : Fin (T / b + 1),
      AllFixedAlphaBlockVisitListsAcceptedFromBlank
        (cachedInputMachine machine) (List.ofFn (sources block))
          alpha scheduled)
    (hfallback : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn fallback) alpha scheduled) :
    AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine)
      (List.ofFn (finiteCachedTimedAlphaAllBlockSplice
        scheduled sources fallback)) alpha scheduled := by
  exact allFixedAlphaBlockVisitListsAcceptedFromBlank_blockSpliceFold
    machine alpha scheduled hschedule sources hsources
      (List.finRange (T / b + 1)) fallback hfallback

end OneTapeMagnification
end Frontier
end Pnp4
