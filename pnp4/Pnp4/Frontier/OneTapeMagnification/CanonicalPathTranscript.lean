import Pnp4.Frontier.OneTapeMagnification.InputCacheNormalization
import Pnp4.Frontier.OneTapeMagnification.WorkHeadCrossings
import Mathlib.Data.Fintype.Option

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite canonical path transcripts

This module packages the deterministic run of the concrete one-tape machine
into a genuinely finite transcript type.  A transcript records:

* one bounded local snapshot at every time `0, ..., T`;
* the (optional) work-tape boundary crossed at each of the `T` transitions;
* one canonical minimum-crossing boundary in every full spatial bucket of
  length `b`.

The work and input heads are bounded by elapsed time, so their exact positions
fit in `Fin (T + 1)`; no truncation is used.  The crossing fibers satisfy the
exact global budget `sum crossings <= T`, and hence the canonical selected
crossing counts sum to at most `T / b`.

The extracted transcript is unique because the underlying machine is
deterministic.  This is the honest unambiguous path layer only.  It does not
construct local validators, a branching program, a rectangle decomposition,
or any width bound: those require additional compatibility proofs about the
work-tape contents at the selected interfaces.
-/

/-- The analogous one-step upper bound for the one-way input head. -/
theorem inputHead_step_le_succ
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    (step machine input config).inputHead ≤ config.inputHead + 1 := by
  rcases inputHead_step_cases machine input config with h | h
  · rw [h]
    exact Nat.le_succ _
  · rw [h]

/-- Blank-start specialization of `runFrom_succ_eq_step_runFrom`. -/
theorem run_succ_eq_step_run
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    run machine input (steps + 1) =
      step machine input (run machine input steps) := by
  exact runFrom_succ_eq_step_runFrom machine input
    (initialConfiguration machine) steps

/-- Consecutive configurations in a run have equal or adjacent work-head
positions.  This justifies representing a nonstationary transition by one
boundary index. -/
theorem workHead_run_succ_cases
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    (run machine input (steps + 1)).workHead =
        (run machine input steps).workHead - 1 ∨
      (run machine input (steps + 1)).workHead =
        (run machine input steps).workHead ∨
      (run machine input (steps + 1)).workHead =
        (run machine input steps).workHead + 1 := by
  rw [run_succ_eq_step_run]
  exact workHead_step_cases machine input (run machine input steps)

/-- After `steps` transitions, the work head is at most `steps` cells to the
right of its starting position. -/
theorem workHead_runFrom_le_start_add
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps : Nat) :
    (runFrom machine input config steps).workHead ≤ config.workHead + steps := by
  exact workHeadTrajectoryFrom_le_initial_add machine input config steps

/-- The same elapsed-time bound for the one-way input head. -/
theorem inputHead_runFrom_le_start_add
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps : Nat) :
    (runFrom machine input config steps).inputHead ≤ config.inputHead + steps := by
  induction steps generalizing config with
  | zero => simp
  | succ steps ih =>
      rw [runFrom_succ]
      calc
        (runFrom machine input (step machine input config) steps).inputHead ≤
            (step machine input config).inputHead + steps :=
          ih (config := step machine input config)
        _ ≤ (config.inputHead + 1) + steps :=
          Nat.add_le_add_right (inputHead_step_le_succ machine input config) steps
        _ = config.inputHead + (steps + 1) := by
          ac_rfl

/-- Exact blank-start work-head bound. -/
theorem workHead_run_le_time
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    (run machine input steps).workHead ≤ steps := by
  simpa [run, initialConfiguration] using
    workHead_runFrom_le_start_add machine input
      (initialConfiguration machine) steps

/-- Exact blank-start input-head bound. -/
theorem inputHead_run_le_time
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    (run machine input steps).inputHead ≤ steps := by
  simpa [run, initialConfiguration] using
    inputHead_runFrom_le_start_add machine input
      (initialConfiguration machine) steps

/-- Finite local information exposed by a run at one time.  Both head
positions are exact; the elapsed-time lemmas justify their finite types. -/
structure BoundedPathSnapshot (State : Type) (T : Nat) where
  state : State
  inputHead : Fin (T + 1)
  workHead : Fin (T + 1)
  inputSymbol : ReadOnlySymbol
  workSymbol : Bool
deriving Fintype

/-- The finite transcript carrier.  `crossedAt t = some cut` records the
single spatial interface crossed between times `t` and `t + 1`. -/
structure CanonicalPathTranscript (State : Type) (T b : Nat) where
  path : Fin (T + 1) → BoundedPathSnapshot State T
  crossedAt : Fin T → Option (Fin T)
  cuts : Fin (T / b) → Fin T
deriving Fintype

/-- The machine supplies the missing finite enumeration of its state type, so
the complete transcript carrier is finite for every fixed `T` and `b`. -/
noncomputable def canonicalPathTranscriptFintype
    (machine : DeterministicMachine) (T b : Nat) :
    Fintype (CanonicalPathTranscript machine.State T b) := by
  letI : Fintype machine.State := machine.stateFintype
  exact inferInstance

/-- Exact bounded snapshot extracted from time `t` of the run. -/
def boundedRunSnapshot (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (t : Fin (T + 1)) : BoundedPathSnapshot machine.State T :=
  let config := run machine input t.val
  { state := config.state
    inputHead :=
      ⟨config.inputHead,
        Nat.lt_succ_of_le ((inputHead_run_le_time machine input t.val).trans
          (Nat.le_of_lt_succ t.isLt))⟩
    workHead :=
      ⟨config.workHead,
        Nat.lt_succ_of_le ((workHead_run_le_time machine input t.val).trans
          (Nat.le_of_lt_succ t.isLt))⟩
    inputSymbol := readOnlySymbol input config.inputHead
    workSymbol := WorkTape.read config.workTape config.workHead }

/-- The canonical interface index of a nonstationary transition is the lesser
of its two adjacent work-head positions.  The result fits in `Fin T` because
the position before transition `t` is at most `t < T`.

`workHead_step_cases` and `runFrom_succ_eq_step_runFrom` establish that the
two positions are equal or adjacent; the definition does not posit a jump. -/
def runCrossedBoundaryAt (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (t : Fin T) : Option (Fin T) :=
  let before := (run machine input t.val).workHead
  let after := (run machine input (t.val + 1)).workHead
  if _h : before = after then
    none
  else
    some ⟨min before after,
      lt_of_le_of_lt (Nat.min_le_left before after)
        ((workHead_run_le_time machine input t.val).trans_lt t.isLt)⟩

/-- The optional boundary stored by the transcript agrees exactly with the
crossing predicate of `WorkHeadCrossings`.  Adjacency of consecutive work-head
positions is essential here: the lesser endpoint identifies the unique
crossed boundary only because legal transitions never jump over a cell. -/
theorem runCrossedBoundaryAt_eq_some_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (t cut : Fin T) :
    runCrossedBoundaryAt machine input T t = some cut ↔
      WorkBoundaryCrossingAt machine input t.val cut.val := by
  let before := (run machine input t.val).workHead
  let after := (run machine input (t.val + 1)).workHead
  have hBefore : before < T := by
    exact (workHead_run_le_time machine input t.val).trans_lt t.isLt
  have hBoundary : min before after < T :=
    lt_of_le_of_lt (Nat.min_le_left before after) hBefore
  have hCases : after = before - 1 ∨ after = before ∨ after = before + 1 := by
    simpa [before, after] using
      (workHead_run_succ_cases machine input t.val)
  rcases cut with ⟨cut, hCut⟩
  change
    (if _h : before = after then (none : Option (Fin T))
      else some (⟨min before after, hBoundary⟩ : Fin T)) =
        some (⟨cut, hCut⟩ : Fin T) ↔
        CrossesWorkBoundary cut before after
  rcases hCases with hLeft | hStay | hRight
  all_goals
    by_cases hSame : before = after
    · simp [hSame, CrossesWorkBoundary]
      omega
    · simp [hSame, CrossesWorkBoundary]
      omega

/-- Number of transitions whose canonical crossed interface is `cut`. -/
def runCrossingCount (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (cut : Fin T) : Nat :=
  ((Finset.univ : Finset (Fin T)).filter
    (fun t => runCrossedBoundaryAt machine input T t = some cut)).card

/-- Fiber cardinality in the transcript presentation is exactly the crossing
count already defined by `WorkHeadCrossings`. -/
theorem runCrossingCount_eq_workBoundaryCrossingCount
    (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (cut : Fin T) :
    runCrossingCount machine input T cut =
      workBoundaryCrossingCount machine input T cut.val := by
  classical
  unfold runCrossingCount workBoundaryCrossingCount
    workBoundaryCrossingCountFrom
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hEvent : runCrossedBoundaryAt machine input T t = some cut
  · have hCrossing :=
      (runCrossedBoundaryAt_eq_some_iff machine input T t cut).1 hEvent
    change WorkBoundaryCrossingAtFrom machine input
      (initialConfiguration machine) t.val cut.val at hCrossing
    simp [hEvent, hCrossing]
  · have hCrossing :
        ¬ WorkBoundaryCrossingAt machine input t.val cut.val := by
      exact fun h => hEvent
        ((runCrossedBoundaryAt_eq_some_iff machine input T t cut).2 h)
    change ¬ WorkBoundaryCrossingAtFrom machine input
      (initialConfiguration machine) t.val cut.val at hCrossing
    simp [hEvent, hCrossing]

/-- Crossing count computed from an arbitrary finite transcript. -/
def transcriptCrossingCount {State : Type} {T b : Nat}
    (transcript : CanonicalPathTranscript State T b) (cut : Fin T) : Nat :=
  ((Finset.univ : Finset (Fin T)).filter
    (fun t => transcript.crossedAt t = some cut)).card

/-- The sum of all crossing-fiber sizes is at most the number `T` of
transitions.  Stationary transitions lie in the omitted `none` fiber. -/
theorem sum_runCrossingCount_le_time
    (machine : DeterministicMachine) (input : List Bool) (T : Nat) :
    (∑ cut : Fin T, runCrossingCount machine input T cut) ≤ T := by
  simpa only [runCrossingCount_eq_workBoundaryCrossingCount] using
    (sum_workBoundaryCrossingCount_le_steps machine input T)

/-- Canonical extraction from a deterministic run. -/
noncomputable def extractCanonicalPathTranscript {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool) :
    CanonicalPathTranscript machine.State T b where
  path := boundedRunSnapshot machine input T
  crossedAt := runCrossedBoundaryAt machine input T
  cuts := fun i => canonicalBoundary hb
    (runCrossingCount machine input T) i

/-- The crossing counts stored in the extracted transcript are exactly the
crossing counts of the run. -/
@[simp]
theorem transcriptCrossingCount_extract {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool) (cut : Fin T) :
    transcriptCrossingCount
        (extractCanonicalPathTranscript hb machine input) cut =
      runCrossingCount machine input T cut :=
  rfl

/-- Every extracted canonical cut lies in its declared full spatial bucket. -/
theorem extracted_canonical_cut_mem_bucket {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool)
    (i : Fin (T / b)) :
    i.val * b ≤ (extractCanonicalPathTranscript hb machine input).cuts i ∧
      (extractCanonicalPathTranscript hb machine input).cuts i <
        (i.val + 1) * b := by
  exact canonicalBoundary_mem_bucket hb
    (runCrossingCount machine input T) i

/-- The selected interface is a minimum-crossing interface in its bucket. -/
theorem extracted_canonical_cut_is_minimum {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool)
    (i : Fin (T / b)) (offset : Fin b) :
    runCrossingCount machine input T
        ((extractCanonicalPathTranscript hb machine input).cuts i) ≤
      runCrossingCount machine input T (fullBucketBoundary i offset) := by
  exact canonicalBoundary_is_minimum hb
    (runCrossingCount machine input T) i offset

/-- Combining the fiber budget with canonical boundary selection gives the
floor-exact aggregate bound for the extracted path transcript. -/
theorem sum_extracted_canonical_cut_crossings_le_div {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool) :
    (∑ i : Fin (T / b),
      runCrossingCount machine input T
        ((extractCanonicalPathTranscript hb machine input).cuts i)) ≤ T / b := by
  exact sum_canonicalBoundary_le_div hb
    (runCrossingCount machine input T)
    (sum_runCrossingCount_le_time machine input T)

/-- Predicate defining the canonical transcript fiber of one fixed run. -/
def IsCanonicalPathTranscriptFor {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool)
    (transcript : CanonicalPathTranscript machine.State T b) : Prop :=
  transcript = extractCanonicalPathTranscript hb machine input

/-- Determinism makes the canonical transcript fiber a singleton. -/
theorem canonical_path_transcript_unique {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool) :
    ∃! transcript : CanonicalPathTranscript machine.State T b,
      IsCanonicalPathTranscriptFor hb machine input transcript := by
  refine ⟨extractCanonicalPathTranscript hb machine input, rfl, ?_⟩
  intro transcript hTranscript
  exact hTranscript

/-- Acceptance predicate read from the final bounded snapshot. -/
def PathTranscriptAccepts (machine : DeterministicMachine) {T b : Nat}
    (transcript : CanonicalPathTranscript machine.State T b) : Prop :=
  machine.halt (transcript.path ⟨T, Nat.lt_succ_self T⟩).state =
    some .accept

/-- The final snapshot of the extracted transcript preserves acceptance
exactly. -/
theorem extracted_path_transcript_accepts_iff {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool) :
    PathTranscriptAccepts (T := T) (b := b) machine
        (extractCanonicalPathTranscript (T := T) (b := b) hb machine input) ↔
      IsAccepting machine (run machine input T) := by
  rfl

/-- An accepting deterministic run has exactly one accepting member in its
canonical transcript fiber. -/
theorem accepting_run_has_unique_canonical_path_transcript
    {T b : Nat} (hb : 0 < b)
    (machine : DeterministicMachine) (input : List Bool)
    (hAccept : IsAccepting machine (run machine input T)) :
    ∃! transcript : CanonicalPathTranscript machine.State T b,
      IsCanonicalPathTranscriptFor hb machine input transcript ∧
        PathTranscriptAccepts machine transcript := by
  refine ⟨extractCanonicalPathTranscript hb machine input,
    ⟨rfl, (extracted_path_transcript_accepts_iff hb machine input).2 hAccept⟩,
    ?_⟩
  intro transcript hTranscript
  exact hTranscript.1

/-- The cached-input normalization exposes the original control state and
cached current input symbol at every positive normalized time.  This is the
exact compatibility needed before building cached path transcripts. -/
theorem cached_run_state_at_succ
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    (run (cachedInputMachine machine) input (steps + 1)).state =
      some ((run machine input steps).state,
        readOnlySymbol input (run machine input steps).inputHead) := by
  rw [cachedInputMachine_run_succ]
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
