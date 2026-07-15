import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalCutOutputInformationBarrier
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaCutCounterReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A fixed machine realizing the paired information-barrier profiles

The crossing-count profiles of the legal boundary words from
`CanonicalCutOutputInformationBarrier` are not merely synthetic.  This file
realizes every such profile during the first `6 * r` transitions of one fixed
deterministic one-tape machine.  The seed is supplied on the one-way read-only
input tape.

During the first two transitions for each input bit the machine moves right
twice and stores that bit in the odd work-tape cell of the corresponding
two-boundary bucket.  Once it sees the input endmarker it walks back through
the buckets.  Four transitions per stored bit contribute the crossing-count
multiplicities of the paired descent chunk.  Thus the control has constant
size (eight states), while the actual crossing profile contains the `r`
independent bits used by the canonical-offset information barrier.
-/

/-! ## The fixed eight-state control -/

inductive FixedPairedBounceState where
  | ascend
  | ascendWrite (bit : Bool)
  | descentKick
  | descentRead
  | descentReturn (bit : Bool)
  | descentFinish
deriving DecidableEq, Fintype, Repr

@[simp]
theorem card_fixedPairedBounceState :
    Fintype.card FixedPairedBounceState = 8 := by
  decide

/-- One fixed machine, independent of both the seed and its length. -/
def fixedPairedBounceMachine : DeterministicMachine where
  State := FixedPairedBounceState
  stateFintype := inferInstance
  startState := .ascend
  halt := fun _ => none
  transition := fun state input work =>
    match state with
    | .ascend =>
        match input with
        | .bit bit =>
            { nextState := .ascendWrite bit
              write := false
              inputMove := .stay
              workMove := .right }
        | .rightEnd =>
            { nextState := .descentRead
              write := work
              inputMove := .stay
              workMove := .left }
    | .ascendWrite bit =>
        { nextState := .ascend
          write := bit
          inputMove := .right
          workMove := .right }
    | .descentKick =>
        { nextState := .descentRead
          write := work
          inputMove := .stay
          workMove := .left }
    | .descentRead =>
        { nextState := .descentReturn work
          write := work
          inputMove := .stay
          workMove := if work then .right else .left }
    | .descentReturn bit =>
        { nextState := .descentFinish
          write := work
          inputMove := .stay
          workMove := if bit then .left else .right }
    | .descentFinish =>
        { nextState := .descentKick
          write := work
          inputMove := .stay
          workMove := .left }

/-! ## Exact ascent configurations -/

/-- Work tape after the first `processed` seed bits have been stored. -/
def fixedPairedBouncePrefixTape (bits : Nat -> Bool) : Nat -> WorkTape
  | 0 => WorkTape.blank
  | processed + 1 =>
      WorkTape.write (fixedPairedBouncePrefixTape bits processed)
        (2 * processed + 1) (bits processed)

@[simp]
theorem fixedPairedBouncePrefixTape_zero (bits : Nat -> Bool) :
    fixedPairedBouncePrefixTape bits 0 = WorkTape.blank := rfl

@[simp]
theorem fixedPairedBouncePrefixTape_even
    (bits : Nat -> Bool) (processed cell : Nat) :
    WorkTape.read (fixedPairedBouncePrefixTape bits processed) (2 * cell) =
      false := by
  induction processed with
  | zero => rfl
  | succ processed ih =>
      rw [fixedPairedBouncePrefixTape]
      rw [WorkTape.read_write_of_ne]
      · exact ih
      · omega

@[simp]
theorem fixedPairedBouncePrefixTape_odd_of_lt
    (bits : Nat -> Bool) {index processed : Nat} (hindex : index < processed) :
    WorkTape.read (fixedPairedBouncePrefixTape bits processed)
        (2 * index + 1) = bits index := by
  induction processed with
  | zero => omega
  | succ processed ih =>
      by_cases htop : index = processed
      · subst index
        exact WorkTape.read_write_same _ _ _
      · rw [fixedPairedBouncePrefixTape,
          WorkTape.read_write_of_ne _ _ _ _ (by omega)]
        exact ih (by omega)

@[simp]
theorem WorkTape.write_read_self (tape : WorkTape) (head : Nat) :
    WorkTape.write tape head (WorkTape.read tape head) = tape := by
  funext cell
  by_cases hcell : cell = head
  · subst cell
    simp [WorkTape.write, WorkTape.read]
  · simp [WorkTape.write, hcell]

/-- Configuration at the boundary between two completed ascent buckets. -/
def fixedPairedBounceAscentConfig (bits : Nat -> Bool) (processed : Nat) :
    Configuration FixedPairedBounceState where
  state := .ascend
  inputHead := processed
  workHead := 2 * processed
  workTape := fixedPairedBouncePrefixTape bits processed

/-- Intermediate configuration after the first move for one ascent bucket. -/
def fixedPairedBounceAscentWriteConfig
    (bits : Nat -> Bool) (processed : Nat) :
    Configuration FixedPairedBounceState where
  state := .ascendWrite (bits processed)
  inputHead := processed
  workHead := 2 * processed + 1
  workTape := fixedPairedBouncePrefixTape bits processed

/-- Descent configuration at the right edge of the first unprocessed bucket. -/
def fixedPairedBounceKickConfig
    (tape : WorkTape) (inputHead bucketCount : Nat) :
    Configuration FixedPairedBounceState where
  state := .descentKick
  inputHead := inputHead
  workHead := 2 * bucketCount
  workTape := tape

@[simp]
theorem readOnlySymbol_ofFn_fixedPairedBounceSeed
    {r : Nat} (seed : Fin r -> Bool) (index : Fin r) :
    readOnlySymbol (List.ofFn seed) index.val = .bit (seed index) := by
  unfold readOnlySymbol
  rw [List.getElem?_eq_getElem]
  · simp
  · simp [index.isLt]

@[simp]
theorem readOnlySymbol_ofFn_fixedPairedBounceSeed_end
    {r : Nat} (seed : Fin r -> Bool) :
    readOnlySymbol (List.ofFn seed) r = .rightEnd := by
  simp [readOnlySymbol]

theorem fixedPairedBouncePrefixTape_write_even
    (bits : Nat -> Bool) (processed : Nat) :
    WorkTape.write (fixedPairedBouncePrefixTape bits processed)
        (2 * processed) false =
      fixedPairedBouncePrefixTape bits processed := by
  simpa only [fixedPairedBouncePrefixTape_even] using
    (WorkTape.write_read_self
      (fixedPairedBouncePrefixTape bits processed) (2 * processed))

@[simp]
theorem fixedPairedBouncePrefixTape_write_even_at
    (bits : Nat -> Bool) (processed cell : Nat) :
    WorkTape.write (fixedPairedBouncePrefixTape bits processed)
        (2 * cell) false =
      fixedPairedBouncePrefixTape bits processed := by
  simpa only [fixedPairedBouncePrefixTape_even] using
    (WorkTape.write_read_self
      (fixedPairedBouncePrefixTape bits processed) (2 * cell))

@[simp]
theorem step_fixedPairedBounceAscentConfig
    {r : Nat} (seed : Fin r -> Bool) (processed : Fin r) :
    step fixedPairedBounceMachine (List.ofFn seed)
        (fixedPairedBounceAscentConfig (pairedSeedBitAt seed) processed.val) =
      fixedPairedBounceAscentWriteConfig
        (pairedSeedBitAt seed) processed.val := by
  simp [step, fixedPairedBounceMachine,
    fixedPairedBounceAscentConfig, fixedPairedBounceAscentWriteConfig,
    applyInstruction, moveInputHead, moveWorkHead]

@[simp]
theorem step_fixedPairedBounceAscentWriteConfig
    {r : Nat} (seed : Fin r -> Bool) (processed : Fin r) :
    step fixedPairedBounceMachine (List.ofFn seed)
        (fixedPairedBounceAscentWriteConfig
          (pairedSeedBitAt seed) processed.val) =
      fixedPairedBounceAscentConfig
        (pairedSeedBitAt seed) (processed.val + 1) := by
  simp [step, fixedPairedBounceMachine,
    fixedPairedBounceAscentConfig, fixedPairedBounceAscentWriteConfig,
    applyInstruction, moveInputHead, moveWorkHead,
    fixedPairedBouncePrefixTape, pairedSeedBitAt_apply]
  omega

/-- Blank-start run after storing any prefix of the input seed. -/
theorem run_fixedPairedBounceMachine_ascent
    {r : Nat} (seed : Fin r -> Bool) (processed : Nat)
    (hprocessed : processed <= r) :
    run fixedPairedBounceMachine (List.ofFn seed) (2 * processed) =
      fixedPairedBounceAscentConfig (pairedSeedBitAt seed) processed := by
  induction processed with
  | zero =>
      rfl
  | succ processed ih =>
      have hlt : processed < r := by omega
      let index : Fin r := ⟨processed, hlt⟩
      have hFirst := step_fixedPairedBounceAscentConfig seed index
      have hSecond := step_fixedPairedBounceAscentWriteConfig seed index
      have hRunFirst :
          run fixedPairedBounceMachine (List.ofFn seed) (2 * processed + 1) =
            fixedPairedBounceAscentWriteConfig
              (pairedSeedBitAt seed) processed := by
        change runFrom fixedPairedBounceMachine (List.ofFn seed)
          (initialConfiguration fixedPairedBounceMachine)
            (2 * processed + 1) = _
        rw [runFrom_succ_eq_step_runFrom]
        change step fixedPairedBounceMachine (List.ofFn seed)
          (run fixedPairedBounceMachine (List.ofFn seed) (2 * processed)) = _
        rw [ih (by omega)]
        simpa [index] using hFirst
      calc
        run fixedPairedBounceMachine (List.ofFn seed) (2 * (processed + 1)) =
            run fixedPairedBounceMachine (List.ofFn seed)
              ((2 * processed + 1) + 1) := by
            apply congrArg (fun steps =>
              run fixedPairedBounceMachine (List.ofFn seed) steps)
            omega
        _ = step fixedPairedBounceMachine (List.ofFn seed)
              (run fixedPairedBounceMachine (List.ofFn seed)
                (2 * processed + 1)) :=
            runFrom_succ_eq_step_runFrom _ _ _ _
        _ = fixedPairedBounceAscentConfig
              (pairedSeedBitAt seed) (processed + 1) := by
            rw [hRunFirst]
            simpa [index] using hSecond

/-! ## Exact local crossing traces -/

/-- Two ascent transitions cross the two boundaries of the next bucket. -/
theorem streaming_fixedPairedBounceAscentConfig_two
    {r : Nat} (seed : Fin r -> Bool) (processed : Fin r) (boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        (List.ofFn seed)
        (fixedPairedBounceAscentConfig
          (pairedSeedBitAt seed) processed.val)
        2 boundary =
      List.count boundary [2 * processed.val, 2 * processed.val + 1] := by
  have hFirst := step_fixedPairedBounceAscentConfig seed processed
  have hSecond := step_fixedPairedBounceAscentWriteConfig seed processed
  simp only [streamingWorkBoundaryCrossingCountFrom]
  rw [hFirst, hSecond]
  simp only [List.count_cons, List.count_nil, Nat.add_zero]
  simp [CrossesWorkBoundary, fixedPairedBounceAscentConfig,
    fixedPairedBounceAscentWriteConfig]
  split_ifs <;> omega

/-- One descent bucket executes one paired four-crossing chunk exactly. -/
theorem runFrom_fixedPairedBounceKickConfig_four
    {r : Nat} (seed : Fin r -> Bool) {bucket : Nat} (hbucket : bucket < r) :
    runFrom fixedPairedBounceMachine (List.ofFn seed)
        (fixedPairedBounceKickConfig
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r)
          r (bucket + 1))
        4 =
      fixedPairedBounceKickConfig
        (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r) r bucket := by
  have hread :
      WorkTape.read
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r)
          (2 * bucket + 1) = pairedSeedBitAt seed bucket :=
    fixedPairedBouncePrefixTape_odd_of_lt _ hbucket
  have hodd : 2 * (bucket + 1) - 1 = 2 * bucket + 1 := by omega
  have hwrite :
      WorkTape.write
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r)
          (2 * bucket + 1) (pairedSeedBitAt seed bucket) =
        fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r := by
    rw [← hread]
    exact WorkTape.write_read_self _ _
  cases hbit : pairedSeedBitAt seed bucket <;>
    simp [runFrom, step, fixedPairedBounceMachine,
      fixedPairedBounceKickConfig, applyInstruction, moveInputHead,
      moveWorkHead, hodd, hread, hbit]
  all_goals
    rw [← hbit, hwrite, hwrite]

/-- The crossing multiplicities of the four executed transitions agree with
the corresponding explicit descent chunk. -/
theorem streaming_fixedPairedBounceKickConfig_four
    {r : Nat} (seed : Fin r -> Bool) {bucket : Nat} (hbucket : bucket < r)
    (boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        (List.ofFn seed)
        (fixedPairedBounceKickConfig
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r)
          r (bucket + 1))
        4 boundary =
      List.count boundary
        (pairedDescentChunk (pairedSeedBitAt seed bucket) bucket) := by
  have hread :
      WorkTape.read
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r)
          (2 * bucket + 1) = pairedSeedBitAt seed bucket :=
    fixedPairedBouncePrefixTape_odd_of_lt _ hbucket
  have hodd : 2 * (bucket + 1) - 1 = 2 * bucket + 1 := by omega
  cases hbit : pairedSeedBitAt seed bucket <;>
    simp [streamingWorkBoundaryCrossingCountFrom, step,
      fixedPairedBounceMachine, fixedPairedBounceKickConfig,
      pairedDescentChunk, applyInstruction, moveInputHead, moveWorkHead,
      CrossesWorkBoundary, List.count_cons, List.count_nil,
      hodd, hread, hbit] <;>
    split_ifs <;> omega

/-! ## Global execution and crossing profile -/

/-- The monotone ascent contributes one occurrence of every boundary in
`List.range (2 * processed)`. -/
theorem streaming_fixedPairedBounceMachine_ascent
    {r : Nat} (seed : Fin r -> Bool) (processed : Nat)
    (hprocessed : processed <= r) (boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        (List.ofFn seed) (initialConfiguration fixedPairedBounceMachine)
        (2 * processed) boundary =
      List.count boundary (List.range (2 * processed)) := by
  induction processed with
  | zero =>
      simp [streamingWorkBoundaryCrossingCountFrom]
  | succ processed ih =>
      have hlt : processed < r := by omega
      let index : Fin r := ⟨processed, hlt⟩
      have hsplit := streamingWorkBoundaryCrossingCountFrom_add
        fixedPairedBounceMachine (List.ofFn seed)
        (initialConfiguration fixedPairedBounceMachine)
        (2 * processed) 2 boundary
      have hrun := run_fixedPairedBounceMachine_ascent
        seed processed (by omega)
      have hlocal := streaming_fixedPairedBounceAscentConfig_two
        seed index boundary
      have hRange :
          List.range (2 * (processed + 1)) =
            List.range (2 * processed) ++
              [2 * processed, 2 * processed + 1] := by
        rw [show 2 * (processed + 1) = (2 * processed + 1) + 1 by omega,
          List.range_succ, List.range_succ]
        simp [List.append_assoc]
      rw [hRange, List.count_append]
      rw [show 2 * (processed + 1) = 2 * processed + 2 by omega,
        hsplit, ih (by omega)]
      change
        List.count boundary (List.range (2 * processed)) +
            streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
              (List.ofFn seed)
              (run fixedPairedBounceMachine (List.ofFn seed) (2 * processed))
              2 boundary = _
      rw [hrun]
      simpa [index] using congrArg
        (fun value => List.count boundary (List.range (2 * processed)) + value)
        hlocal

/-- Executing all remaining buckets from a descent-kick configuration yields
the crossing-count multiplicities of the recursive descending boundary word. -/
theorem streaming_fixedPairedBounceMachine_descent
    {r : Nat} (seed : Fin r -> Bool) (bucketCount : Nat)
    (hbucketCount : bucketCount <= r) (boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        (List.ofFn seed)
        (fixedPairedBounceKickConfig
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r)
          r bucketCount)
        (4 * bucketCount) boundary =
      List.count boundary
        (pairedDescentBoundaryWord (pairedSeedBitAt seed) bucketCount) := by
  induction bucketCount with
  | zero =>
      simp [streamingWorkBoundaryCrossingCountFrom,
        pairedDescentBoundaryWord]
  | succ bucketCount ih =>
      have hlt : bucketCount < r := by omega
      have hsplit := streamingWorkBoundaryCrossingCountFrom_add
        fixedPairedBounceMachine (List.ofFn seed)
        (fixedPairedBounceKickConfig
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r)
          r (bucketCount + 1))
        4 (4 * bucketCount) boundary
      have hrun := runFrom_fixedPairedBounceKickConfig_four seed hlt
      have hlocal := streaming_fixedPairedBounceKickConfig_four
        seed hlt boundary
      rw [show 4 * (bucketCount + 1) = 4 + 4 * bucketCount by omega,
        hsplit, hlocal, hrun, ih (by omega)]
      simp [pairedDescentBoundaryWord, List.count_append]

/-- Streaming counts depend only on the current head and its first successor
when the first transition reaches the same configuration. -/
theorem streamingWorkBoundaryCrossingCountFrom_eq_of_head_step_eq
    (input : List Bool)
    (left right : Configuration FixedPairedBounceState)
    (hhead : left.workHead = right.workHead)
    (hstep : step fixedPairedBounceMachine input left =
      step fixedPairedBounceMachine input right)
    (steps boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        input left steps boundary =
      streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        input right steps boundary := by
  cases steps with
  | zero => rfl
  | succ steps =>
      simp only [streamingWorkBoundaryCrossingCountFrom]
      rw [hhead, hstep]

/-- At the endmarker the ascent state and the descent-kick state take the
same first descent transition. -/
theorem step_fixedPairedBounceAscentEnd_eq_kick
    {r : Nat} (seed : Fin r -> Bool) :
    step fixedPairedBounceMachine (List.ofFn seed)
        (fixedPairedBounceAscentConfig (pairedSeedBitAt seed) r) =
      step fixedPairedBounceMachine (List.ofFn seed)
        (fixedPairedBounceKickConfig
          (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r) r r) := by
  simp [step, fixedPairedBounceMachine, fixedPairedBounceAscentConfig,
    fixedPairedBounceKickConfig, applyInstruction, moveInputHead,
    moveWorkHead]

/-- The post-ascent execution contributes the crossing-count multiplicities
of the paired descending word, including the first move triggered directly by
the endmarker. -/
theorem streaming_fixedPairedBounceMachine_afterAscent
    {r : Nat} (seed : Fin r -> Bool) (boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        (List.ofFn seed)
        (fixedPairedBounceAscentConfig (pairedSeedBitAt seed) r)
        (4 * r) boundary =
      List.count boundary
        (pairedDescentBoundaryWord (pairedSeedBitAt seed) r) := by
  rw [streamingWorkBoundaryCrossingCountFrom_eq_of_head_step_eq
    (List.ofFn seed)
    (fixedPairedBounceAscentConfig (pairedSeedBitAt seed) r)
    (fixedPairedBounceKickConfig
      (fixedPairedBouncePrefixTape (pairedSeedBitAt seed) r) r r)
    (by rfl) (step_fixedPairedBounceAscentEnd_eq_kick seed)]
  exact streaming_fixedPairedBounceMachine_descent seed r (by omega) boundary

/-- The first `6*r` transitions of the fixed machine have the same boundary
crossing multiplicities as the legal paired word from the information-barrier
construction. -/
theorem streaming_fixedPairedBounceMachine_count_eq_word_count
    {r : Nat} (seed : Fin r -> Bool) (boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
        (List.ofFn seed) (initialConfiguration fixedPairedBounceMachine)
        (6 * r) boundary =
      List.count boundary (pairedBounceBoundaryWord seed) := by
  have hsplit := streamingWorkBoundaryCrossingCountFrom_add
    fixedPairedBounceMachine (List.ofFn seed)
    (initialConfiguration fixedPairedBounceMachine)
    (2 * r) (4 * r) boundary
  rw [show 6 * r = 2 * r + 4 * r by omega, hsplit,
    streaming_fixedPairedBounceMachine_ascent seed r (by omega)]
  change
    List.count boundary (List.range (2 * r)) +
        streamingWorkBoundaryCrossingCountFrom fixedPairedBounceMachine
          (List.ofFn seed)
          (run fixedPairedBounceMachine (List.ofFn seed) (2 * r))
          (4 * r) boundary = _
  rw [run_fixedPairedBounceMachine_ascent seed r (by omega),
    streaming_fixedPairedBounceMachine_afterAscent]
  simp [pairedBounceBoundaryWord, List.count_append]

/-- Main realization theorem: on a seed of length `r`, the actual work-head
crossing profile of this one fixed machine after `6*r` transitions is the
synthetic paired profile used by the canonical-offset lower bound. -/
theorem workBoundaryCrossingCount_fixedPairedBounceMachine
    {r : Nat} (seed : Fin r -> Bool) (boundary : Fin (6 * r)) :
    workBoundaryCrossingCount fixedPairedBounceMachine (List.ofFn seed)
        (6 * r) boundary.val =
      pairedCrossingProfile seed boundary := by
  rw [workBoundaryCrossingCount]
  rw [← streamingWorkBoundaryCrossingCountFrom_eq]
  rw [streaming_fixedPairedBounceMachine_count_eq_word_count]
  exact count_pairedBounceBoundaryWord_eq_pairedCrossingProfile seed boundary

/-! ## Canonical offsets and terminal-summary lower bounds -/

/-- Canonical offsets computed from the actual `6*r`-step run of the fixed
machine on the finite seed input. -/
noncomputable def fixedPairedBounceMachineCanonicalCutOffsets
    {r : Nat} (seed : Fin r -> Bool) : CanonicalCutOffsets (6 * r) 2 :=
  fun bucket =>
    canonicalBoundaryOffset (by omega : 0 < 2)
      (fun boundary : Fin (6 * r) =>
        workBoundaryCrossingCount fixedPairedBounceMachine (List.ofFn seed)
          (6 * r) boundary.val)
      bucket

/-- Actual-run canonical offsets are exactly the paired offset vector. -/
theorem fixedPairedBounceMachineCanonicalCutOffsets_eq
    {r : Nat} (seed : Fin r -> Bool) :
    fixedPairedBounceMachineCanonicalCutOffsets seed =
      pairedCanonicalCutOffsets seed := by
  have hProfile :
      (fun boundary : Fin (6 * r) =>
        workBoundaryCrossingCount fixedPairedBounceMachine (List.ofFn seed)
          (6 * r) boundary.val) =
        pairedCrossingProfile seed := by
    funext boundary
    exact workBoundaryCrossingCount_fixedPairedBounceMachine seed boundary
  unfold fixedPairedBounceMachineCanonicalCutOffsets pairedCanonicalCutOffsets
  rw [hProfile]

/-- The actual canonical-offset vectors of this one fixed machine retain all
seed bits. -/
theorem fixedPairedBounceMachineCanonicalCutOffsets_injective (r : Nat) :
    Function.Injective
      (fixedPairedBounceMachineCanonicalCutOffsets :
        (Fin r -> Bool) -> CanonicalCutOffsets (6 * r) 2) := by
  intro left right hOffsets
  apply pairedCanonicalCutOffsets_injective r
  rw [← fixedPairedBounceMachineCanonicalCutOffsets_eq left,
    ← fixedPairedBounceMachineCanonicalCutOffsets_eq right, hOffsets]

/-- Any finite terminal summary which exactly recovers all canonical offsets
on the length-`r` inputs of the fixed machine has at least `2^r` states. -/
theorem two_pow_le_card_of_recovers_fixedPairedBounceMachineOffsets
    (r : Nat) (State : Type) [Fintype State]
    (encode : List Bool -> State)
    (decode : State -> CanonicalCutOffsets (6 * r) 2)
    (hdecode : forall seed : Fin r -> Bool,
      decode (encode (List.ofFn seed)) =
        fixedPairedBounceMachineCanonicalCutOffsets seed) :
    2 ^ r <= Fintype.card State := by
  apply two_pow_le_card_of_recovers_pairedCanonicalCutOffsets
    r State (fun seed => encode (List.ofFn seed)) decode
  intro seed
  rw [hdecode, fixedPairedBounceMachineCanonicalCutOffsets_eq]

/-- In an explicit `s`-bit terminal carrier, exact recovery on the fixed
machine's length-`r` inputs forces `r <= s`, i.e. at least `T/6` bits for the
common horizon `T = 6*r`. -/
theorem bitBudget_of_recovers_fixedPairedBounceMachineOffsets
    (r s : Nat)
    (encode : List Bool -> Fin (2 ^ s))
    (decode : Fin (2 ^ s) -> CanonicalCutOffsets (6 * r) 2)
    (hdecode : forall seed : Fin r -> Bool,
      decode (encode (List.ofFn seed)) =
        fixedPairedBounceMachineCanonicalCutOffsets seed) :
    r <= s := by
  have hCard :=
    two_pow_le_card_of_recovers_fixedPairedBounceMachineOffsets
      r (Fin (2 ^ s)) encode decode hdecode
  simp only [Fintype.card_fin] at hCard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hCard

/-- The same bit-budget conclusion for an arbitrary finite terminal carrier
whose cardinality is at most `2^s`. -/
theorem bitBudget_of_card_le_two_pow_of_recovers_fixedPairedBounceMachineOffsets
    (r s : Nat) (State : Type) [Fintype State]
    (hStateCard : Fintype.card State <= 2 ^ s)
    (encode : List Bool -> State)
    (decode : State -> CanonicalCutOffsets (6 * r) 2)
    (hdecode : forall seed : Fin r -> Bool,
      decode (encode (List.ofFn seed)) =
        fixedPairedBounceMachineCanonicalCutOffsets seed) :
    r <= s := by
  have hLower :=
    two_pow_le_card_of_recovers_fixedPairedBounceMachineOffsets
      r State encode decode hdecode
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1
    (hLower.trans hStateCard)

end OneTapeMagnification
end Frontier
end Pnp4
