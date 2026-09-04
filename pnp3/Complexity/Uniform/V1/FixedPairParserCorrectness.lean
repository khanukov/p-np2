import Complexity.Uniform.V1.FixedPairParserCore
import Complexity.Uniform.V1.FixedPairParserLanguage

/-!
# Exact universal execution of the fixed pair parser

The ambient tape budget in every public result in this file is *exactly*
`clock N`.  The proof uses two positional invariants.  During every positive
forward time and throughout rewind, cell zero is `none` and every other cell
(including all padding) is exactly the corresponding initial cell.  The final
transition is the only transition that restores cell zero and enters a public
verdict state.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedPairParser

open PairEncoding

/-! ## Small extensional and projection lemmas -/

private theorem config_ext
    {N : Nat} {c d : Config parserStateCount N (clock N)}
    (hstate : c.state = d.state)
    (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cstate chead ctape =>
      cases d with
      | mk dstate dhead dtape =>
          change cstate = dstate at hstate
          change chead = dhead at hhead
          change ctape = dtape at htape
          subst dstate
          subst dhead
          subst dtape
          rfl

@[simp] private theorem stepConfig_state
    {N : Nat} (c : Config parserStateCount N (clock N)) :
    (machine.stepConfig c).state =
      (machine.step c.state (c.tape c.head)).1 :=
  rfl

@[simp] private theorem stepConfig_head
    {N : Nat} (c : Config parserStateCount N (clock N)) :
    (machine.stepConfig c).head =
      moveHead c.head (machine.step c.state (c.tape c.head)).2.2 :=
  rfl

@[simp] private theorem stepConfig_tape
    {N : Nat} (c : Config parserStateCount N (clock N))
    (i : Fin (tapeLength N (clock N))) :
    (machine.stepConfig c).tape i =
      if i = c.head
      then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i :=
  rfl

/-! ## Indexed prefixes and the independent grammar phase -/

/-- Total view of an indexed input.  Only indices below `N` are used by the
forward trace; the default makes the auxiliary prefix recursion total. -/
def indexedBit {N : Nat} (y : Bitstring N) (i : Nat) : Bool :=
  if h : i < N then y ⟨i, h⟩ else false

/-- First `k` indexed bits, built by appending at the right. -/
def indexedPrefix {N : Nat} (y : Bitstring N) : Nat → List Bool
  | 0 => []
  | k + 1 => indexedPrefix y k ++ [indexedBit y k]

@[simp] private theorem indexedPrefix_length {N : Nat}
    (y : Bitstring N) (k : Nat) :
    (indexedPrefix y k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [indexedPrefix, ih]

private theorem indexedPrefix_getElem {N : Nat}
    (y : Bitstring N) {k i : Nat} (hi : i < k) :
    (indexedPrefix y k)[i]'(by simpa using hi) = indexedBit y i := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hik : i < k
      · simpa [indexedPrefix, indexedPrefix_length, hik] using ih hik
      · have hieq : i = k := by omega
        subst i
        simp [indexedPrefix, indexedPrefix_length]

/-- At the real input length, the hand-built positional prefix is exactly
`List.ofFn`; no host decoder participates in the trace. -/
private theorem indexedPrefix_eq_ofFn {N : Nat} (y : Bitstring N) :
    indexedPrefix y N = List.ofFn y := by
  apply List.ext_get
  · simp
  · intro i hleft hright
    have hiN : i < N := by simpa using hright
    have hget := indexedPrefix_getElem (y := y) (k := N) (i := i) hiN
    simpa [indexedBit, hiN, List.get_ofFn] using hget

/-- Grammar phase after the first `k` positions. -/
def phaseAt {N : Nat} (y : Bitstring N) (k : Nat) : GrammarPhase :=
  grammarRun .needTag (indexedPrefix y k)

@[simp] private theorem phaseAt_zero {N : Nat} (y : Bitstring N) :
    phaseAt y 0 = .needTag := rfl

private theorem phaseAt_succ {N : Nat} (y : Bitstring N) (k : Nat) :
    phaseAt y (k + 1) = grammarStep (phaseAt y k) (indexedBit y k) := by
  simp [phaseAt, indexedPrefix, grammarRun_append, grammarRun]

private theorem phaseAt_length {N : Nat} (y : Bitstring N) :
    phaseAt y N = grammarRun .needTag (List.ofFn y) := by
  simp [phaseAt, indexedPrefix_eq_ofFn]

/-! ## Exact tape and control descriptions -/

/-- Exact-budget initial configuration. -/
def exactInitial {N : Nat} (y : Bitstring N) :
    Config parserStateCount N (clock N) :=
  initialConfig machine (clock N) y

/-- The actual forward/rewind tape: the exact initial tape with cell zero
erased.  This definition ranges over the complete `3*N+2` allocation. -/
def erasedZeroTape {N : Nat} (y : Bitstring N) :
    Fin (tapeLength N (clock N)) → Option Bool :=
  fun i => if i.val = 0 then none else (exactInitial y).tape i

@[simp] private theorem exactInitial_state {N : Nat} (y : Bitstring N) :
    (exactInitial y).state = qStart :=
  rfl

@[simp] private theorem exactInitial_head_val {N : Nat} (y : Bitstring N) :
    (exactInitial y).head.val = 0 :=
  rfl

private theorem erasedZeroTape_input {N : Nat} (y : Bitstring N)
    {i : Nat} (hpos : 0 < i) (hi : i < N)
    (hfit : i < tapeLength N (clock N)) :
    erasedZeroTape y ⟨i, hfit⟩ = some (indexedBit y i) := by
  simp [erasedZeroTape, exactInitial, initialConfig, indexedBit,
    hpos.ne', hi]

private theorem erasedZeroTape_boundary {N : Nat} (y : Bitstring N)
    (hfit : N < tapeLength N (clock N)) :
    erasedZeroTape y ⟨N, hfit⟩ = none := by
  by_cases hN : N = 0
  · subst N
    simp [erasedZeroTape]
  · simp [erasedZeroTape, exactInitial, initialConfig, hN]

private theorem exactInitial_read_zero {N : Nat} (y : Bitstring N)
    (hN : 0 < N) :
    (exactInitial y).tape (exactInitial y).head =
      some (indexedBit y 0) := by
  simp [exactInitial, initialConfig, indexedBit, hN]

/-- Restoring the saved first bit gives the whole exact-budget initial tape,
including every blank padding cell. -/
theorem restore_erasedZeroTape {N : Nat} (y : Bitstring N)
    (hN : 0 < N) :
    (fun i : Fin (tapeLength N (clock N)) =>
      if i.val = 0 then some (indexedBit y 0) else erasedZeroTape y i) =
      (exactInitial y).tape := by
  funext i
  by_cases hi : i.val = 0
  · simp [hi, exactInitial, initialConfig, indexedBit, hN]
  · simp [hi, erasedZeroTape]

/-- Map a saved first symbol and grammar phase to the corresponding forward
control of the fixed machine. -/
def forwardState (saved : Bool) : GrammarPhase → Fin parserStateCount
  | .needTag => qTagF
  | .needData => qDataF
  | .witness => if saved then qWitnessT else qWitnessF

/-- Rewind control selected at the right blank. -/
def backState (saved : Bool) : GrammarPhase → Fin parserStateCount
  | .needTag => qBackRejectF
  | .needData => qBackRejectF
  | .witness => if saved then qBackAcceptT else qBackAcceptF

/-- Literal terminal selected by a completed grammar phase. -/
def verdictState : GrammarPhase → Fin parserStateCount
  | .witness => qAccept
  | _ => qReject

/-- Symbol written by the final rewind transition.  For reachable phases it is
the saved first symbol. -/
private def backMarker (saved : Bool) : GrammarPhase → Bool
  | .witness => saved
  | _ => false

/-- The only reachability restriction needed by the phase/control map. -/
private def PhaseCompatible (saved : Bool) (phase : GrammarPhase) : Prop :=
  saved = true → phase = .witness

private theorem phaseAt_succ_witness_of_first_true {N : Nat} (y : Bitstring N)
    (hfirst : indexedBit y 0 = true) (k : Nat) :
    phaseAt y (k + 1) = .witness := by
  induction k with
  | zero =>
      rw [phaseAt_succ]
      simp [hfirst, grammarStep]
  | succ k ih =>
      rw [phaseAt_succ, ih]
      rfl

private theorem phaseAt_compatible {N : Nat} (y : Bitstring N)
    {k : Nat} (hpos : 0 < k) :
    PhaseCompatible (indexedBit y 0) (phaseAt y k) := by
  intro hfirst
  cases k with
  | zero => omega
  | succ k => exact phaseAt_succ_witness_of_first_true y hfirst k

private theorem backMarker_eq_saved (saved : Bool) (phase : GrammarPhase)
    (h : PhaseCompatible saved phase) :
    backMarker saved phase = saved := by
  cases saved <;> cases phase <;> simp [PhaseCompatible, backMarker] at h ⊢

/-! ## Exact transition bridges to the installed table -/

private theorem machine_step_start_some (b : Bool) :
    machine.step qStart (some b) =
      (forwardState b (grammarStep .needTag b), none, .right) := by
  cases b <;> rfl

private theorem machine_step_start_none :
    machine.step qStart none = (qReject, none, .stay) := by
  rfl

private theorem machine_step_forward (saved b : Bool) (phase : GrammarPhase)
    (h : PhaseCompatible saved phase) :
    machine.step (forwardState saved phase) (some b) =
      (forwardState saved (grammarStep phase b), some b, .right) := by
  cases saved <;> cases phase <;> cases b
  all_goals simp [PhaseCompatible] at h
  all_goals rfl

private theorem machine_step_forward_blank (saved : Bool) (phase : GrammarPhase) :
    machine.step (forwardState saved phase) none =
      (backState saved phase, none, .left) := by
  cases saved <;> cases phase <;> rfl

private theorem machine_step_back_some (saved b : Bool) (phase : GrammarPhase) :
    machine.step (backState saved phase) (some b) =
      (backState saved phase, some b, .left) := by
  cases saved <;> cases phase <;> cases b <;> rfl

private theorem machine_step_back_marker (saved : Bool) (phase : GrammarPhase) :
    machine.step (backState saved phase) none =
      (verdictState phase, some (backMarker saved phase), .stay) := by
  cases saved <;> cases phase <;> rfl

private theorem qStart_not_terminal :
    qStart ≠ machine.accept ∧ qStart ≠ machine.reject := by
  decide

private theorem forwardState_not_terminal (saved : Bool) (phase : GrammarPhase) :
    forwardState saved phase ≠ machine.accept ∧
      forwardState saved phase ≠ machine.reject := by
  cases saved <;> cases phase <;> decide

private theorem backState_not_terminal (saved : Bool) (phase : GrammarPhase) :
    backState saved phase ≠ machine.accept ∧
      backState saved phase ≠ machine.reject := by
  cases saved <;> cases phase <;> decide

/-! ## Forward and rewind positional invariants -/

/-- Positive forward times.  Cell zero is erased; it is not the initial tape. -/
def ForwardAt {N : Nat} (y : Bitstring N) (k : Nat)
    (c : Config parserStateCount N (clock N)) : Prop :=
  c.state = forwardState (indexedBit y 0) (phaseAt y k) ∧
  c.head.val = k ∧
  c.tape = erasedZeroTape y

/-- At time `N+1+j`, rewind has crossed exactly `j` preserved cells. -/
def BackAt {N : Nat} (y : Bitstring N) (j : Nat)
    (c : Config parserStateCount N (clock N)) : Prop :=
  c.state = backState (indexedBit y 0) (phaseAt y N) ∧
  c.head.val = N - 1 - j ∧
  c.tape = erasedZeroTape y

private theorem forward_one {N : Nat} (y : Bitstring N) (hN : 0 < N) :
    ForwardAt y 1 (machine.run 1 (exactInitial y)) := by
  have haction :
      machine.step (exactInitial y).state
          ((exactInitial y).tape (exactInitial y).head) =
        (forwardState (indexedBit y 0)
          (grammarStep .needTag (indexedBit y 0)), none, .right) := by
    rw [exactInitial_state, exactInitial_read_zero y hN]
    exact machine_step_start_some _
  change ForwardAt y 1 (machine.stepConfig (exactInitial y))
  constructor
  · rw [stepConfig_state, haction, phaseAt_succ]
    rfl
  constructor
  · rw [stepConfig_head, haction]
    have hright :
        (exactInitial y).head.val + 1 < tapeLength N (clock N) := by
      rw [exactInitial_head_val]
      unfold tapeLength clock
      omega
    unfold moveHead
    rw [dif_pos hright]
    exact congrArg (fun n : Nat => n + 1) (exactInitial_head_val y)
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i.val = 0
    · have hieq : i = (exactInitial y).head := by
        apply Fin.ext
        have hh := exactInitial_head_val y
        omega
      simp [hieq, erasedZeroTape]
    · have hine : i ≠ (exactInitial y).head := by
        intro hieq
        apply hi
        have hh := exactInitial_head_val y
        omega
      simp [hine, erasedZeroTape, hi]

private theorem forward_step {N : Nat} (y : Bitstring N)
    {k : Nat} {c : Config parserStateCount N (clock N)}
    (hInv : ForwardAt y k c) (hpos : 0 < k) (hlt : k < N) :
    ForwardAt y (k + 1) (machine.stepConfig c) := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  let ik : Fin (tapeLength N (clock N)) :=
    ⟨k, by simp [tapeLength, clock]; omega⟩
  have hheadEq : c.head = ik := Fin.ext hhead
  have hread : c.tape c.head = some (indexedBit y k) := by
    rw [htape, hheadEq]
    exact erasedZeroTape_input y hpos hlt _
  have hcompat := phaseAt_compatible y hpos
  have haction :
      machine.step c.state (c.tape c.head) =
        (forwardState (indexedBit y 0)
            (grammarStep (phaseAt y k) (indexedBit y k)),
          some (indexedBit y k), .right) := by
    rw [hstate, hread]
    exact machine_step_forward _ _ _ hcompat
  constructor
  · rw [stepConfig_state, haction, phaseAt_succ]
  constructor
  · rw [stepConfig_head, haction]
    have hright : c.head.val + 1 < tapeLength N (clock N) := by
      rw [hhead]
      unfold tapeLength clock
      omega
    unfold moveHead
    rw [dif_pos hright]
    exact congrArg (fun n : Nat => n + 1) hhead
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c.head
    · subst i
      simpa [htape] using hread.symm
    · simp [hi, htape]

/-- Universal forward trace.  Its range deliberately starts at time one,
because time zero still has the unmarked initial tape. -/
theorem run_forward {N : Nat} (y : Bitstring N) (r : Nat) :
    r + 1 ≤ N →
    ForwardAt y (r + 1) (machine.run (r + 1) (exactInitial y)) := by
  induction r with
  | zero =>
      intro h
      simpa using forward_one y (by omega)
  | succ r ih =>
      intro h
      have hPrev := ih (by omega)
      have hStep := forward_step y hPrev (by omega) (by omega)
      simpa [UniformTM.run, Nat.add_assoc] using hStep

private theorem forward_to_back {N : Nat} (y : Bitstring N)
    {c : Config parserStateCount N (clock N)}
    (hInv : ForwardAt y N c) :
    BackAt y 0 (machine.stepConfig c) := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  let iN : Fin (tapeLength N (clock N)) :=
    ⟨N, by unfold tapeLength clock; omega⟩
  have hheadEq : c.head = iN := Fin.ext hhead
  have hread : c.tape c.head = none := by
    rw [htape, hheadEq]
    exact erasedZeroTape_boundary y _
  have haction :
      machine.step c.state (c.tape c.head) =
        (backState (indexedBit y 0) (phaseAt y N), none, .left) := by
    rw [hstate, hread]
    exact machine_step_forward_blank _ _
  constructor
  · rw [stepConfig_state, haction]
  constructor
  · rw [stepConfig_head, haction]
    simp [moveHead, hheadEq, iN]
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c.head
    · subst i
      simpa [htape] using hread.symm
    · simp [hi, htape]

private theorem back_step {N : Nat} (y : Bitstring N)
    {j : Nat} {c : Config parserStateCount N (clock N)}
    (hInv : BackAt y j c) (hnext : j + 1 < N) :
    BackAt y (j + 1) (machine.stepConfig c) := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  have hpos : 0 < N - 1 - j := by omega
  have hlt : N - 1 - j < N := by omega
  let ip : Fin (tapeLength N (clock N)) :=
    ⟨N - 1 - j, by simp [tapeLength, clock]; omega⟩
  have hheadEq : c.head = ip := Fin.ext hhead
  have hread : c.tape c.head = some (indexedBit y (N - 1 - j)) := by
    rw [htape, hheadEq]
    exact erasedZeroTape_input y hpos hlt _
  have haction :
      machine.step c.state (c.tape c.head) =
        (backState (indexedBit y 0) (phaseAt y N),
          some (indexedBit y (N - 1 - j)), .left) := by
    rw [hstate, hread]
    exact machine_step_back_some _ _ _
  constructor
  · rw [stepConfig_state, haction]
  constructor
  · rw [stepConfig_head, haction]
    change c.head.val - 1 = N - 1 - (j + 1)
    rw [hhead]
    omega
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c.head
    · subst i
      simpa [htape] using hread.symm
    · simp [hi, htape]

/-- Universal rewind trace.  `j=0` is immediately after crossing the right
blank; `j=N-1` is at the erased marker in cell zero. -/
theorem run_back {N : Nat} (y : Bitstring N) (hN : 0 < N) (j : Nat) :
    j < N →
    BackAt y j (machine.run (N + 1 + j) (exactInitial y)) := by
  induction j with
  | zero =>
      intro _
      have hForward := run_forward y (N - 1) (by omega)
      have hpred : N - 1 + 1 = N := by omega
      have hForwardN : ForwardAt y N (machine.run N (exactInitial y)) := by
        simpa [hpred] using hForward
      have hBack := forward_to_back y hForwardN
      simpa [UniformTM.run] using hBack
  | succ j ih =>
      intro hj
      have hPrev := ih (by omega)
      have hStep := back_step y hPrev (by omega)
      rw [show N + 1 + (j + 1) = (N + 1 + j) + 1 by omega,
        UniformTM.run]
      exact hStep

/-- At the last nonterminal time, rewind has reached the unique erased marker
at zero; all positive input positions crossed on rewind contained `some`. -/
theorem rewind_reaches_zero_marker {N : Nat} (y : Bitstring N)
    (hN : 0 < N) :
    let c := machine.run (2 * N) (exactInitial y)
    BackAt y (N - 1) c ∧ c.head.val = 0 ∧ c.tape c.head = none := by
  let c := machine.run (2 * N) (exactInitial y)
  change BackAt y (N - 1) c ∧ c.head.val = 0 ∧ c.tape c.head = none
  have hBack := run_back y hN (N - 1) (by omega)
  have htime : N + 1 + (N - 1) = 2 * N := by omega
  rw [htime] at hBack
  change BackAt y (N - 1) c at hBack
  refine ⟨hBack, ?_, ?_⟩
  · exact hBack.2.1.trans (by omega)
  · rcases hBack with ⟨_, hhead, htape⟩
    rw [htape]
    have hheadZero : c.head.val = 0 := by omega
    simp [erasedZeroTape, hheadZero]

/-! ## Final transition and decoder classification -/

/-- Specification-only final control.  It is never consulted by the machine. -/
def expectedFinalState {N : Nat} (y : Bitstring N) :
    Fin parserStateCount :=
  match decodePair y with
  | some _ => qAccept
  | none => qReject

theorem verdictState_phaseAt_eq_expected {N : Nat} (y : Bitstring N) :
    verdictState (phaseAt y N) = expectedFinalState y := by
  rw [phaseAt_length]
  have hsyntax := syntaxOK_ofFn_eq_decodePair_isSome y
  generalize hphase : grammarRun GrammarPhase.needTag (List.ofFn y) = phase
  cases phase <;> cases hdecode : decodePair y <;>
    simp [syntaxOK, hphase, hdecode, verdictState, expectedFinalState] at hsyntax ⊢

private theorem back_to_final {N : Nat} (y : Bitstring N)
    (hN : 0 < N) {c : Config parserStateCount N (clock N)}
    (hInv : BackAt y (N - 1) c) :
    let d := machine.stepConfig c
    d.state = expectedFinalState y ∧
      d.head.val = 0 ∧
      d.tape = (exactInitial y).tape := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  have hheadZero : c.head.val = 0 := by omega
  have hread : c.tape c.head = none := by
    rw [htape]
    unfold erasedZeroTape
    simp [hheadZero]
  have hcompat := phaseAt_compatible y hN
  have hmarker : backMarker (indexedBit y 0) (phaseAt y N) = indexedBit y 0 :=
    backMarker_eq_saved _ _ hcompat
  have haction :
      machine.step c.state (c.tape c.head) =
        (verdictState (phaseAt y N), some (indexedBit y 0), .stay) := by
    rw [hstate, hread, machine_step_back_marker, hmarker]
  dsimp
  constructor
  · rw [haction]
    exact verdictState_phaseAt_eq_expected y
  constructor
  · rw [haction]
    exact hheadZero
  · calc
      (machine.stepConfig c).tape =
          (fun i : Fin (tapeLength N (clock N)) =>
            if i.val = 0 then some (indexedBit y 0)
            else erasedZeroTape y i) := by
        funext i
        rw [stepConfig_tape, haction, htape]
        have hieq : i = c.head ↔ i.val = 0 := by
          constructor
          · intro h
            simpa [h] using hheadZero
          · intro h
            apply Fin.ext
            omega
        simp only [hieq]
      _ = (exactInitial y).tape := restore_erasedZeroTape y hN

/-- Dedicated empty-input execution.  Its one deadline transition rejects,
keeps the head at zero, and preserves the complete exact-budget tape. -/
theorem run_empty_at_clock (y : Bitstring 0) :
    let c₀ := initialConfig machine (clock 0) y
    let cF := machine.run (clock 0) c₀
    cF.state = qReject ∧ cF.head.val = 0 ∧ cF.tape = c₀.tape := by
  let c0 : Config parserStateCount 0 (clock 0) :=
    initialConfig machine (clock 0) y
  have hread : c0.tape c0.head = none := by
    simp [c0, initialConfig]
  have haction :
      machine.step c0.state (c0.tape c0.head) =
        (qReject, none, .stay) := by
    rw [show c0.state = qStart by rfl, hread]
    exact machine_step_start_none
  change
    (machine.stepConfig c0).state = qReject ∧
      (machine.stepConfig c0).head.val = 0 ∧
      (machine.stepConfig c0).tape = c0.tape
  constructor
  · rw [stepConfig_state, haction]
  constructor
  · rw [stepConfig_head, haction]
    change c0.head.val = 0
    rfl
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c0.head
    · rw [if_pos hi, hi, hread]
    · rw [if_neg hi]

/-- Exact final state, head position, and full allocated tape. -/
theorem run_initialConfig_fields {N : Nat} (y : Bitstring N) :
    let c₀ := exactInitial y
    let cF := machine.run (clock N) c₀
    cF.state = expectedFinalState y ∧
      cF.head.val = 0 ∧
      cF.tape = c₀.tape := by
  cases N with
  | zero =>
      have hdecode : decodePair y = none := by
        simp [decodePair, decodePairList]
      simpa [exactInitial, expectedFinalState, hdecode] using
        run_empty_at_clock y
  | succ N =>
      have hN : 0 < N + 1 := by omega
      have hBack := run_back y hN N (by omega)
      have htime : N + 1 + 1 + N = 2 * (N + 1) := by omega
      rw [htime] at hBack
      have hFinal := back_to_final y hN hBack
      simpa [clock, UniformTM.run] using hFinal

/-- Required exact full-configuration theorem.  The record update changes only
the state, so this simultaneously states head restoration and equality on all
`3*N+2` tape cells, including padding. -/
theorem run_initialConfig_exact {N : Nat} (y : Bitstring N) :
    machine.run (clock N) (initialConfig machine (clock N) y) =
      { initialConfig machine (clock N) y with
        state := expectedFinalState y } := by
  have h := run_initialConfig_fields y
  apply config_ext
  · exact h.1
  · apply Fin.ext
    exact h.2.1
  · exact h.2.2

/-- Strict first-terminal theorem.  `N=0` is included: its sole earlier time is
zero, while literal rejection occurs at time one. -/
theorem noEarlyTerminal_initialConfig {N : Nat} (y : Bitstring N)
    (steps : Nat) (hsteps : steps < clock N) :
    let c := machine.run steps (initialConfig machine (clock N) y)
    c.state ≠ machine.accept ∧ c.state ≠ machine.reject := by
  change (machine.run steps (exactInitial y)).state ≠ machine.accept ∧
    (machine.run steps (exactInitial y)).state ≠ machine.reject
  cases N with
  | zero =>
      have hs : steps = 0 := by simp [clock] at hsteps; omega
      subst steps
      simpa [exactInitial, UniformTM.run] using qStart_not_terminal
  | succ N =>
      have hN : 0 < N + 1 := by omega
      by_cases hs0 : steps = 0
      · subst steps
        simpa [exactInitial, UniformTM.run] using qStart_not_terminal
      · by_cases hforward : steps ≤ N + 1
        · obtain ⟨r, hr⟩ : ∃ r, steps = r + 1 :=
            ⟨steps - 1, by omega⟩
          subst steps
          have hInv := run_forward y r hforward
          rw [hInv.1]
          exact forwardState_not_terminal _ _
        · let j := steps - (N + 1 + 1)
          have hj : j < N + 1 := by
            dsimp [j]
            simp [clock] at hsteps
            omega
          have htime : steps = (N + 1) + 1 + j := by
            dsimp [j]
            omega
          rw [htime]
          have hInv := run_back y hN j hj
          rw [hInv.1]
          exact backState_not_terminal _ _

/-- Predicate-level form of strict preterminality. -/
theorem no_public_terminal_before_clock {N : Nat} (y : Bitstring N)
    (steps : Nat) (hsteps : steps < clock N) :
    ¬ AcceptsAt machine (clock N) steps y ∧
      ¬ RejectsAt machine (clock N) steps y := by
  simpa [AcceptsAt, RejectsAt] using
    noEarlyTerminal_initialConfig y steps hsteps

theorem head_zero_at_clock {N : Nat} (y : Bitstring N) :
    (machine.run (clock N)
      (initialConfig machine (clock N) y)).head.val = 0 :=
  (run_initialConfig_fields y).2.1

theorem tape_restored_at_clock {N : Nat} (y : Bitstring N) :
    (machine.run (clock N)
      (initialConfig machine (clock N) y)).tape =
        (initialConfig machine (clock N) y).tape :=
  (run_initialConfig_fields y).2.2

theorem final_state_at_clock {N : Nat} (y : Bitstring N) :
    (machine.run (clock N)
      (initialConfig machine (clock N) y)).state = expectedFinalState y :=
  (run_initialConfig_fields y).1

/-- The same literal classification stated directly through the independent
grammar DFA, before the decoder-facing wrappers. -/
theorem final_state_at_clock_syntax {N : Nat} (y : Bitstring N) :
    (machine.run (clock N)
      (initialConfig machine (clock N) y)).state =
        if syntaxOK (List.ofFn y) then qAccept else qReject := by
  rw [final_state_at_clock]
  have h := syntaxOK_ofFn_eq_decodePair_isSome y
  cases hs : syntaxOK (List.ofFn y) <;> cases hd : decodePair y <;>
    simp [hs, hd, expectedFinalState] at h ⊢

/-! ## Literal exact and within-budget decision contracts -/

theorem acceptsAt_clock_iff_decodePair_some {N : Nat} (y : Bitstring N) :
    AcceptsAt machine (clock N) (clock N) y ↔
      ∃ p : DecodedPair, decodePair y = some p := by
  rw [AcceptsAt, final_state_at_clock]
  cases h : decodePair y with
  | none =>
      have hne : qReject ≠ machine.accept := by
        intro heq
        exact machine.accept_ne_reject heq.symm
      simp [expectedFinalState, h, hne]
  | some p => simp [expectedFinalState, h, machine]

theorem rejectsAt_clock_iff_decodePair_none {N : Nat} (y : Bitstring N) :
    RejectsAt machine (clock N) (clock N) y ↔
      decodePair y = none := by
  rw [RejectsAt, final_state_at_clock]
  cases h : decodePair y with
  | none => simp [expectedFinalState, h, machine]
  | some p =>
      have hne : qAccept ≠ machine.reject := machine.accept_ne_reject
      simp [expectedFinalState, h, hne]

/-- Exact decision at the literal deadline and exact tape budget. -/
theorem decidesAt_clock {N : Nat} (y : Bitstring N) :
    DecidesAt machine (clock N) (clock N) y (decodePair y).isSome := by
  cases h : decodePair y with
  | none =>
      simp [DecidesAt]
      exact (rejectsAt_clock_iff_decodePair_none y).2 h
  | some p =>
      simp [DecidesAt]
      exact (acceptsAt_clock_iff_decodePair_some y).2 ⟨p, h⟩

/-- Exact decision phrased with the independently computed DFA answer. -/
theorem decidesAt_clock_syntax {N : Nat} (y : Bitstring N) :
    DecidesAt machine (clock N) (clock N) y
      (syntaxOK (List.ofFn y)) := by
  rw [syntaxOK_ofFn_eq_decodePair_isSome]
  exact decidesAt_clock y

/-- Within-budget decision is derived from the exact-deadline theorem; it is
not used as a substitute for exact execution. -/
theorem decidesWithin_clock {N : Nat} (y : Bitstring N) :
    DecidesWithin machine (clock N) y (decodePair y).isSome :=
  (decidesAt_budget_iff_decidesWithin machine y (decodePair y).isSome).1
    (decidesAt_clock y)

/-- Bundled fixed-budget execution and decoder classification at the exact clock. -/
theorem exact_execution_initialConfig {N : Nat} (y : Bitstring N) :
    let c₀ := initialConfig machine (clock N) y
    let cF := machine.run (clock N) c₀
    (cF = { c₀ with state := expectedFinalState y }) ∧
    (∀ steps, steps < clock N →
      let c := machine.run steps c₀
      c.state ≠ machine.accept ∧ c.state ≠ machine.reject) ∧
    cF.head.val = 0 ∧
    cF.tape = c₀.tape ∧
    ((cF.state = machine.accept) ↔
      ∃ p : DecodedPair, decodePair y = some p) ∧
    ((cF.state = machine.reject) ↔ decodePair y = none) ∧
    (AcceptsAt machine (clock N) (clock N) y ↔
      ∃ p : DecodedPair, decodePair y = some p) ∧
    (RejectsAt machine (clock N) (clock N) y ↔ decodePair y = none) ∧
    DecidesAt machine (clock N) (clock N) y (decodePair y).isSome ∧
    DecidesWithin machine (clock N) y (decodePair y).isSome := by
  dsimp
  refine ⟨run_initialConfig_exact y, noEarlyTerminal_initialConfig y,
    head_zero_at_clock y, tape_restored_at_clock y, ?_, ?_,
    acceptsAt_clock_iff_decodePair_some y,
    rejectsAt_clock_iff_decodePair_none y,
    decidesAt_clock y, decidesWithin_clock y⟩
  · simpa [AcceptsAt] using acceptsAt_clock_iff_decodePair_some y
  · simpa [RejectsAt] using rejectsAt_clock_iff_decodePair_none y

end Pnp3.Complexity.Uniform.V1.FixedPairParser
