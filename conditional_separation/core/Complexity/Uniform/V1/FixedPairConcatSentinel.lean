import Complexity.Uniform.V1.PolynomialTime
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Fixed pair-concat sentinel phase (Part A, first operational sub-slice)

This module installs one closed seven-state `UniformTM` that prepares a raw
word for the later destructive pair-concat (compaction) machine.  Starting
from `initialConfig`, on every finite raw word `x : Bitstring N` and on every
tape budget `B`, the machine

* saves the first symbol in finite control and blanks the origin cell, so a
  literal `some false` input bit is never confused with the blank `none`;
* scans right over the raw word, writes the right-end marker `some true` at
  cell `N` (the first blank cell after the input), rewinds to the unique blank
  at the origin, restores the saved symbol, and stops at head zero in literal
  accept.

**Final layout.**  The final tape is `[input][marker]` followed by the
untouched blank suffix: cells `0..N-1` hold the raw input exactly, cell `N`
holds the single-cell marker `some true`, and every cell above `N` is `none`.
There is no separate two-cell `[end-marker][sentinel]` trailer.  When `0 < B`,
cell `N+1` exists and is proved blank; a later compactor may then recognise the
marker by one-cell lookahead (`some` followed by `none`).  At budget zero that
cell does not exist, so the all-budget exact theorem is not by itself a reusable
lookahead handoff.  A marker value alone cannot be distinguished from an input
bit in the three-symbol alphabet `Option Bool`.

**Clock.**  `clock N = N + 1 + N = 2 * N + 1` is read off the transition
trace: `N` scanning transitions reach cell `N`, one transition writes the
marker, and `N` rewinding transitions (of which the last restores the origin)
return to cell zero.  `N = 0` has the single transition that writes the
marker at the origin and accepts.

**Footprint.**  All footprint results hold for every budget `B`, including
`B = 0`. The head never exceeds cell `N`, every cell above `N` stays blank
throughout, no transition relies on the boundary clamp of `moveHead`, and state, head,
and every common tape cell at every time through the clock are literally
independent of `B`.  Consequently the ambient budget is not hidden advice: it
is consulted neither by the control nor by the trace.

**Public surface.**  The state count, the seven control names, the machine,
the clock, the layout `sentinelTape`, and the handoff `sentinelConfig`; the
table, clock, and resource pins; the exact full-configuration theorem
`run_initialConfig_exact` with its pointwise tape corollary; the footprint,
budget-independence, and no-clamp theorems; strict preterminality; literal
acceptance and never-reject; `DecidesWithin` at the repository `polyClock`;
and one bundled handoff contract.  Every phase representation and every trace
description is private.

**Non-claims.**  This is the sentinel phase only.  It does not remove tags or
the separator, does not shift any input symbol, does not evaluate any
relation, and does not claim that the pair compactor is complete.  It imports
no pair-grammar module; the only connection to pair words is the intended
reuse of its five work rows and its exact handoff configuration.
-/

namespace Pnp3.Complexity.Uniform.V1

namespace FixedPairConcatSentinel

/-- Five working controls followed by two public verdict controls. -/
abbrev sentinelStateCount : Nat := 7

def qStart : Fin sentinelStateCount :=
  ⟨0, by decide⟩

def qScanF : Fin sentinelStateCount :=
  ⟨1, by decide⟩

def qScanT : Fin sentinelStateCount :=
  ⟨2, by decide⟩

def qBackF : Fin sentinelStateCount :=
  ⟨3, by decide⟩

def qBackT : Fin sentinelStateCount :=
  ⟨4, by decide⟩

def qAccept : Fin sentinelStateCount :=
  ⟨5, by decide⟩

def qReject : Fin sentinelStateCount :=
  ⟨6, by decide⟩

/-!
Row zero saves the first symbol in finite control and erases the origin.  The
two scan rows preserve every scanned symbol and write the marker at the first
blank.  The two rewind rows preserve every scanned symbol and restore the
saved symbol at the blank origin.  Row zero on a blank is the `N = 0` case:
the marker is written at the origin and the machine accepts at once.
-/
private def sentinelRawStep
    (q : Fin sentinelStateCount)
    (scanned : Option Bool) :
    Fin sentinelStateCount × Option Bool × Move :=
  match q.val with
  | 0 =>
      match scanned with
      | none =>
          (qAccept, some true, .stay)
      | some false =>
          (qScanF, none, .right)
      | some true =>
          (qScanT, none, .right)
  | 1 =>
      match scanned with
      | none =>
          (qBackF, some true, .left)
      | some b =>
          (qScanF, some b, .right)
  | 2 =>
      match scanned with
      | none =>
          (qBackT, some true, .left)
      | some b =>
          (qScanT, some b, .right)
  | 3 =>
      match scanned with
      | none =>
          (qAccept, some false, .stay)
      | some b =>
          (qBackF, some b, .left)
  | 4 =>
      match scanned with
      | none =>
          (qAccept, some true, .stay)
      | some b =>
          (qBackT, some b, .left)
  | 5 =>
      (qAccept, scanned, .stay)
  | _ =>
      (qReject, scanned, .stay)

/-- The fixed seven-state standalone sentinel machine. -/
def machine : UniformTM where
  stateCount := sentinelStateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := sentinelRawStep

/-- One theorem pins every row of the installed raw transition table. -/
theorem machine_rawStep_table :
    (∀ scanned,
      machine.rawStep qStart scanned =
        match scanned with
        | none => (qAccept, some true, .stay)
        | some false => (qScanF, none, .right)
        | some true => (qScanT, none, .right)) ∧
    (∀ scanned,
      machine.rawStep qScanF scanned =
        match scanned with
        | none => (qBackF, some true, .left)
        | some b => (qScanF, some b, .right)) ∧
    (∀ scanned,
      machine.rawStep qScanT scanned =
        match scanned with
        | none => (qBackT, some true, .left)
        | some b => (qScanT, some b, .right)) ∧
    (∀ scanned,
      machine.rawStep qBackF scanned =
        match scanned with
        | none => (qAccept, some false, .stay)
        | some b => (qBackF, some b, .left)) ∧
    (∀ scanned,
      machine.rawStep qBackT scanned =
        match scanned with
        | none => (qAccept, some true, .stay)
        | some b => (qBackT, some b, .left)) ∧
    (∀ scanned,
      machine.rawStep qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned,
      machine.rawStep qReject scanned = (qReject, scanned, .stay)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro scanned
    cases scanned with
    | none => rfl
    | some b => cases b <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    rfl
  · intro scanned
    rfl

/-- Exact deadline: `N` scanning transitions, one marker transition, and `N`
rewinding transitions. -/
def clock (N : Nat) : Nat :=
  N + 1 + N

theorem clock_eq (N : Nat) : clock N = 2 * N + 1 := by
  unfold clock
  omega

/-- Closed finite-control, raw-table, and clock resource pins. -/
theorem machine_resource_pins :
    machine.stateCount = 7 ∧
    machine.start = qStart ∧
    machine.accept = qAccept ∧
    machine.reject = qReject ∧
    qStart.val = 0 ∧
    qScanF.val = 1 ∧
    qScanT.val = 2 ∧
    qBackF.val = 3 ∧
    qBackT.val = 4 ∧
    qAccept.val = 5 ∧
    qReject.val = 6 ∧
    (∀ N, clock N = 2 * N + 1) ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 21 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, clock_eq, ?_⟩
  change Fintype.card (Fin 7 × Option Bool) = 21
  decide

/-! ## Layout and handoff configuration -/

/-- The final layout `[input][marker]` followed by blanks, on the complete
`N + B + 1` allocation. -/
def sentinelTape {N : Nat} (B : Nat) (x : Bitstring N) :
    Fin (tapeLength N B) → Option Bool :=
  fun i =>
    if h : i.val < N then some (x ⟨i.val, h⟩)
    else if i.val = N then some true
    else none

/-- The exact handoff configuration: literal accept, head at the origin, and
the sentinel layout. -/
def sentinelConfig {N : Nat} (B : Nat) (x : Bitstring N) :
    Config sentinelStateCount N B where
  state := qAccept
  head := ⟨0, by unfold tapeLength; omega⟩
  tape := sentinelTape B x

/-! ## Private specification tapes and controls -/

/-- Total view of an indexed input.  Only indices below `N` are consulted. -/
private def bitAt {N : Nat} (x : Bitstring N) (i : Nat) : Bool :=
  if h : i < N then x ⟨i, h⟩ else false

private theorem sentinelTape_beyond {N B : Nat} (x : Bitstring N)
    (j : Fin (tapeLength N B)) (hj : N < j.val) :
    sentinelTape B x j = none := by
  have hnot : ¬ j.val < N := by omega
  have hne : j.val ≠ N := by omega
  simp [sentinelTape, hnot, hne]

/-- The actual scan tape: the initial tape with the origin erased. -/
private def erasedZeroTape {N : Nat} (B : Nat) (x : Bitstring N) :
    Fin (tapeLength N B) → Option Bool :=
  fun i => if i.val = 0 then none else (initialConfig machine B x).tape i

/-- The actual rewind tape: the sentinel tape with the origin erased. -/
private def erasedZeroMarkedTape {N : Nat} (B : Nat) (x : Bitstring N) :
    Fin (tapeLength N B) → Option Bool :=
  fun i => if i.val = 0 then none else sentinelTape B x i

/-- Scan control carrying the saved first symbol. -/
private def scanState (saved : Bool) : Fin sentinelStateCount :=
  if saved then qScanT else qScanF

/-- Rewind control carrying the saved first symbol. -/
private def backState (saved : Bool) : Fin sentinelStateCount :=
  if saved then qBackT else qBackF

@[simp] private theorem initialConfig_state {N B : Nat} (x : Bitstring N) :
    (initialConfig machine B x).state = qStart :=
  rfl

@[simp] private theorem initialConfig_head_val {N B : Nat} (x : Bitstring N) :
    (initialConfig machine B x).head.val = 0 :=
  rfl

private theorem initial_read_zero {N B : Nat} (x : Bitstring N) (hN : 0 < N) :
    (initialConfig machine B x).tape (initialConfig machine B x).head =
      some (bitAt x 0) := by
  simp [initialConfig, bitAt, hN]

private theorem erasedZeroTape_input {N B : Nat} (x : Bitstring N)
    {i : Nat} (hpos : 0 < i) (hi : i < N)
    (hfit : i < tapeLength N B) :
    erasedZeroTape B x ⟨i, hfit⟩ = some (bitAt x i) := by
  simp [erasedZeroTape, initialConfig, bitAt, hpos.ne', hi]

private theorem erasedZeroTape_boundary {N B : Nat} (x : Bitstring N)
    (hfit : N < tapeLength N B) :
    erasedZeroTape B x ⟨N, hfit⟩ = none := by
  by_cases hN : N = 0
  · subst N
    simp [erasedZeroTape]
  · simp [erasedZeroTape, initialConfig, hN]

private theorem erasedZeroTape_beyond {N B : Nat} (x : Bitstring N)
    (j : Fin (tapeLength N B)) (hj : N < j.val) :
    erasedZeroTape B x j = none := by
  have hnot : ¬ j.val < N := by omega
  simp [erasedZeroTape, initialConfig, hnot]

private theorem erasedZeroMarkedTape_input {N B : Nat} (x : Bitstring N)
    {i : Nat} (hpos : 0 < i) (hi : i < N)
    (hfit : i < tapeLength N B) :
    erasedZeroMarkedTape B x ⟨i, hfit⟩ = some (bitAt x i) := by
  simp [erasedZeroMarkedTape, sentinelTape, bitAt, hpos.ne', hi]

private theorem erasedZeroMarkedTape_zero {N B : Nat} (x : Bitstring N)
    {i : Fin (tapeLength N B)} (hi : i.val = 0) :
    erasedZeroMarkedTape B x i = none := by
  simp [erasedZeroMarkedTape, hi]

private theorem erasedZeroMarkedTape_beyond {N B : Nat} (x : Bitstring N)
    (j : Fin (tapeLength N B)) (hj : N < j.val) :
    erasedZeroMarkedTape B x j = none := by
  have hne : j.val ≠ 0 := by omega
  simp [erasedZeroMarkedTape, hne, sentinelTape_beyond x j hj]

/-- Writing the marker at cell `N` on the scan tape gives the rewind tape. -/
private theorem mark_erasedZeroTape {N B : Nat} (x : Bitstring N) (hN : 0 < N) :
    (fun i : Fin (tapeLength N B) =>
      if i.val = N then some true else erasedZeroTape B x i) =
      erasedZeroMarkedTape B x := by
  funext i
  by_cases hiN : i.val = N
  · simp [hiN, erasedZeroMarkedTape, sentinelTape, hN.ne']
  · by_cases hi0 : i.val = 0
    · simp [hi0, erasedZeroTape, erasedZeroMarkedTape, hN.ne]
    · simp [hiN, hi0, erasedZeroTape, erasedZeroMarkedTape, sentinelTape,
        initialConfig]

/-- Restoring the saved first symbol at the origin of the rewind tape gives
the complete sentinel layout, including every blank cell above `N`. -/
private theorem restore_erasedZeroMarkedTape {N B : Nat} (x : Bitstring N)
    (hN : 0 < N) :
    (fun i : Fin (tapeLength N B) =>
      if i.val = 0 then some (bitAt x 0) else erasedZeroMarkedTape B x i) =
      sentinelTape B x := by
  funext i
  by_cases hi : i.val = 0
  · simp [hi, sentinelTape, bitAt, hN]
  · simp [hi, erasedZeroMarkedTape]

/-! ## Private transition bridges to the installed table -/

private theorem machine_step_start_some (b : Bool) :
    machine.step qStart (some b) = (scanState b, none, .right) := by
  cases b <;> rfl

private theorem machine_step_start_none :
    machine.step qStart none = (qAccept, some true, .stay) := by
  rfl

private theorem machine_step_scan_some (saved b : Bool) :
    machine.step (scanState saved) (some b) =
      (scanState saved, some b, .right) := by
  cases saved <;> cases b <;> rfl

private theorem machine_step_scan_none (saved : Bool) :
    machine.step (scanState saved) none =
      (backState saved, some true, .left) := by
  cases saved <;> rfl

private theorem machine_step_back_some (saved b : Bool) :
    machine.step (backState saved) (some b) =
      (backState saved, some b, .left) := by
  cases saved <;> cases b <;> rfl

private theorem machine_step_back_none (saved : Bool) :
    machine.step (backState saved) none =
      (qAccept, some saved, .stay) := by
  cases saved <;> rfl

private theorem scanState_val_lt (saved : Bool) :
    (scanState saved).val < 5 := by
  cases saved <;> decide

private theorem backState_val_lt (saved : Bool) :
    (backState saved).val < 5 := by
  cases saved <;> decide

/-! ## Private extensional and projection lemmas -/

private theorem config_ext
    {N B : Nat} {c d : Config sentinelStateCount N B}
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

private theorem stepConfig_state
    {N B : Nat} (c : Config sentinelStateCount N B) :
    (machine.stepConfig c).state =
      (machine.step c.state (c.tape c.head)).1 :=
  rfl

private theorem stepConfig_head
    {N B : Nat} (c : Config sentinelStateCount N B) :
    (machine.stepConfig c).head =
      moveHead c.head (machine.step c.state (c.tape c.head)).2.2 :=
  rfl

private theorem stepConfig_tape
    {N B : Nat} (c : Config sentinelStateCount N B)
    (i : Fin (tapeLength N B)) :
    (machine.stepConfig c).tape i =
      if i = c.head
      then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i :=
  rfl

/-! ## Private scan and rewind positional invariants -/

/-- Positive scan times.  The origin is erased and the saved symbol is in
control; every other cell is exactly its initial cell. -/
private def ScanAt {N : Nat} (B : Nat) (x : Bitstring N) (k : Nat)
    (c : Config sentinelStateCount N B) : Prop :=
  c.state = scanState (bitAt x 0) ∧
  c.head.val = k ∧
  c.tape = erasedZeroTape B x

/-- At time `N + 1 + j`, the marker is in place and the rewind has crossed
exactly `j` preserved cells. -/
private def BackAt {N : Nat} (B : Nat) (x : Bitstring N) (j : Nat)
    (c : Config sentinelStateCount N B) : Prop :=
  c.state = backState (bitAt x 0) ∧
  c.head.val = N - 1 - j ∧
  c.tape = erasedZeroMarkedTape B x

private theorem scan_one {N B : Nat} (x : Bitstring N) (hN : 0 < N) :
    ScanAt B x 1 (machine.run 1 (initialConfig machine B x)) := by
  have haction :
      machine.step (initialConfig machine B x).state
          ((initialConfig machine B x).tape (initialConfig machine B x).head) =
        (scanState (bitAt x 0), none, .right) := by
    rw [initialConfig_state, initial_read_zero x hN]
    exact machine_step_start_some _
  change ScanAt B x 1 (machine.stepConfig (initialConfig machine B x))
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state, haction]
  · rw [stepConfig_head, haction]
    have hright :
        (initialConfig machine B x).head.val + 1 < tapeLength N B := by
      rw [initialConfig_head_val]
      unfold tapeLength
      omega
    unfold moveHead
    rw [dif_pos hright]
    exact congrArg (fun n : Nat => n + 1) (initialConfig_head_val x)
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i.val = 0
    · have hieq : i = (initialConfig machine B x).head := by
        apply Fin.ext
        rw [hi, initialConfig_head_val]
      rw [if_pos hieq]
      simp [erasedZeroTape, hi]
    · have hine : i ≠ (initialConfig machine B x).head := by
        intro hieq
        apply hi
        rw [hieq, initialConfig_head_val]
      rw [if_neg hine]
      simp [erasedZeroTape, hi]

private theorem scan_step {N B : Nat} (x : Bitstring N)
    {k : Nat} {c : Config sentinelStateCount N B}
    (hInv : ScanAt B x k c) (hpos : 0 < k) (hlt : k < N) :
    ScanAt B x (k + 1) (machine.stepConfig c) := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  have hfit : k < tapeLength N B := by
    unfold tapeLength
    omega
  have hheadEq : c.head = ⟨k, hfit⟩ := Fin.ext hhead
  have hread : c.tape c.head = some (bitAt x k) := by
    rw [htape, hheadEq]
    exact erasedZeroTape_input x hpos hlt hfit
  have haction :
      machine.step c.state (c.tape c.head) =
        (scanState (bitAt x 0), some (bitAt x k), .right) := by
    rw [hstate, hread]
    exact machine_step_scan_some _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state, haction]
  · rw [stepConfig_head, haction]
    have hright : c.head.val + 1 < tapeLength N B := by
      rw [hhead]
      unfold tapeLength
      omega
    unfold moveHead
    rw [dif_pos hright]
    exact congrArg (fun n : Nat => n + 1) hhead
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c.head
    · subst hi
      simpa [htape] using hread.symm
    · simp [hi, htape]

/-- Universal scan trace.  Its range starts at time one, because time zero
still has the unmarked initial tape. -/
private theorem run_scan {N B : Nat} (x : Bitstring N) (r : Nat) :
    r + 1 ≤ N →
    ScanAt B x (r + 1) (machine.run (r + 1) (initialConfig machine B x)) := by
  induction r with
  | zero =>
      intro h
      exact scan_one x (by omega)
  | succ r ih =>
      intro h
      have hPrev := ih (by omega)
      have hStep := scan_step x hPrev (by omega) (by omega)
      rw [UniformTM.run]
      exact hStep

private theorem scan_to_back {N B : Nat} (x : Bitstring N) (hN : 0 < N)
    {c : Config sentinelStateCount N B}
    (hInv : ScanAt B x N c) :
    BackAt B x 0 (machine.stepConfig c) := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  have hfit : N < tapeLength N B := by
    unfold tapeLength
    omega
  have hheadEq : c.head = ⟨N, hfit⟩ := Fin.ext hhead
  have hread : c.tape c.head = none := by
    rw [htape, hheadEq]
    exact erasedZeroTape_boundary x hfit
  have haction :
      machine.step c.state (c.tape c.head) =
        (backState (bitAt x 0), some true, .left) := by
    rw [hstate, hread]
    exact machine_step_scan_none _
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state, haction]
  · rw [stepConfig_head, haction]
    change c.head.val - 1 = N - 1 - 0
    omega
  · calc
      (machine.stepConfig c).tape =
          (fun i : Fin (tapeLength N B) =>
            if i.val = N then some true else erasedZeroTape B x i) := by
        funext i
        rw [stepConfig_tape, haction, htape]
        have hieq : i = c.head ↔ i.val = N := by
          constructor
          · intro h
            rw [h, hhead]
          · intro h
            apply Fin.ext
            rw [h, hhead]
        simp only [hieq]
      _ = erasedZeroMarkedTape B x := mark_erasedZeroTape x hN

private theorem back_step {N B : Nat} (x : Bitstring N)
    {j : Nat} {c : Config sentinelStateCount N B}
    (hInv : BackAt B x j c) (hnext : j + 1 < N) :
    BackAt B x (j + 1) (machine.stepConfig c) := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  have hpos : 0 < N - 1 - j := by omega
  have hlt : N - 1 - j < N := by omega
  have hfit : N - 1 - j < tapeLength N B := by
    unfold tapeLength
    omega
  have hheadEq : c.head = ⟨N - 1 - j, hfit⟩ := Fin.ext hhead
  have hread : c.tape c.head = some (bitAt x (N - 1 - j)) := by
    rw [htape, hheadEq]
    exact erasedZeroMarkedTape_input x hpos hlt hfit
  have haction :
      machine.step c.state (c.tape c.head) =
        (backState (bitAt x 0), some (bitAt x (N - 1 - j)), .left) := by
    rw [hstate, hread]
    exact machine_step_back_some _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [stepConfig_state, haction]
  · rw [stepConfig_head, haction]
    change c.head.val - 1 = N - 1 - (j + 1)
    omega
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c.head
    · subst hi
      simpa [htape] using hread.symm
    · simp [hi, htape]

/-- Universal rewind trace.  `j = 0` is immediately after writing the marker;
`j = N - 1` is at the erased origin. -/
private theorem run_back {N B : Nat} (x : Bitstring N) (hN : 0 < N) (j : Nat) :
    j < N →
    BackAt B x j (machine.run (N + 1 + j) (initialConfig machine B x)) := by
  induction j with
  | zero =>
      intro _
      have hScan := run_scan (B := B) x (N - 1) (by omega)
      have hpred : N - 1 + 1 = N := by omega
      rw [hpred] at hScan
      have hBack := scan_to_back x hN hScan
      rw [Nat.add_zero, UniformTM.run]
      exact hBack
  | succ j ih =>
      intro hj
      have hPrev := ih (by omega)
      have hStep := back_step x hPrev (by omega)
      rw [show N + 1 + (j + 1) = (N + 1 + j) + 1 by omega, UniformTM.run]
      exact hStep

private theorem back_to_final {N B : Nat} (x : Bitstring N) (hN : 0 < N)
    {j : Nat} {c : Config sentinelStateCount N B}
    (hInv : BackAt B x j c) (hj : N = j + 1) :
    machine.stepConfig c = sentinelConfig B x := by
  rcases hInv with ⟨hstate, hhead, htape⟩
  have hheadZero : c.head.val = 0 := by omega
  have hread : c.tape c.head = none := by
    rw [htape]
    exact erasedZeroMarkedTape_zero x hheadZero
  have haction :
      machine.step c.state (c.tape c.head) =
        (qAccept, some (bitAt x 0), .stay) := by
    rw [hstate, hread]
    exact machine_step_back_none _
  apply config_ext
  · rw [stepConfig_state, haction]
    rfl
  · apply Fin.ext
    rw [stepConfig_head, haction]
    exact hheadZero
  · calc
      (machine.stepConfig c).tape =
          (fun i : Fin (tapeLength N B) =>
            if i.val = 0 then some (bitAt x 0)
            else erasedZeroMarkedTape B x i) := by
        funext i
        rw [stepConfig_tape, haction, htape]
        have hieq : i = c.head ↔ i.val = 0 := by
          constructor
          · intro h
            rw [h, hheadZero]
          · intro h
            apply Fin.ext
            rw [h, hheadZero]
        simp only [hieq]
      _ = sentinelTape B x := restore_erasedZeroMarkedTape x hN

/-- Dedicated empty-input execution: the one deadline transition writes the
marker at the origin, stays, and accepts. -/
private theorem run_empty (B : Nat) (x : Bitstring 0) :
    machine.run (clock 0) (initialConfig machine B x) = sentinelConfig B x := by
  have hread :
      (initialConfig machine B x).tape (initialConfig machine B x).head = none := by
    simp [initialConfig]
  have haction :
      machine.step (initialConfig machine B x).state
          ((initialConfig machine B x).tape (initialConfig machine B x).head) =
        (qAccept, some true, .stay) := by
    rw [initialConfig_state, hread]
    exact machine_step_start_none
  change machine.stepConfig (initialConfig machine B x) = sentinelConfig B x
  apply config_ext
  · rw [stepConfig_state, haction]
    rfl
  · apply Fin.ext
    rw [stepConfig_head, haction]
    rfl
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = (initialConfig machine B x).head
    · rw [if_pos hi]
      have hi0 : i.val = 0 := by
        rw [hi, initialConfig_head_val]
      simp [sentinelConfig, sentinelTape, hi0]
    · rw [if_neg hi]
      have hi0 : i.val ≠ 0 := by
        intro h
        apply hi
        apply Fin.ext
        rw [h, initialConfig_head_val]
      simp [sentinelConfig, sentinelTape, initialConfig, hi0]

/-! ## Exact final configuration on every budget -/

/-- Required exact full-configuration theorem, for every raw word (including
`N = 0`) and every budget (including `B = 0`): literal accept, head at the
origin, and the complete `[input][marker]` layout with every cell above `N`
blank. -/
theorem run_initialConfig_exact {N : Nat} (B : Nat) (x : Bitstring N) :
    machine.run (clock N) (initialConfig machine B x) = sentinelConfig B x := by
  cases N with
  | zero => exact run_empty B x
  | succ N =>
      have hN : 0 < N + 1 := Nat.succ_pos N
      have hBack := run_back (B := B) x hN N (Nat.lt_succ_self N)
      have hFinal := back_to_final x hN hBack rfl
      have htime : clock (N + 1) = (N + 1 + 1 + N) + 1 := by
        rw [clock_eq]
        omega
      rw [htime, UniformTM.run]
      exact hFinal

/-- Pointwise final tape contract: the raw input is preserved exactly
(including every literal `some false` bit), the marker is at cell `N`, and
every cell above `N` is blank. -/
theorem final_tape_behavior {N B : Nat} (x : Bitstring N) :
    let cF := machine.run (clock N) (initialConfig machine B x)
    (∀ i : Fin N,
      cF.tape
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_add_right N (B + 1))⟩ = some (x i)) ∧
    cF.tape ⟨N, by unfold tapeLength; omega⟩ = some true ∧
    (∀ j : Fin (tapeLength N B), N < j.val → cF.tape j = none) := by
  dsimp
  rw [run_initialConfig_exact]
  refine ⟨fun i => ?_, ?_, fun j hj => sentinelTape_beyond x j hj⟩
  · simp [sentinelConfig, sentinelTape]
  · simp [sentinelConfig, sentinelTape]

/-- With positive ambient budget, the cell immediately after the marker exists
and is blank. This is the additional allocation fact required by a downstream
one-cell-lookahead consumer; it is deliberately separate from the all-budget
exact execution theorem. -/
theorem blank_after_marker {N B : Nat} (x : Bitstring N) (hB : 0 < B) :
    let cF := machine.run (clock N) (initialConfig machine B x)
    cF.tape ⟨N + 1, by unfold tapeLength; omega⟩ = none := by
  dsimp
  exact (final_tape_behavior x).2.2
    (⟨N + 1, by unfold tapeLength; omega⟩ : Fin (tapeLength N B))
    (show N < N + 1 by omega)

/-! ## Private trace description through the clock -/

/-- Control at each time through the clock, read off the transition trace. -/
private def traceState {N : Nat} (x : Bitstring N) (s : Nat) :
    Fin sentinelStateCount :=
  if s = 0 then qStart
  else if s ≤ N then scanState (bitAt x 0)
  else if s ≤ 2 * N then backState (bitAt x 0)
  else qAccept

/-- Head address at each time through the clock. -/
private def traceHead (N s : Nat) : Nat :=
  if s ≤ N then s
  else if s ≤ 2 * N then 2 * N - s
  else 0

/-- Tape at each time through the clock. -/
private def traceTape {N : Nat} (B : Nat) (x : Bitstring N) (s : Nat) :
    Fin (tapeLength N B) → Option Bool :=
  if s = 0 then (initialConfig machine B x).tape
  else if s ≤ N then erasedZeroTape B x
  else if s ≤ 2 * N then erasedZeroMarkedTape B x
  else sentinelTape B x

private theorem traceHead_le (N s : Nat) : traceHead N s ≤ N := by
  unfold traceHead
  split_ifs <;> omega

private theorem run_scan_time {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs0 : 0 < s) (hsN : s ≤ N) :
    ScanAt B x s (machine.run s (initialConfig machine B x)) := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  exact run_scan x r hsN

private theorem run_back_time {N B : Nat} (x : Bitstring N)
    (s : Nat) (hsN : N < s) (hs2N : s ≤ 2 * N) :
    BackAt B x (s - (N + 1)) (machine.run s (initialConfig machine B x)) := by
  have hN : 0 < N := by omega
  have h := run_back (B := B) x hN (s - (N + 1)) (by omega)
  rwa [show N + 1 + (s - (N + 1)) = s by omega] at h

/-- Exact state, head, and tape at every time through the clock. -/
private theorem run_trace_fields {N : Nat} (B : Nat) (x : Bitstring N)
    (s : Nat) (hs : s ≤ clock N) :
    (machine.run s (initialConfig machine B x)).state = traceState x s ∧
      (machine.run s (initialConfig machine B x)).head.val = traceHead N s ∧
      (machine.run s (initialConfig machine B x)).tape = traceTape B x s := by
  rw [clock_eq] at hs
  by_cases hs0 : s = 0
  · subst hs0
    simp only [traceState, traceHead, traceTape, if_pos (Nat.zero_le N)]
    exact ⟨rfl, rfl, rfl⟩
  · by_cases hsN : s ≤ N
    · obtain ⟨h1, h2, h3⟩ := run_scan_time (B := B) x s (by omega) hsN
      simp only [traceState, traceHead, traceTape, if_neg hs0, if_pos hsN]
      exact ⟨h1, h2, h3⟩
    · by_cases hs2N : s ≤ 2 * N
      · obtain ⟨h1, h2, h3⟩ := run_back_time (B := B) x s (by omega) hs2N
        simp only [traceState, traceHead, traceTape, if_neg hs0, if_neg hsN,
          if_pos hs2N]
        refine ⟨h1, ?_, h3⟩
        rw [h2]
        omega
      · have hfinal : s = clock N := by
          rw [clock_eq]
          omega
        subst hfinal
        rw [run_initialConfig_exact]
        simp only [traceState, traceHead, traceTape, if_neg hs0, if_neg hsN,
          if_neg hs2N]
        exact ⟨rfl, rfl, rfl⟩

/-! ## Footprint and boundary safety -/

/-- The head never passes cell `N` at any time through the clock. -/
theorem head_le_input_through_clock {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : s ≤ clock N) :
    (machine.run s (initialConfig machine B x)).head.val ≤ N := by
  rw [(run_trace_fields B x s hs).2.1]
  exact traceHead_le N s

/-- Every cell above `N` is blank at every time through the clock, on every
budget.  The machine never touches the ambient suffix. -/
theorem beyond_input_blank_through_clock {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : s ≤ clock N)
    (j : Fin (tapeLength N B)) (hj : N < j.val) :
    (machine.run s (initialConfig machine B x)).tape j = none := by
  rw [(run_trace_fields B x s hs).2.2]
  unfold traceTape
  split_ifs
  · exact initialConfig_tape_padding machine x j (Nat.le_of_lt hj)
  · exact erasedZeroTape_beyond x j hj
  · exact erasedZeroMarkedTape_beyond x j hj
  · exact sentinelTape_beyond x j hj

/-- The finite control, the head address, and every common tape cell at every
time through the clock are the same on any two budgets, including the minimal
allocation `B = 0`. -/
theorem run_budget_independent {N : Nat} (B B' : Nat) (x : Bitstring N)
    (s : Nat) (hs : s ≤ clock N) :
    (machine.run s (initialConfig machine B x)).state =
      (machine.run s (initialConfig machine B' x)).state ∧
    (machine.run s (initialConfig machine B x)).head.val =
      (machine.run s (initialConfig machine B' x)).head.val ∧
    (∀ (i : Fin (tapeLength N B)) (i' : Fin (tapeLength N B')),
      i.val = i'.val →
        (machine.run s (initialConfig machine B x)).tape i =
          (machine.run s (initialConfig machine B' x)).tape i') := by
  obtain ⟨h1, h2, h3⟩ := run_trace_fields B x s hs
  obtain ⟨h1', h2', h3'⟩ := run_trace_fields B' x s hs
  refine ⟨by rw [h1, h1'], by rw [h2, h2'], fun i i' hii' => ?_⟩
  rw [h3, h3']
  unfold traceTape
  split_ifs
  · simp [initialConfig, hii']
  · simp [erasedZeroTape, initialConfig, hii']
  · simp [erasedZeroMarkedTape, sentinelTape, hii']
  · simp [sentinelTape, hii']

/-- The head move taken at each time before the clock, read off the trace:
right moves while scanning, left moves from the marker transition through the
rewind, and stay at the final transition. -/
private def traceMove (N s : Nat) : Move :=
  if s < N then .right
  else if s < 2 * N then .left
  else .stay

private theorem run_move_eq_traceMove {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : s < clock N) :
    let c := machine.run s (initialConfig machine B x)
    (machine.step c.state (c.tape c.head)).2.2 = traceMove N s := by
  dsimp
  obtain ⟨hstate, hhead, htape⟩ := run_trace_fields B x s (Nat.le_of_lt hs)
  set c := machine.run s (initialConfig machine B x) with hc
  rw [clock_eq] at hs
  by_cases hs0 : s = 0
  · subst hs0
    have hstate' : c.state = qStart := hstate
    have hhead' : c.head.val = 0 := by
      rw [hhead]
      unfold traceHead
      rw [if_pos (Nat.zero_le N)]
    have htape' : c.tape = (initialConfig machine B x).tape := htape
    have hheadEq : c.head = (initialConfig machine B x).head := by
      apply Fin.ext
      rw [hhead', initialConfig_head_val]
    rw [hstate', htape', hheadEq]
    by_cases hN : 0 < N
    · rw [initial_read_zero x hN, machine_step_start_some]
      simp [traceMove, hN]
    · have hN0 : N = 0 := by omega
      subst hN0
      have hread :
          (initialConfig machine B x).tape (initialConfig machine B x).head =
            none := by
        simp [initialConfig]
      rw [hread, machine_step_start_none]
      simp [traceMove]
  · by_cases hsN : s ≤ N
    · simp only [traceState, traceHead, traceTape, if_neg hs0, if_pos hsN]
        at hstate hhead htape
      have hfit : s < tapeLength N B := by
        unfold tapeLength
        omega
      have hheadEq : c.head = ⟨s, hfit⟩ := Fin.ext hhead
      rw [hstate, htape, hheadEq]
      by_cases hsltN : s < N
      · rw [erasedZeroTape_input x (by omega) hsltN hfit,
          machine_step_scan_some]
        simp [traceMove, hsltN]
      · have hsEq : s = N := by omega
        have hheadN : (⟨s, hfit⟩ : Fin (tapeLength N B)) =
            ⟨N, by unfold tapeLength; omega⟩ := by
          apply Fin.ext
          exact hsEq
        rw [hheadN, erasedZeroTape_boundary x _, machine_step_scan_none]
        have h2N : N < 2 * N := by omega
        simp [traceMove, hsEq, h2N]
    · have hs2N : s ≤ 2 * N := by omega
      simp only [traceState, traceHead, traceTape, if_neg hs0, if_neg hsN,
        if_pos hs2N] at hstate hhead htape
      have hfit : 2 * N - s < tapeLength N B := by
        unfold tapeLength
        omega
      have hheadEq : c.head = ⟨2 * N - s, hfit⟩ := Fin.ext hhead
      have hNs : ¬ s < N := by omega
      rw [hstate, htape, hheadEq]
      by_cases hslt : s < 2 * N
      · rw [erasedZeroMarkedTape_input x (by omega) (by omega) hfit,
          machine_step_back_some]
        simp [traceMove, hslt, hNs]
      · have hzero : (⟨2 * N - s, hfit⟩ : Fin (tapeLength N B)).val = 0 := by
          change 2 * N - s = 0
          omega
        rw [erasedZeroMarkedTape_zero x hzero, machine_step_back_none]
        simp [traceMove, hNs, hslt]

/-- No transition through the clock relies on the boundary clamp of
`moveHead`: every right move has strict room and every left move starts at a
positive address, on every budget including the minimal allocation `B = 0`.
Together with `run_budget_independent` this shows that the finite tape
boundary never influences the trace. -/
theorem no_boundary_clamp_before_clock {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : s < clock N) :
    let c := machine.run s (initialConfig machine B x)
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength N B) ∧
    (move = .left → 0 < c.head.val) := by
  dsimp
  rw [run_move_eq_traceMove x s hs,
    (run_trace_fields B x s (Nat.le_of_lt hs)).2.1]
  rw [clock_eq] at hs
  refine ⟨fun hmove => ?_, fun hmove => ?_⟩
  all_goals
    unfold traceMove at hmove
    unfold traceHead
    try unfold tapeLength
    split_ifs at hmove ⊢ <;> omega

/-! ## Strict preterminality and literal acceptance -/

/-- Before the clock the control is always one of the five work controls. -/
theorem work_state_before_clock {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : s < clock N) :
    (machine.run s (initialConfig machine B x)).state.val < 5 := by
  rw [(run_trace_fields B x s (Nat.le_of_lt hs)).1]
  rw [clock_eq] at hs
  unfold traceState
  split_ifs with hs0 hsN hs2N
  · decide
  · exact scanState_val_lt _
  · exact backState_val_lt _
  · omega

/-- Strict first-terminal theorem.  `N = 0` is included: its sole earlier time
is zero, while literal acceptance occurs at time one. -/
theorem noEarlyTerminal_initialConfig {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : s < clock N) :
    (machine.run s (initialConfig machine B x)).state ≠ machine.accept ∧
      (machine.run s (initialConfig machine B x)).state ≠ machine.reject := by
  have hwork := work_state_before_clock (B := B) x s hs
  constructor
  · intro h
    rw [h] at hwork
    exact absurd hwork (by decide)
  · intro h
    rw [h] at hwork
    exact absurd hwork (by decide)

/-- Literal acceptance at the exact clock, on every budget. -/
theorem acceptsAt_clock {N : Nat} (B : Nat) (x : Bitstring N) :
    AcceptsAt machine B (clock N) x := by
  unfold AcceptsAt
  rw [run_initialConfig_exact]
  rfl

private theorem acceptsAt_of_clock_le {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : clock N ≤ s) :
    AcceptsAt machine B s x := by
  unfold AcceptsAt
  obtain ⟨extra, rfl⟩ : ∃ extra, s = clock N + extra :=
    ⟨s - clock N, by omega⟩
  rw [machine.run_add, run_initialConfig_exact,
    machine.run_accept (sentinelConfig B x) rfl extra]
  rfl

/-- The machine never enters literal reject on any raw word, at any time. -/
theorem not_rejectsAt {N B : Nat} (x : Bitstring N) (s : Nat) :
    ¬ RejectsAt machine B s x := by
  by_cases hs : s < clock N
  · exact (noEarlyTerminal_initialConfig (B := B) x s hs).2
  · intro hr
    have ha := acceptsAt_of_clock_le (B := B) x s (Nat.le_of_not_gt hs)
    exact machine.accept_ne_reject (ha.symm.trans hr)

/-- Within-budget decision, with `clock N` itself as the witness. -/
theorem decidesWithin {N B : Nat} (x : Bitstring N) (hB : clock N ≤ B) :
    DecidesWithin machine B x true := by
  change AcceptsWithin machine B x
  exact ⟨clock N, hB, acceptsAt_clock B x⟩

/-! ## Fixed external polynomial clock -/

/-- The exponent-two pinned clock dominates the sentinel clock at every raw
length. -/
theorem clock_le_polyClock_two (N : Nat) : clock N ≤ polyClock 2 N := by
  rw [clock_eq]
  unfold polyClock
  cases N with
  | zero => decide
  | succ n =>
      rw [Nat.pow_two]
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega

theorem decidesWithin_polyClock {N : Nat} (x : Bitstring N) :
    DecidesWithin machine (polyClock 2 N) x true :=
  decidesWithin x (clock_le_polyClock_two N)

/-! ## Bundled handoff contract for the later compactor -/

/-- The all-budget phase contract: exact final configuration, strict
preterminality, footprint, and literal decision behavior.  Reusable one-cell
lookahead additionally requires `blank_after_marker`, hence positive budget. -/
theorem sentinel_phase_contract {N : Nat} (B : Nat) (x : Bitstring N) :
    let c₀ := initialConfig machine B x
    machine.run (clock N) c₀ = sentinelConfig B x ∧
    (∀ s, s < clock N → (machine.run s c₀).state.val < 5) ∧
    (∀ s, s < clock N →
      (machine.run s c₀).state ≠ machine.accept ∧
        (machine.run s c₀).state ≠ machine.reject) ∧
    (∀ s, s ≤ clock N → (machine.run s c₀).head.val ≤ N) ∧
    (∀ s, s ≤ clock N → ∀ j : Fin (tapeLength N B), N < j.val →
      (machine.run s c₀).tape j = none) ∧
    AcceptsAt machine B (clock N) x ∧
    (∀ s, ¬ RejectsAt machine B s x) ∧
    (clock N ≤ B → DecidesWithin machine B x true) := by
  dsimp
  exact ⟨run_initialConfig_exact B x,
    fun s hs => work_state_before_clock x s hs,
    fun s hs => noEarlyTerminal_initialConfig x s hs,
    fun s hs => head_le_input_through_clock x s hs,
    fun s hs j hj => beyond_input_blank_through_clock x s hs j hj,
    acceptsAt_clock B x, fun s => not_rejectsAt x s,
    fun hB => decidesWithin x hB⟩

end FixedPairConcatSentinel

end Pnp3.Complexity.Uniform.V1
