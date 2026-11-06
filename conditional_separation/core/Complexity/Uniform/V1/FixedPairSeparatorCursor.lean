import Complexity.Uniform.V1.FixedPairConcatSentinel
import Complexity.Uniform.V1.PairEncoding
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Fixed pair separator cursor

This is the next deliberately small operational phase after
`FixedPairConcatSentinel`.  It does not compact the tape.  It scans the
alternating query tag/data prefix, validates a prospective separator by
looking one cell to its right, and returns one cell left in literal accept.
Thus the complete tape is unchanged and the head itself is the live cursor at
the query/witness separator.

On an encoded pair with query length `n` the exact clock is `2*n + 2`, the
final head is cell `2*n`, and the largest visited cell is `2*n + 1`.  A valid
separator always has a nonblank successor: either the first witness bit or the
sentinel produced at raw cell `N`.  Conversely, when a malformed finite raw
word has no separator at a tag position, the scan reaches the sentinel in a
tag or data state.  With positive external padding, the sentinel lookahead at
cell `N+1` exists and the machine is in literal reject at time `N+2`.

The five-state transition table is closed.  It contains no input length,
query length, witness length, clock, decoder, evaluator, or callback.  Every
row writes the exact scanned `Option Bool`, so `none` and `some false` remain
distinct.

This module intentionally makes no claim of physical equality with `x ++ w`:
the raw tape remains tagged.  Its reusable postcondition is instead the exact
full configuration with the head at the still-present separator.
-/

namespace Pnp3.Complexity.Uniform.V1

namespace FixedPairSeparatorCursor

open PairEncoding

abbrev cursorStateCount : Nat := 5

def qTag : Fin cursorStateCount :=
  ⟨0, by decide⟩

def qData : Fin cursorStateCount :=
  ⟨1, by decide⟩

def qPeek : Fin cursorStateCount :=
  ⟨2, by decide⟩

def qAccept : Fin cursorStateCount :=
  ⟨3, by decide⟩

def qReject : Fin cursorStateCount :=
  ⟨4, by decide⟩

/-!
`qTag` is used at addresses `0,2,4,...`.  A false is a query tag.  A
true is only a candidate separator, because the terminal sentinel is also
true.  `qPeek` accepts the candidate only when its successor is nonblank.
`qData` accepts either Boolean data value and rejects a blank.
-/
private def cursorRawStep
    (q : Fin cursorStateCount)
    (scanned : Option Bool) :
    Fin cursorStateCount × Option Bool × Move :=
  match q.val with
  | 0 =>
      match scanned with
      | none => (qReject, none, .stay)
      | some false => (qData, some false, .right)
      | some true => (qPeek, some true, .right)
  | 1 =>
      match scanned with
      | none => (qReject, none, .stay)
      | some b => (qTag, some b, .right)
  | 2 =>
      match scanned with
      | none => (qReject, none, .stay)
      | some b => (qAccept, some b, .left)
  | 3 => (qAccept, scanned, .stay)
  | _ => (qReject, scanned, .stay)

/-- The closed five-state separator-cursor machine. -/
def machine : UniformTM where
  stateCount := cursorStateCount
  start := qTag
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := cursorRawStep

/-- Exhaustive pin for all five rows of the installed raw table. -/
theorem cursorRawStep_table :
    (∀ scanned,
      machine.rawStep qTag scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some false => (qData, some false, .right)
        | some true => (qPeek, some true, .right)) ∧
    (∀ scanned,
      machine.rawStep qData scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some b => (qTag, some b, .right)) ∧
    (∀ scanned,
      machine.rawStep qPeek scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some b => (qAccept, some b, .left)) ∧
    (∀ scanned,
      machine.rawStep qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned,
      machine.rawStep qReject scanned = (qReject, scanned, .stay)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro scanned
    cases scanned with
    | none => rfl
    | some b => cases b <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    rfl
  · intro scanned
    rfl

/-- Exact finite-control and transition-table resource pins. -/
theorem machine_resource_pins :
    machine.stateCount = 5 ∧
    machine.start = qTag ∧
    machine.accept = qAccept ∧
    machine.reject = qReject ∧
    qTag.val = 0 ∧
    qData.val = 1 ∧
    qPeek.val = 2 ∧
    qAccept.val = 3 ∧
    qReject.val = 4 ∧
    Fintype.card (Fin machine.stateCount) = 5 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 15 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · change Fintype.card (Fin 5 × Option Bool) = 15
    decide

/-! ## Exact sentinel handoff -/

/-- The downstream start configuration is obtained only by changing the
finite control at the sentinel phase boundary.  Head and complete tape are
the producer's exact handoff fields. -/
def startConfig {N : Nat} (B : Nat) (raw : Bitstring N) :
    Config cursorStateCount N B where
  state := qTag
  head := ⟨0, by simp [tapeLength]⟩
  tape := FixedPairConcatSentinel.sentinelTape B raw

/-- Exact field-level handoff from the proved sentinel run.  No destination
address is supplied: the producer ends at zero and the cursor machine must
discover the separator from tape symbols. -/
theorem startConfig_of_sentinel_run {N B : Nat} (raw : Bitstring N) :
    (startConfig B raw).state = qTag ∧
    (startConfig B raw).head =
      (FixedPairConcatSentinel.machine.run
        (FixedPairConcatSentinel.clock N)
        (initialConfig FixedPairConcatSentinel.machine B raw)).head ∧
    (startConfig B raw).tape =
      (FixedPairConcatSentinel.machine.run
        (FixedPairConcatSentinel.clock N)
        (initialConfig FixedPairConcatSentinel.machine B raw)).tape := by
  rw [FixedPairConcatSentinel.run_initialConfig_exact]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Valid-pair clock and exact configurations -/

/-- Two transitions per query tag/data pair, then candidate lookahead and
the accepting left move. -/
def clock (n : Nat) : Nat :=
  2 * n + 2

/-- Exact successful postconfiguration.  The complete sentinel tape is
unchanged and the head is the still-present separator at cell `2*n`. -/
def finalConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config cursorStateCount (pairLength n m) B where
  state := qAccept
  head := ⟨2 * n, by unfold tapeLength pairLength; omega⟩
  tape := FixedPairConcatSentinel.sentinelTape B (encodePair x w)

/-- Exact valid trace configuration at tag position `i`. -/
private def scanConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i ≤ n) :
    Config cursorStateCount (pairLength n m) B where
  state := qTag
  head := ⟨2 * i, by unfold tapeLength pairLength; omega⟩
  tape := FixedPairConcatSentinel.sentinelTape B (encodePair x w)

/-- Exact valid trace configuration at query-data position `i`. -/
private def dataConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    Config cursorStateCount (pairLength n m) B where
  state := qData
  head := ⟨2 * i + 1, by unfold tapeLength pairLength; omega⟩
  tape := FixedPairConcatSentinel.sentinelTape B (encodePair x w)

/-- Exact valid preterminal configuration one cell right of the separator. -/
private def peekConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config cursorStateCount (pairLength n m) B where
  state := qPeek
  head := ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩
  tape := FixedPairConcatSentinel.sentinelTape B (encodePair x w)

/-! ## Small execution bridges -/

private theorem config_ext
    {N B : Nat} {c d : Config cursorStateCount N B}
    (hstate : c.state = d.state)
    (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
      cases d with
      | mk ds dh dt =>
          change cs = ds at hstate
          change ch = dh at hhead
          change ct = dt at htape
          subst ds
          subst dh
          subst dt
          rfl

private theorem stepConfig_state
    {N B : Nat} (c : Config cursorStateCount N B) :
    (machine.stepConfig c).state =
      (machine.step c.state (c.tape c.head)).1 :=
  rfl

private theorem stepConfig_head
    {N B : Nat} (c : Config cursorStateCount N B) :
    (machine.stepConfig c).head =
      moveHead c.head (machine.step c.state (c.tape c.head)).2.2 :=
  rfl

private theorem stepConfig_tape
    {N B : Nat} (c : Config cursorStateCount N B)
    (i : Fin (tapeLength N B)) :
    (machine.stepConfig c).tape i =
      if i = c.head
      then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i :=
  rfl

private theorem step_preserving
    {N B : Nat} (c : Config cursorStateCount N B)
    (q : Fin cursorStateCount) (move : Move)
    (haction : machine.step c.state (c.tape c.head) =
      (q, c.tape c.head, move)) :
    machine.stepConfig c =
      ({ state := q
         head := moveHead c.head move
         tape := c.tape } : Config cursorStateCount N B) := by
  apply config_ext
  · rw [stepConfig_state, haction]
  · rw [stepConfig_head, haction]
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c.head
    · subst i
      simp
    · simp [hi]

private theorem step_tag_false :
    machine.step qTag (some false) =
      (qData, some false, .right) := by
  rfl

private theorem step_tag_true :
    machine.step qTag (some true) =
      (qPeek, some true, .right) := by
  rfl

private theorem step_tag_none :
    machine.step qTag none = (qReject, none, .stay) := by
  rfl

private theorem step_data_some (b : Bool) :
    machine.step qData (some b) = (qTag, some b, .right) := by
  cases b <;> rfl

private theorem step_peek_some (b : Bool) :
    machine.step qPeek (some b) = (qAccept, some b, .left) := by
  cases b <;> rfl

private theorem step_peek_none :
    machine.step qPeek none = (qReject, none, .stay) := by
  rfl

private theorem scan_read_tag {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    (scanConfig B x w i (Nat.le_of_lt hi)).tape
      (scanConfig B x w i (Nat.le_of_lt hi)).head = some false := by
  change FixedPairConcatSentinel.sentinelTape B (encodePair x w)
      ⟨2 * i, by unfold tapeLength pairLength; omega⟩ = some false
  have hinput : 2 * i < pairLength n m := by
    unfold pairLength
    omega
  simp [FixedPairConcatSentinel.sentinelTape, hinput,
    encodePair_tag x w ⟨i, hi⟩]

private theorem data_read {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    (dataConfig B x w i hi).tape
      (dataConfig B x w i hi).head = some (x ⟨i, hi⟩) := by
  change FixedPairConcatSentinel.sentinelTape B (encodePair x w)
      ⟨2 * i + 1, by unfold tapeLength pairLength; omega⟩ =
        some (x ⟨i, hi⟩)
  have hinput : 2 * i + 1 < pairLength n m := by
    unfold pairLength
    omega
  simp [FixedPairConcatSentinel.sentinelTape, hinput,
    encodePair_data x w ⟨i, hi⟩]

private theorem scan_to_data {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    machine.stepConfig (scanConfig B x w i (Nat.le_of_lt hi)) =
      dataConfig B x w i hi := by
  let c := scanConfig B x w i (Nat.le_of_lt hi)
  have hread : c.tape c.head = some false := scan_read_tag x w i hi
  have haction : machine.step c.state (c.tape c.head) =
      (qData, c.tape c.head, .right) := by
    rw [hread]
    exact step_tag_false
  rw [step_preserving c qData .right haction]
  apply config_ext
  · rfl
  · apply Fin.ext
    have hroom : 2 * i + 1 < tapeLength (pairLength n m) B := by
      unfold tapeLength pairLength
      omega
    simp [c, scanConfig, dataConfig, moveHead, hroom]
  · rfl

private theorem data_to_scan {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    machine.stepConfig (dataConfig B x w i hi) =
      scanConfig B x w (i + 1) (by omega) := by
  let c := dataConfig B x w i hi
  have hread : c.tape c.head = some (x ⟨i, hi⟩) := data_read x w i hi
  have haction : machine.step c.state (c.tape c.head) =
      (qTag, c.tape c.head, .right) := by
    rw [hread]
    exact step_data_some _
  rw [step_preserving c qTag .right haction]
  apply config_ext
  · rfl
  · apply Fin.ext
    have hroom : 2 * i + 2 < tapeLength (pairLength n m) B := by
      unfold tapeLength pairLength
      omega
    simp [c, dataConfig, scanConfig, moveHead, hroom]
    omega
  · rfl

private theorem scan_pair {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    machine.run 2 (scanConfig B x w i (Nat.le_of_lt hi)) =
      scanConfig B x w (i + 1) (by omega) := by
  calc
    machine.run 2 (scanConfig B x w i (Nat.le_of_lt hi)) =
        machine.stepConfig
          (machine.stepConfig
            (scanConfig B x w i (Nat.le_of_lt hi))) := rfl
    _ = machine.stepConfig (dataConfig B x w i hi) := by
      rw [scan_to_data]
    _ = scanConfig B x w (i + 1) (by omega) :=
      data_to_scan x w i hi

private theorem start_eq_scan_zero {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    startConfig B (encodePair x w) = scanConfig B x w 0 (Nat.zero_le n) := by
  apply config_ext
  · rfl
  · apply Fin.ext
    rfl
  · rfl

private theorem run_scan {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i ≤ n) :
    machine.run (2 * i) (startConfig B (encodePair x w)) =
      scanConfig B x w i hi := by
  induction i with
  | zero =>
      simpa [UniformTM.run] using start_eq_scan_zero (B := B) x w
  | succ i ih =>
      have hiprev : i ≤ n := by omega
      have hilt : i < n := by omega
      calc
        machine.run (2 * (i + 1)) (startConfig B (encodePair x w)) =
            machine.run 2
              (machine.run (2 * i) (startConfig B (encodePair x w))) := by
          rw [show 2 * (i + 1) = 2 * i + 2 by omega,
            machine.run_add]
        _ = machine.run 2 (scanConfig B x w i hiprev) := by
          rw [ih hiprev]
        _ = scanConfig B x w (i + 1) (by omega) :=
          scan_pair x w i hilt

private theorem scan_read_separator {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (scanConfig B x w n (Nat.le_refl n)).tape
      (scanConfig B x w n (Nat.le_refl n)).head = some true := by
  change FixedPairConcatSentinel.sentinelTape B (encodePair x w)
      ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = some true
  have hinput : 2 * n < pairLength n m := by
    unfold pairLength
    omega
  simp [FixedPairConcatSentinel.sentinelTape, hinput,
    encodePair_separator]

private theorem scan_to_peek {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (scanConfig B x w n (Nat.le_refl n)) =
      peekConfig B x w := by
  let c := scanConfig B x w n (Nat.le_refl n)
  have hread : c.tape c.head = some true := scan_read_separator x w
  have haction : machine.step c.state (c.tape c.head) =
      (qPeek, c.tape c.head, .right) := by
    rw [hread]
    exact step_tag_true
  rw [step_preserving c qPeek .right haction]
  apply config_ext
  · rfl
  · apply Fin.ext
    have hroom : 2 * n + 1 < tapeLength (pairLength n m) B := by
      unfold tapeLength pairLength
      omega
    simp [c, scanConfig, peekConfig, moveHead, hroom]
  · rfl

private theorem peek_read_some {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    ∃ b, (peekConfig B x w).tape (peekConfig B x w).head = some b := by
  cases m with
  | zero =>
      refine ⟨true, ?_⟩
      change FixedPairConcatSentinel.sentinelTape B (encodePair x w)
          ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ = some true
      simp [FixedPairConcatSentinel.sentinelTape, pairLength]
  | succ m =>
      refine ⟨w ⟨0, Nat.succ_pos m⟩, ?_⟩
      change FixedPairConcatSentinel.sentinelTape B (encodePair x w)
          ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ =
            some (w ⟨0, Nat.succ_pos m⟩)
      have hinput : 2 * n + 1 < pairLength n (m + 1) := by
        unfold pairLength
        omega
      have hw :
          encodePair x w ⟨2 * n + 1, hinput⟩ =
            w ⟨0, Nat.succ_pos m⟩ := by
        convert
          (encodePair_witness x w ⟨0, Nat.succ_pos m⟩) using 1
      unfold FixedPairConcatSentinel.sentinelTape
      rw [dif_pos hinput, hw]

private theorem peek_to_final {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (peekConfig B x w) = finalConfig B x w := by
  obtain ⟨b, hread⟩ := peek_read_some (B := B) x w
  let c := peekConfig B x w
  have haction : machine.step c.state (c.tape c.head) =
      (qAccept, c.tape c.head, .left) := by
    rw [hread]
    exact step_peek_some b
  rw [step_preserving c qAccept .left haction]
  apply config_ext
  · rfl
  · apply Fin.ext
    simp [c, peekConfig, finalConfig, moveHead]
  · rfl

/-! ## Exact valid trace and full final configuration -/

/-- Exact full configuration at every data-position landmark. -/
private theorem run_at_data_exact {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    machine.run (2 * i + 1) (startConfig B (encodePair x w)) =
      dataConfig B x w i hi := by
  rw [show 2 * i + 1 = 2 * i + 1 by rfl, machine.run_add,
    run_scan x w i (Nat.le_of_lt hi)]
  simpa [UniformTM.run] using scan_to_data (B := B) x w i hi

private theorem run_preterminal_config_exact {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    machine.run (2 * n + 1) (startConfig B (encodePair x w)) =
      peekConfig B x w := by
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, machine.run_add,
    run_scan x w n (Nat.le_refl n)]
  simpa [UniformTM.run] using scan_to_peek (B := B) x w

/-- Exact literal preterminal fields, with no private layout in the public
statement. -/
theorem run_preterminal_exact {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (2 * n + 1) (startConfig B (encodePair x w))).state = qPeek ∧
    (machine.run (2 * n + 1) (startConfig B (encodePair x w))).head.val =
      2 * n + 1 ∧
    (machine.run (2 * n + 1) (startConfig B (encodePair x w))).tape =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) := by
  rw [run_preterminal_config_exact]
  exact ⟨rfl, rfl, rfl⟩

/-- Required exact full-configuration theorem for the live cursor phase.
It holds for every external allocation, including `B=0`. -/
theorem run_encoded_exact {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n) (startConfig B (encodePair x w)) =
      finalConfig B x w := by
  unfold clock
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, machine.run_add,
    run_preterminal_config_exact]
  simpa [UniformTM.run] using peek_to_final (B := B) x w

/-- Pointwise form of the final tape theorem.  Query tags, data, separator,
witness, sentinel, and every blank suffix cell are all literally unchanged. -/
theorem final_tape_unchanged {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (clock n) (startConfig B (encodePair x w))).tape =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) := by
  rw [run_encoded_exact]
  rfl

/-- Literal valid verdict and exact cursor address. -/
theorem final_literal_fields {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (clock n) (startConfig B (encodePair x w))).state = qAccept ∧
    (machine.run (clock n) (startConfig B (encodePair x w))).head.val = 2 * n := by
  rw [run_encoded_exact]
  exact ⟨rfl, rfl⟩

/-! ## Trace coverage, footprint, and budget independence -/

private theorem even_or_odd (s : Nat) :
    (∃ i, s = 2 * i) ∨ (∃ i, s = 2 * i + 1) := by
  induction s with
  | zero => exact Or.inl ⟨0, by omega⟩
  | succ s ih =>
      rcases ih with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact Or.inr ⟨i, by omega⟩
      · exact Or.inl ⟨i + 1, by omega⟩

/-- Every time through the valid clock is one of the exact configurations
above; in particular the tape is unchanged and the head address is given
exactly by the phase of the structural trace. -/
private theorem valid_trace_fields {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (machine.run s (startConfig B (encodePair x w))).tape =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
    (if s ≤ 2 * n then
        (machine.run s (startConfig B (encodePair x w))).head.val = s ∧
        ((∃ i, s = 2 * i) →
          (machine.run s (startConfig B (encodePair x w))).state = qTag) ∧
        ((∃ i, s = 2 * i + 1) →
          (machine.run s (startConfig B (encodePair x w))).state = qData)
      else if s = 2 * n + 1 then
        (machine.run s (startConfig B (encodePair x w))).head.val = 2 * n + 1 ∧
        (machine.run s (startConfig B (encodePair x w))).state = qPeek
      else
        (machine.run s (startConfig B (encodePair x w))).head.val = 2 * n ∧
        (machine.run s (startConfig B (encodePair x w))).state = qAccept) := by
  unfold clock at hs
  by_cases hscan : s ≤ 2 * n
  · rw [if_pos hscan]
    rcases even_or_odd s with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hin : i ≤ n := by omega
      rw [hi, run_scan x w i hin]
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro _
        rfl
      · rintro ⟨j, hj⟩
        omega
    · have hin : i < n := by omega
      rw [hi, run_at_data_exact x w i hin]
      refine ⟨rfl, rfl, ?_, ?_⟩
      · rintro ⟨j, hj⟩
        omega
      · intro _
        rfl
  · rw [if_neg hscan]
    by_cases hpeek : s = 2 * n + 1
    · rw [if_pos hpeek, hpeek, run_preterminal_config_exact]
      exact ⟨rfl, rfl, rfl⟩
    · have hfinal : s = 2 * n + 2 := by omega
      rw [if_neg hpeek, hfinal]
      change
        (machine.run (clock n) (startConfig B (encodePair x w))).tape =
            FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
          (machine.run (clock n)
              (startConfig B (encodePair x w))).head.val = 2 * n ∧
          (machine.run (clock n)
              (startConfig B (encodePair x w))).state = qAccept
      rw [run_encoded_exact]
      exact ⟨rfl, rfl, rfl⟩

/-- Sharp valid footprint upper bound. -/
theorem head_le_separator_successor_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (machine.run s (startConfig B (encodePair x w))).head.val ≤ 2 * n + 1 := by
  by_cases hscan : s ≤ 2 * n
  · rcases even_or_odd s with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hin : i ≤ n := by omega
      rw [hi, run_scan x w i hin]
      change 2 * i ≤ 2 * n + 1
      omega
    · have hin : i < n := by omega
      rw [hi, run_at_data_exact x w i hin]
      change 2 * i + 1 ≤ 2 * n + 1
      omega
  · unfold clock at hs
    by_cases hpeek : s = 2 * n + 1
    · subst s
      rw [run_preterminal_config_exact]
      change 2 * n + 1 ≤ 2 * n + 1
      omega
    · have hfinal : s = 2 * n + 2 := by omega
      subst s
      change
        (machine.run (clock n)
          (startConfig B (encodePair x w))).head.val ≤ 2 * n + 1
      rw [run_encoded_exact]
      change 2 * n ≤ 2 * n + 1
      omega

/-- The sharp upper footprint address is actually attained at the unique
preterminal time. -/
theorem reaches_separator_successor {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (2 * n + 1)
      (startConfig B (encodePair x w))).head.val = 2 * n + 1 := by
  rw [run_preterminal_config_exact]
  rfl

/-- Valid execution is independent of padding: state and natural head agree,
and every pair of common addresses has the same exact tape symbol. -/
theorem run_budget_independent {n m : Nat}
    (B B' : Nat) (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (machine.run s (startConfig B (encodePair x w))).state =
      (machine.run s (startConfig B' (encodePair x w))).state ∧
    (machine.run s (startConfig B (encodePair x w))).head.val =
      (machine.run s (startConfig B' (encodePair x w))).head.val ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B (encodePair x w))).tape i =
        (machine.run s (startConfig B' (encodePair x w))).tape i') := by
  have hB := valid_trace_fields (B := B) x w s hs
  have hB' := valid_trace_fields (B := B') x w s hs
  refine ⟨?_, ?_, ?_⟩
  · by_cases hscan : s ≤ 2 * n
    · rcases even_or_odd s with ⟨i, hi⟩ | ⟨i, hi⟩
      · have hin : i ≤ n := by omega
        rw [hi, run_scan x w i hin, run_scan x w i hin]
        change qTag = qTag
        rfl
      · have hin : i < n := by omega
        rw [hi, run_at_data_exact x w i hin,
          run_at_data_exact x w i hin]
        change qData = qData
        rfl
    · by_cases hpeek : s = 2 * n + 1
      · subst s
        rw [run_preterminal_config_exact, run_preterminal_config_exact]
        change qPeek = qPeek
        rfl
      · have hfinal : s = clock n := by
          unfold clock
          unfold clock at hs
          omega
        subst s
        rw [run_encoded_exact, run_encoded_exact]
        change qAccept = qAccept
        rfl
  · by_cases hscan : s ≤ 2 * n
    · rcases even_or_odd s with ⟨i, hi⟩ | ⟨i, hi⟩
      · have hin : i ≤ n := by omega
        rw [hi, run_scan x w i hin, run_scan x w i hin]
        change 2 * i = 2 * i
        rfl
      · have hin : i < n := by omega
        rw [hi, run_at_data_exact x w i hin,
          run_at_data_exact x w i hin]
        change 2 * i + 1 = 2 * i + 1
        rfl
    · by_cases hpeek : s = 2 * n + 1
      · subst s
        rw [run_preterminal_config_exact, run_preterminal_config_exact]
        change 2 * n + 1 = 2 * n + 1
        rfl
      · have hfinal : s = clock n := by
          unfold clock
          unfold clock at hs
          omega
        subst s
        rw [run_encoded_exact, run_encoded_exact]
        change 2 * n = 2 * n
        rfl
  · intro i i' hii'
    rw [hB.1, hB'.1]
    simp [FixedPairConcatSentinel.sentinelTape, hii']

/-- No valid transition through the exact clock can use either clamp. -/
theorem no_boundary_clamp_before_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n) :
    let c := machine.run s (startConfig B (encodePair x w))
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (move = .left → 0 < c.head.val) := by
  dsimp
  unfold clock at hs
  by_cases hscan : s ≤ 2 * n
  · rcases even_or_odd s with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hin : i ≤ n := by omega
      by_cases hlt : i < n
      · subst s
        rw [run_scan x w i hin]
        rw [scan_read_tag x w i hlt]
        change
          ((machine.step qTag (some false)).2.2 = .right →
              2 * i + 1 < tapeLength (pairLength n m) B) ∧
            ((machine.step qTag (some false)).2.2 = .left → 0 < 2 * i)
        rw [step_tag_false]
        unfold tapeLength pairLength
        exact ⟨by omega, by simp⟩
      · have hieq : i = n := by omega
        subst i
        subst s
        rw [run_scan x w n (Nat.le_refl n), scan_read_separator]
        change
          ((machine.step qTag (some true)).2.2 = .right →
              2 * n + 1 < tapeLength (pairLength n m) B) ∧
            ((machine.step qTag (some true)).2.2 = .left → 0 < 2 * n)
        rw [step_tag_true]
        unfold tapeLength pairLength
        exact ⟨by omega, by simp⟩
    · have hin : i < n := by omega
      subst s
      rw [run_at_data_exact x w i hin, data_read x w i hin]
      change
        ((machine.step qData (some (x ⟨i, hin⟩))).2.2 = .right →
            2 * i + 2 < tapeLength (pairLength n m) B) ∧
          ((machine.step qData (some (x ⟨i, hin⟩))).2.2 = .left →
            0 < 2 * i + 1)
      rw [step_data_some]
      unfold tapeLength pairLength
      exact ⟨by omega, by simp⟩
  · have hpeek : s = 2 * n + 1 := by omega
    subst s
    rw [run_preterminal_config_exact]
    obtain ⟨b, hread⟩ := peek_read_some (B := B) x w
    rw [hread]
    change
      ((machine.step qPeek (some b)).2.2 = .right →
          2 * n + 2 < tapeLength (pairLength n m) B) ∧
        ((machine.step qPeek (some b)).2.2 = .left → 0 < 2 * n + 1)
    rw [step_peek_some]
    exact ⟨by simp, by omega⟩

/-! ## Strict valid terminal behavior -/

theorem noEarlyTerminal {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n) :
    (machine.run s (startConfig B (encodePair x w))).state ≠ qAccept ∧
    (machine.run s (startConfig B (encodePair x w))).state ≠ qReject := by
  unfold clock at hs
  by_cases hscan : s ≤ 2 * n
  · rcases even_or_odd s with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hin : i ≤ n := by omega
      rw [hi, run_scan x w i hin]
      change qTag ≠ qAccept ∧ qTag ≠ qReject
      decide
    · have hin : i < n := by omega
      rw [hi, run_at_data_exact x w i hin]
      change qData ≠ qAccept ∧ qData ≠ qReject
      decide
  · have hpeek : s = 2 * n + 1 := by omega
    subst s
    rw [run_preterminal_config_exact]
    change qPeek ≠ qAccept ∧ qPeek ≠ qReject
    decide

theorem run_after_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (extra : Nat) :
    machine.run (clock n + extra) (startConfig B (encodePair x w)) =
      finalConfig B x w := by
  rw [machine.run_add, run_encoded_exact,
    machine.run_accept (finalConfig B x w) rfl extra]

/-! ## Malformed canonical raw words -/

private theorem decode_none_even_false (raw : List Bool)
    (hdecode : decodePairList raw = none)
    (i : Nat) (hi : 2 * i < raw.length) :
    raw.get ⟨2 * i, hi⟩ = false := by
  induction i generalizing raw with
  | zero =>
      cases raw with
      | nil => simp at hi
      | cons b rest =>
          cases b with
          | false => rfl
          | true => simp [decodePairList] at hdecode
  | succ i ih =>
      cases raw with
      | nil => simp at hi
      | cons first rest =>
          cases first with
          | true => simp [decodePairList] at hdecode
          | false =>
              cases rest with
              | nil =>
                  simp at hi
                  omega
              | cons b tail =>
                  have htail : decodePairList tail = none := by
                    cases hd : decodePairList tail with
                    | none => rfl
                    | some p =>
                        rcases p with ⟨xs, ws⟩
                        simp [decodePairList, hd] at hdecode
                  have hlt : 2 * i < tail.length := by
                    simp at hi
                    omega
                  simpa [List.get_cons_succ, Nat.mul_add] using
                    ih tail htail hlt

private theorem decodePair_none_even_false {N : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (i : Nat) (hi : 2 * i < N) :
    raw ⟨2 * i, hi⟩ = false := by
  have hlist : decodePairList (List.ofFn raw) = none := by
    cases hd : decodePairList (List.ofFn raw) with
    | none => rfl
    | some p =>
        rcases p with ⟨xs, ws⟩
        simp [decodePair, hd] at hdecode
  have h := decode_none_even_false (List.ofFn raw) hlist i (by simpa using hi)
  simpa [List.get_ofFn] using h

private def rawScanConfig {N : Nat} (B : Nat) (raw : Bitstring N)
    (i : Nat) (hi : 2 * i ≤ N) : Config cursorStateCount N B where
  state := qTag
  head := ⟨2 * i, by unfold tapeLength; omega⟩
  tape := FixedPairConcatSentinel.sentinelTape B raw

private theorem raw_start_eq_scan_zero {N B : Nat} (raw : Bitstring N) :
    startConfig B raw = rawScanConfig B raw 0 (Nat.zero_le N) := by
  apply config_ext <;> rfl

private theorem raw_scan_pair {N B : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (i : Nat) (hi : 2 * i + 1 < N) :
    machine.run 2 (rawScanConfig B raw i (by omega)) =
      rawScanConfig B raw (i + 1) (by omega) := by
  let c₀ := rawScanConfig B raw i (by omega)
  have heven : raw ⟨2 * i, by omega⟩ = false :=
    decodePair_none_even_false raw hdecode i (by omega)
  have hread₀ : c₀.tape c₀.head = some false := by
    change FixedPairConcatSentinel.sentinelTape B raw
      ⟨2 * i, by unfold tapeLength; omega⟩ = some false
    have hinput : 2 * i < N := by omega
    simp [FixedPairConcatSentinel.sentinelTape, hinput, heven]
  have haction₀ : machine.step c₀.state (c₀.tape c₀.head) =
      (qData, c₀.tape c₀.head, .right) := by
    rw [hread₀]
    exact step_tag_false
  let c₁ : Config cursorStateCount N B :=
    { state := qData
      head := ⟨2 * i + 1, by unfold tapeLength; omega⟩
      tape := FixedPairConcatSentinel.sentinelTape B raw }
  have hstep₀ : machine.stepConfig c₀ = c₁ := by
    rw [step_preserving c₀ qData .right haction₀]
    apply config_ext
    · rfl
    · apply Fin.ext
      have hroom : 2 * i + 1 < tapeLength N B := by
        unfold tapeLength
        omega
      simp [c₀, c₁, rawScanConfig, moveHead, hroom]
    · rfl
  have hread₁ : c₁.tape c₁.head = some (raw ⟨2 * i + 1, by omega⟩) := by
    change FixedPairConcatSentinel.sentinelTape B raw
      ⟨2 * i + 1, by unfold tapeLength; omega⟩ =
        some (raw ⟨2 * i + 1, by omega⟩)
    simp [FixedPairConcatSentinel.sentinelTape, hi]
  have haction₁ : machine.step c₁.state (c₁.tape c₁.head) =
      (qTag, c₁.tape c₁.head, .right) := by
    rw [hread₁]
    exact step_data_some _
  have hstep₁ : machine.stepConfig c₁ =
      rawScanConfig B raw (i + 1) (by omega) := by
    rw [step_preserving c₁ qTag .right haction₁]
    apply config_ext
    · rfl
    · apply Fin.ext
      have hroom : 2 * i + 2 < tapeLength N B := by
        unfold tapeLength
        omega
      simp [c₁, rawScanConfig, moveHead, hroom]
      omega
    · rfl
  calc
    machine.run 2 c₀ = machine.stepConfig (machine.stepConfig c₀) := rfl
    _ = machine.stepConfig c₁ := by rw [hstep₀]
    _ = rawScanConfig B raw (i + 1) (by omega) := hstep₁

private theorem run_raw_scan {N B : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (i : Nat) (hi : 2 * i ≤ N) :
    machine.run (2 * i) (startConfig B raw) = rawScanConfig B raw i hi := by
  induction i with
  | zero =>
      simpa [UniformTM.run] using raw_start_eq_scan_zero (B := B) raw
  | succ i ih =>
      have hiprev : 2 * i ≤ N := by omega
      have hpair : 2 * i + 1 < N := by omega
      calc
        machine.run (2 * (i + 1)) (startConfig B raw) =
            machine.run 2 (machine.run (2 * i) (startConfig B raw)) := by
          rw [show 2 * (i + 1) = 2 * i + 2 by omega,
            machine.run_add]
        _ = machine.run 2 (rawScanConfig B raw i hiprev) := by
          rw [ih hiprev]
        _ = rawScanConfig B raw (i + 1) (by omega) :=
          raw_scan_pair raw hdecode i hpair

/-- Exact malformed canonical-layout result. -/
private def rejectConfig {N : Nat} (B : Nat) (raw : Bitstring N)
    (hB : 0 < B) : Config cursorStateCount N B where
  state := qReject
  head := ⟨N + 1, by unfold tapeLength; omega⟩
  tape := FixedPairConcatSentinel.sentinelTape B raw

private theorem malformed_even_reject {N B : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (hB : 0 < B) (i : Nat) (hN : N = 2 * i) :
    machine.run (N + 2) (startConfig B raw) = rejectConfig B raw hB := by
  subst N
  have hscan := run_raw_scan (B := B) raw hdecode i (Nat.le_refl _)
  let c₀ := rawScanConfig B raw i (Nat.le_refl _)
  have hmarker : c₀.tape c₀.head = some true := by
    change FixedPairConcatSentinel.sentinelTape B raw
      ⟨2 * i, by unfold tapeLength; omega⟩ = some true
    simp [FixedPairConcatSentinel.sentinelTape]
  have haction₀ : machine.step c₀.state (c₀.tape c₀.head) =
      (qPeek, c₀.tape c₀.head, .right) := by
    rw [hmarker]
    exact step_tag_true
  let c₁ : Config cursorStateCount (2 * i) B :=
    { state := qPeek
      head := ⟨2 * i + 1, by unfold tapeLength; omega⟩
      tape := FixedPairConcatSentinel.sentinelTape B raw }
  have hstep₀ : machine.stepConfig c₀ = c₁ := by
    rw [step_preserving c₀ qPeek .right haction₀]
    apply config_ext
    · rfl
    · apply Fin.ext
      have hroom : 2 * i + 1 < tapeLength (2 * i) B := by
        unfold tapeLength
        omega
      simp [c₀, c₁, rawScanConfig, moveHead, hroom]
    · rfl
  have hblank : c₁.tape c₁.head = none := by
    change FixedPairConcatSentinel.sentinelTape B raw
      ⟨2 * i + 1, by unfold tapeLength; omega⟩ = none
    have hnot : ¬ 2 * i + 1 < 2 * i := by omega
    simp [FixedPairConcatSentinel.sentinelTape, hnot]
  have haction₁ : machine.step c₁.state (c₁.tape c₁.head) =
      (qReject, c₁.tape c₁.head, .stay) := by
    rw [hblank]
    exact step_peek_none
  have hstep₁ : machine.stepConfig c₁ = rejectConfig B raw hB := by
    rw [step_preserving c₁ qReject .stay haction₁]
    apply config_ext
    · rfl
    · apply Fin.ext
      rfl
    · rfl
  calc
    machine.run (2 * i + 2) (startConfig B raw) =
        machine.run 2 (machine.run (2 * i) (startConfig B raw)) := by
      rw [← machine.run_add]
    _ = machine.run 2 c₀ := by rw [hscan]
    _ = machine.stepConfig (machine.stepConfig c₀) := rfl
    _ = machine.stepConfig c₁ := by rw [hstep₀]
    _ = rejectConfig B raw hB := hstep₁

private theorem malformed_odd_reject {N B : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (hB : 0 < B) (i : Nat) (hN : N = 2 * i + 1) :
    machine.run (N + 2) (startConfig B raw) = rejectConfig B raw hB := by
  subst N
  have hscan := run_raw_scan (B := B) raw hdecode i (by omega)
  let c₀ := rawScanConfig B raw i (by omega)
  have heven : raw ⟨2 * i, by omega⟩ = false :=
    decodePair_none_even_false raw hdecode i (by omega)
  have hread₀ : c₀.tape c₀.head = some false := by
    change FixedPairConcatSentinel.sentinelTape B raw
      ⟨2 * i, by unfold tapeLength; omega⟩ = some false
    have hinput : 2 * i < 2 * i + 1 := by omega
    simp [FixedPairConcatSentinel.sentinelTape, hinput, heven]
  have haction₀ : machine.step c₀.state (c₀.tape c₀.head) =
      (qData, c₀.tape c₀.head, .right) := by
    rw [hread₀]
    exact step_tag_false
  let c₁ : Config cursorStateCount (2 * i + 1) B :=
    { state := qData
      head := ⟨2 * i + 1, by unfold tapeLength; omega⟩
      tape := FixedPairConcatSentinel.sentinelTape B raw }
  have hstep₀ : machine.stepConfig c₀ = c₁ := by
    rw [step_preserving c₀ qData .right haction₀]
    apply config_ext
    · rfl
    · apply Fin.ext
      have hroom : 2 * i + 1 < tapeLength (2 * i + 1) B := by
        unfold tapeLength
        omega
      simp [c₀, c₁, rawScanConfig, moveHead, hroom]
    · rfl
  have hmarker : c₁.tape c₁.head = some true := by
    change FixedPairConcatSentinel.sentinelTape B raw
      ⟨2 * i + 1, by unfold tapeLength; omega⟩ = some true
    simp [FixedPairConcatSentinel.sentinelTape]
  have haction₁ : machine.step c₁.state (c₁.tape c₁.head) =
      (qTag, c₁.tape c₁.head, .right) := by
    rw [hmarker]
    exact step_data_some true
  let c₂ : Config cursorStateCount (2 * i + 1) B :=
    { state := qTag
      head := ⟨2 * i + 2, by unfold tapeLength; omega⟩
      tape := FixedPairConcatSentinel.sentinelTape B raw }
  have hstep₁ : machine.stepConfig c₁ = c₂ := by
    rw [step_preserving c₁ qTag .right haction₁]
    apply config_ext
    · rfl
    · apply Fin.ext
      have hroom : 2 * i + 2 < tapeLength (2 * i + 1) B := by
        unfold tapeLength
        omega
      simp [c₁, c₂, moveHead, hroom]
    · rfl
  have hblank : c₂.tape c₂.head = none := by
    change FixedPairConcatSentinel.sentinelTape B raw
      ⟨2 * i + 2, by unfold tapeLength; omega⟩ = none
    have hnot : ¬ 2 * i + 2 < 2 * i + 1 := by omega
    simp [FixedPairConcatSentinel.sentinelTape, hnot]
  have haction₂ : machine.step c₂.state (c₂.tape c₂.head) =
      (qReject, c₂.tape c₂.head, .stay) := by
    rw [hblank]
    exact step_tag_none
  have hstep₂ : machine.stepConfig c₂ = rejectConfig B raw hB := by
    rw [step_preserving c₂ qReject .stay haction₂]
    apply config_ext
    · rfl
    · apply Fin.ext
      rfl
    · rfl
  calc
    machine.run (2 * i + 3) (startConfig B raw) =
        machine.run 3 (machine.run (2 * i) (startConfig B raw)) := by
      rw [← machine.run_add]
    _ = machine.run 3 c₀ := by rw [hscan]
    _ = machine.stepConfig
          (machine.stepConfig (machine.stepConfig c₀)) := rfl
    _ = machine.stepConfig (machine.stepConfig c₁) := by rw [hstep₀]
    _ = machine.stepConfig c₂ := by rw [hstep₁]
    _ = rejectConfig B raw hB := hstep₂

/-- Every canonically sentinelized malformed raw pair reaches the literal
reject state at the exact structural time `N+2`, with head at `N+1` and the
entire tape unchanged.  Positive padding is used only to make `N+1` a genuine
cell rather than a clamped right boundary. -/
private theorem run_malformed_exact {N B : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (hB : 0 < B) :
    machine.run (N + 2) (startConfig B raw) = rejectConfig B raw hB := by
  rcases even_or_odd N with ⟨i, hN⟩ | ⟨i, hN⟩
  · exact malformed_even_reject raw hdecode hB i hN
  · exact malformed_odd_reject raw hdecode hB i hN

theorem malformed_literal_fields {N B : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (hB : 0 < B) :
    (machine.run (N + 2) (startConfig B raw)).state = qReject ∧
    (machine.run (N + 2) (startConfig B raw)).head.val = N + 1 ∧
    (machine.run (N + 2) (startConfig B raw)).tape =
      FixedPairConcatSentinel.sentinelTape B raw := by
  rw [run_malformed_exact raw hdecode hB]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Bundled honest phase contract -/

/-- The bundled valid-pair contract exposes the exact final configuration,
strict first terminal, sharp footprint attainment, complete tape preservation,
and literal accepting fields. Boundary-clamp safety and cross-budget
independence are proved separately by `no_boundary_clamp_before_clock` and
`run_budget_independent`. The remaining invariant is deliberately still tagged,
with the head at the physical separator. -/
theorem phase_contract {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let c₀ := startConfig B (encodePair x w)
    machine.run (clock n) c₀ = finalConfig B x w ∧
    (∀ s, s < clock n →
      (machine.run s c₀).state ≠ qAccept ∧
      (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ clock n →
      (machine.run s c₀).head.val ≤ 2 * n + 1) ∧
    (machine.run (2 * n + 1) c₀).head.val = 2 * n + 1 ∧
    (∀ s, s ≤ clock n →
      (machine.run s c₀).tape =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w)) ∧
    (machine.run (clock n) c₀).state = qAccept ∧
    (machine.run (clock n) c₀).head.val = 2 * n := by
  dsimp
  refine ⟨run_encoded_exact B x w,
    fun s hs => noEarlyTerminal x w s hs,
    fun s hs => head_le_separator_successor_through_clock x w s hs,
    reaches_separator_successor x w,
    fun s hs => (valid_trace_fields x w s hs).1, ?_, ?_⟩
  · exact (final_literal_fields (B := B) x w).1
  · exact (final_literal_fields (B := B) x w).2

end FixedPairSeparatorCursor

end Pnp3.Complexity.Uniform.V1
