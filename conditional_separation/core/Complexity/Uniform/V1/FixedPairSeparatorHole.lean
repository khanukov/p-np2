import Complexity.Uniform.V1.FixedPairSeparatorCursor
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Fixed pair separator hole

This is the next deliberately small operational phase after
`FixedPairSeparatorCursor`.  The cursor halts in literal accept with its head
on the still-present separator at cell `2*n` of the sentinelized tagged pair
layout.  This phase consumes exactly that configuration, overwrites the one
scanned cell with the blank `none`, and halts in literal accept with the head
still at `2*n`.  Nothing else changes: the tagged query to the left, the
witness and the marker to the right, and the blank suffix are all literally
preserved.  The split survives as an interior blank hole.

**Machine.**  Three states.  The start row blanks the scanned cell only when
it reads the separator value `some true`; any other scanned symbol is written
back unchanged and the machine rejects in place.  The table contains no input
length, query length, witness length, budget, clock, decoder, evaluator, or
callback into the source relation.

**Clock.**  Exactly one transition.  The constant clock is read off the single
row that fires on the valid handoff.  It does not depend on `n`, `m`, or `B`.

**Handoff.**  `startConfig` is obtained by `retag`: the cursor's exact valid
final configuration with only its finite control replaced by `qStart`.  Head
and tape are copied verbatim.  Retagging is a proof-level phase boundary
between two separately proved machines.  It is *not* the operational routing
of a combined machine: `FixedParserVerifier` merges transition tables and
routes the parser's accept edge into the verifier's start row, whereas here no
merged table exists and no machine performs the control change.

**Why separator deletion is safe here.**  The cursor module rejects
separator-first deletion because deleting the separator *and closing the gap*
collapses different splits: `x = [b], w = []` and `x = [], w = [false, b]`
both compact to the headerless content `[false, b]`.  In this phase the gap is
not closed.  The split survives in the full configuration twice over: the head
address is `2*n`, and cell `2*n` is the unique blank cell at or below the
marker.  `holeTape_natView_injective` proves that the final tape alone, read
as a total address view, already determines the packed pair `(n, x, m, w)`.

**Zero cases.**  The raw length `pairLength n m` is never zero on a valid
pair, so the relevant zero cases are `n = 0` (hole at the origin), `m = 0`
(the hole's right neighbour is the marker), and `B = 0` (minimal allocation).
Every theorem below quantifies over all three, and the three cases are also
stated explicitly.

**Non-claims.**  This phase does not remove tags, shift the witness, compact
the payload, evaluate any relation, build a combined machine, or claim
anything about malformed raw words.  The only statements about non-separator
scanned symbols are the configuration-level row facts
`stepConfig_start_separator` and `stepConfig_start_non_separator`, which hold
for every configuration and are not decoder claims.
-/

namespace Pnp3.Complexity.Uniform.V1

namespace FixedPairSeparatorHole

open PairEncoding

abbrev holeStateCount : Nat := 3

def qStart : Fin holeStateCount :=
  ⟨0, by decide⟩

def qAccept : Fin holeStateCount :=
  ⟨1, by decide⟩

def qReject : Fin holeStateCount :=
  ⟨2, by decide⟩

/-!
On a valid cursor handoff, `qStart` fires exactly once on the separator cell.
The separator value is
`some true`; only that value is replaced by the blank `none`.  A tag value
`some false` or a blank `none` is written back unchanged and rejected in
place, so the row can never create a blank anywhere except from a `some true`
cell.
-/
private def holeRawStep
    (q : Fin holeStateCount)
    (scanned : Option Bool) :
    Fin holeStateCount × Option Bool × Move :=
  match q.val with
  | 0 =>
      match scanned with
      | none => (qReject, none, .stay)
      | some false => (qReject, some false, .stay)
      | some true => (qAccept, none, .stay)
  | 1 => (qAccept, scanned, .stay)
  | _ => (qReject, scanned, .stay)

/-- The closed three-state separator-hole machine. -/
def machine : UniformTM where
  stateCount := holeStateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := holeRawStep

/-- Exhaustive pin for all three rows of the installed raw table. -/
theorem holeRawStep_table :
    (∀ scanned,
      machine.rawStep qStart scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some false => (qReject, some false, .stay)
        | some true => (qAccept, none, .stay)) ∧
    (∀ scanned,
      machine.rawStep qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned,
      machine.rawStep qReject scanned = (qReject, scanned, .stay)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro scanned
    cases scanned with
    | none => rfl
    | some b => cases b <;> rfl
  · intro scanned
    rfl
  · intro scanned
    rfl

/-- Exact finite-control and transition-table resource pins. -/
theorem machine_resource_pins :
    machine.stateCount = 3 ∧
    machine.start = qStart ∧
    machine.accept = qAccept ∧
    machine.reject = qReject ∧
    qStart.val = 0 ∧
    qAccept.val = 1 ∧
    qReject.val = 2 ∧
    Fintype.card (Fin machine.stateCount) = 3 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 9 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · change Fintype.card (Fin 3 × Option Bool) = 9
    decide

/-! ## Exact cursor handoff by retagging -/

/-- Replace only the finite control of a cursor configuration by the hole
start control.  Head and tape are copied verbatim.  This is a proof-level
phase boundary between two separately proved machines: it is not a transition
of either machine and not the routed table of a combined machine. -/
def retag {N B : Nat}
    (c : Config FixedPairSeparatorCursor.cursorStateCount N B) :
    Config holeStateCount N B where
  state := qStart
  head := c.head
  tape := c.tape

/-- Retagging changes only the finite control. -/
theorem retag_fields {N B : Nat}
    (c : Config FixedPairSeparatorCursor.cursorStateCount N B) :
    (retag c).state = qStart ∧
    (retag c).head = c.head ∧
    (retag c).tape = c.tape :=
  ⟨rfl, rfl, rfl⟩

/-- The phase-start configuration: the cursor's exact valid final
configuration with its finite control retagged. -/
def startConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config holeStateCount (pairLength n m) B :=
  retag (FixedPairSeparatorCursor.finalConfig B x w)

/-- Exact handoff from the proved cursor run: the start configuration is
literally the retagged cursor run at the cursor clock.  Field by field, the
cursor halts in its own literal accept control, the retagged control is
`qStart`, and head and tape are the cursor's exact final fields. -/
theorem startConfig_of_cursor_run {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let cursorFinal := FixedPairSeparatorCursor.machine.run
      (FixedPairSeparatorCursor.clock n)
      (FixedPairSeparatorCursor.startConfig B (encodePair x w))
    startConfig B x w = retag cursorFinal ∧
    cursorFinal.state = FixedPairSeparatorCursor.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = cursorFinal.head ∧
    (startConfig B x w).tape = cursorFinal.tape := by
  dsimp
  rw [FixedPairSeparatorCursor.run_encoded_exact]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## One-step clock and exact final configuration -/

/-- Exactly one transition: the start row fires once on the separator. -/
def clock : Nat :=
  1

theorem clock_eq : clock = 1 :=
  rfl

/-- The exact final layout: the sentinel layout with only cell `2*n`
blanked. -/
def holeTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i =>
    if i.val = 2 * n then none
    else FixedPairConcatSentinel.sentinelTape B (encodePair x w) i

/-- Exact successful postconfiguration: literal accept, head still on the
hole address `2*n`, and the hole layout. -/
def finalConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config holeStateCount (pairLength n m) B where
  state := qAccept
  head := ⟨2 * n, by unfold tapeLength pairLength; omega⟩
  tape := holeTape B x w

/-! ## Small execution bridges -/

private theorem config_ext
    {N B : Nat} {c d : Config holeStateCount N B}
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
    {N B : Nat} (c : Config holeStateCount N B) :
    (machine.stepConfig c).state =
      (machine.step c.state (c.tape c.head)).1 :=
  rfl

private theorem stepConfig_head
    {N B : Nat} (c : Config holeStateCount N B) :
    (machine.stepConfig c).head =
      moveHead c.head (machine.step c.state (c.tape c.head)).2.2 :=
  rfl

private theorem stepConfig_tape
    {N B : Nat} (c : Config holeStateCount N B)
    (i : Fin (tapeLength N B)) :
    (machine.stepConfig c).tape i =
      if i = c.head
      then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i :=
  rfl

private theorem step_start_none :
    machine.step qStart none = (qReject, none, .stay) := by
  rfl

private theorem step_start_false :
    machine.step qStart (some false) = (qReject, some false, .stay) := by
  rfl

private theorem step_start_true :
    machine.step qStart (some true) = (qAccept, none, .stay) := by
  rfl

/-! ## Configuration-level row facts -/

/-- On the separator value the scanned cell is blanked, the head stays, and
the control becomes literal accept.  This holds for every configuration in
`qStart`, whatever the rest of the tape holds. -/
theorem stepConfig_start_separator {N B : Nat}
    (c : Config holeStateCount N B)
    (hstate : c.state = qStart) (hread : c.tape c.head = some true) :
    machine.stepConfig c =
      ({ state := qAccept
         head := c.head
         tape := fun i => if i = c.head then none else c.tape i } :
        Config holeStateCount N B) := by
  have haction : machine.step c.state (c.tape c.head) =
      (qAccept, none, .stay) := by
    rw [hstate, hread]
    exact step_start_true
  apply config_ext
  · rw [stepConfig_state, haction]
  · rw [stepConfig_head, haction]
    rfl
  · funext i
    rw [stepConfig_tape, haction]

/-- On any other scanned value the cell is written back unchanged and the
machine rejects in place.  In particular the start row can never create a
blank except from a `some true` cell. -/
theorem stepConfig_start_non_separator {N B : Nat}
    (c : Config holeStateCount N B)
    (hstate : c.state = qStart) (hread : c.tape c.head ≠ some true) :
    machine.stepConfig c =
      ({ state := qReject
         head := c.head
         tape := c.tape } : Config holeStateCount N B) := by
  have haction : machine.step c.state (c.tape c.head) =
      (qReject, c.tape c.head, .stay) := by
    rw [hstate]
    cases hsym : c.tape c.head with
    | none => exact step_start_none
    | some b =>
        cases b with
        | false => exact step_start_false
        | true => exact absurd hsym hread
  apply config_ext
  · rw [stepConfig_state, haction]
  · rw [stepConfig_head, haction]
    rfl
  · funext i
    rw [stepConfig_tape, haction]
    by_cases hi : i = c.head
    · subst hi
      simp
    · simp [hi]

/-! ## Exact valid run -/

private theorem start_read_separator {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (startConfig B x w).tape (startConfig B x w).head = some true := by
  change FixedPairConcatSentinel.sentinelTape B (encodePair x w)
      ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = some true
  have hinput : 2 * n < pairLength n m := by
    unfold pairLength
    omega
  simp [FixedPairConcatSentinel.sentinelTape, hinput, encodePair_separator]

private theorem step_start_to_final {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (startConfig B x w) = finalConfig B x w := by
  rw [stepConfig_start_separator (startConfig B x w) rfl
    (start_read_separator x w)]
  apply config_ext
  · rfl
  · rfl
  · funext i
    change (if i = (startConfig B x w).head then none
        else (startConfig B x w).tape i) = holeTape B x w i
    unfold holeTape
    by_cases hi : i.val = 2 * n
    · have hi' : i = (startConfig B x w).head := Fin.ext hi
      rw [if_pos hi', if_pos hi]
    · have hi' : i ≠ (startConfig B x w).head :=
        fun h => hi (congrArg Fin.val h)
      rw [if_neg hi', if_neg hi]
      rfl

/-- Exact literal preterminal fields at time zero: control `qStart`, head on
the separator, the complete sentinel tape, and the scanned separator value.
-/
theorem run_preterminal_exact {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    machine.run 0 (startConfig B x w) = startConfig B x w ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head.val = 2 * n ∧
    (startConfig B x w).tape =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
    (startConfig B x w).tape (startConfig B x w).head = some true :=
  ⟨rfl, rfl, rfl, rfl, start_read_separator x w⟩

/-- Required exact full-configuration theorem.  It holds for every query
length, witness length, and external allocation, including `n = 0`, `m = 0`,
and `B = 0`. -/
theorem run_encoded_exact {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run clock (startConfig B x w) = finalConfig B x w := by
  unfold clock
  simpa [UniformTM.run] using step_start_to_final (B := B) x w

private theorem run_one {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run 1 (startConfig B x w) = finalConfig B x w :=
  run_encoded_exact B x w

/-- Literal verdict and exact hole address.  The query length is recovered
from the head alone. -/
theorem final_literal_fields {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run clock (startConfig B x w)).state = qAccept ∧
    (machine.run clock (startConfig B x w)).state = machine.accept ∧
    (machine.run clock (startConfig B x w)).head.val = 2 * n ∧
    (machine.run clock (startConfig B x w)).head.val / 2 = n := by
  rw [run_encoded_exact]
  refine ⟨rfl, rfl, rfl, ?_⟩
  change 2 * n / 2 = n
  omega

/-! ## Exact final tape -/

theorem final_tape_eq_holeTape {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run clock (startConfig B x w)).tape = holeTape B x w := by
  rw [run_encoded_exact]
  rfl

private theorem holeTape_off {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) B)) (hi : i.val ≠ 2 * n) :
    holeTape B x w i =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) i := by
  simp [holeTape, hi]

private theorem holeTape_hole {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    holeTape B x w ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = none := by
  simp [holeTape]

private theorem holeTape_input {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : k < pairLength n m) (hne : k ≠ 2 * n) :
    holeTape B x w ⟨k, by unfold tapeLength; omega⟩ =
      some (encodePair x w ⟨k, hk⟩) := by
  simp [holeTape, FixedPairConcatSentinel.sentinelTape, hne, hk]

private theorem holeTape_marker {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    holeTape B x w ⟨pairLength n m, by unfold tapeLength; omega⟩ =
      some true := by
  have hne : pairLength n m ≠ 2 * n := by
    unfold pairLength
    omega
  simp [holeTape, FixedPairConcatSentinel.sentinelTape, hne]

private theorem holeTape_beyond {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) B)) (hi : pairLength n m < i.val) :
    holeTape B x w i = none := by
  have hne : i.val ≠ 2 * n := by
    unfold pairLength at hi
    omega
  have hnot : ¬ i.val < pairLength n m := by omega
  have hne' : i.val ≠ pairLength n m := by omega
  simp [holeTape, FixedPairConcatSentinel.sentinelTape, hne, hnot, hne']

/-- The final tape is literally the sentinel tape updated at the single
address `2*n` to blank. -/
theorem final_tape_eq_update {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run clock (startConfig B x w)).tape =
      Function.update
        (FixedPairConcatSentinel.sentinelTape B (encodePair x w))
        ⟨2 * n, by unfold tapeLength pairLength; omega⟩ none := by
  rw [final_tape_eq_holeTape]
  funext i
  rw [Function.update_apply]
  by_cases hi : i.val = 2 * n
  · have hi' : i = ⟨2 * n, by unfold tapeLength pairLength; omega⟩ :=
      Fin.ext hi
    rw [if_pos hi', hi']
    exact holeTape_hole x w
  · have hi' : i ≠ ⟨2 * n, by unfold tapeLength pairLength; omega⟩ :=
      fun h => hi (congrArg Fin.val h)
    rw [if_neg hi']
    exact holeTape_off x w i hi

/-- Pointwise final tape contract.  The hole is blank; every query tag, every
query data bit, every witness bit, and the marker are literally unchanged;
every cell above the marker is blank. -/
theorem final_tape_behavior {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let cF := machine.run clock (startConfig B x w)
    cF.tape ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = none ∧
    (∀ i : Fin n,
      cF.tape ⟨2 * i.val, by unfold tapeLength pairLength; omega⟩ =
        some false) ∧
    (∀ i : Fin n,
      cF.tape ⟨2 * i.val + 1, by unfold tapeLength pairLength; omega⟩ =
        some (x i)) ∧
    (∀ j : Fin m,
      cF.tape ⟨2 * n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (w j)) ∧
    cF.tape ⟨pairLength n m, by unfold tapeLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m < i.val → cF.tape i = none) := by
  dsimp
  rw [final_tape_eq_holeTape]
  refine ⟨holeTape_hole x w, fun i => ?_, fun i => ?_, fun j => ?_,
    holeTape_marker x w, fun i hi => holeTape_beyond x w i hi⟩
  · have hk : 2 * i.val < pairLength n m := by
      unfold pairLength
      omega
    have hne : 2 * i.val ≠ 2 * n := by omega
    rw [holeTape_input x w _ hk hne]
    exact congrArg some (encodePair_tag x w i)
  · have hk : 2 * i.val + 1 < pairLength n m := by
      unfold pairLength
      omega
    have hne : 2 * i.val + 1 ≠ 2 * n := by omega
    rw [holeTape_input x w _ hk hne]
    exact congrArg some (encodePair_data x w i)
  · have hk : 2 * n + 1 + j.val < pairLength n m := by
      unfold pairLength
      omega
    have hne : 2 * n + 1 + j.val ≠ 2 * n := by omega
    rw [holeTape_input x w _ hk hne]
    exact congrArg some (encodePair_witness x w j)

/-- Complete blank characterization: a cell is blank exactly when it is the
hole or lies above the marker.  Hence the hole is the unique blank cell at or
below the marker. -/
theorem final_blank_iff {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) B)) :
    (machine.run clock (startConfig B x w)).tape i = none ↔
      (i.val = 2 * n ∨ pairLength n m < i.val) := by
  rw [final_tape_eq_holeTape]
  rcases i with ⟨k, hkfit⟩
  show holeTape B x w ⟨k, hkfit⟩ = none ↔ (k = 2 * n ∨ pairLength n m < k)
  constructor
  · intro h
    by_cases hk : k = 2 * n
    · exact Or.inl hk
    · right
      by_contra hle
      have hle' : k ≤ pairLength n m := Nat.le_of_not_lt hle
      rcases Nat.lt_or_eq_of_le hle' with hlt | heq
      · rw [holeTape_input x w k hlt hk] at h
        cases h
      · subst heq
        rw [holeTape_marker x w] at h
        cases h
  · rintro (hk | hk)
    · subst hk
      exact holeTape_hole x w
    · exact holeTape_beyond x w ⟨k, hkfit⟩ hk

/-- The hole is interior: it lies strictly below the marker, its right
neighbour is nonblank (the first witness bit, or the marker itself when the
witness is empty), and its left neighbour, when it exists, is the last query
data bit. -/
theorem hole_interior {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let cF := machine.run clock (startConfig B x w)
    2 * n < pairLength n m ∧
    (∀ hm : 0 < m,
      cF.tape ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ =
        some (w ⟨0, hm⟩)) ∧
    (m = 0 →
      cF.tape ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ =
        some true) ∧
    (∀ hn : 0 < n,
      cF.tape ⟨2 * n - 1, by unfold tapeLength pairLength; omega⟩ =
        some (x ⟨n - 1, by omega⟩)) := by
  dsimp
  rw [final_tape_eq_holeTape]
  refine ⟨by unfold pairLength; omega, fun hm => ?_, fun hm => ?_,
    fun hn => ?_⟩
  · have hk : 2 * n + 1 < pairLength n m := by
      unfold pairLength
      omega
    have hne : 2 * n + 1 ≠ 2 * n := by omega
    rw [holeTape_input x w _ hk hne]
    exact congrArg some (encodePair_witness x w ⟨0, hm⟩)
  · subst hm
    have hidx : (⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ :
        Fin (tapeLength (pairLength n 0) B)) =
          ⟨pairLength n 0, by unfold tapeLength; omega⟩ :=
      Fin.ext (by
        show 2 * n + 1 = pairLength n 0
        unfold pairLength
        omega)
    rw [hidx]
    exact holeTape_marker x w
  · have hk : 2 * n - 1 < pairLength n m := by
      unfold pairLength
      omega
    have hne : 2 * n - 1 ≠ 2 * n := by omega
    rw [holeTape_input x w _ hk hne]
    have hidx : (⟨2 * n - 1, hk⟩ : Fin (pairLength n m)) =
        ⟨2 * (n - 1) + 1, by unfold pairLength; omega⟩ :=
      Fin.ext (by
        show 2 * n - 1 = 2 * (n - 1) + 1
        omega)
    rw [hidx]
    exact congrArg some (encodePair_data x w ⟨n - 1, by omega⟩)

/-! ## The split survives in the configuration -/

/-- Total address view of a finite tape: addresses outside the allocation
read as blank, so tapes on different budgets can be compared address by
address. -/
def natView {L : Nat} (t : Fin L → Option Bool) (i : Nat) : Option Bool :=
  if h : i < L then t ⟨i, h⟩ else none

private theorem natView_hole {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    natView (holeTape B x w) (2 * n) = none := by
  have h : 2 * n < tapeLength (pairLength n m) B := by
    unfold tapeLength pairLength
    omega
  unfold natView
  rw [dif_pos h]
  exact holeTape_hole x w

private theorem natView_input {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : k < pairLength n m) (hne : k ≠ 2 * n) :
    natView (holeTape B x w) k = some (encodePair x w ⟨k, hk⟩) := by
  have h : k < tapeLength (pairLength n m) B := by
    unfold tapeLength
    omega
  unfold natView
  rw [dif_pos h]
  exact holeTape_input x w k hk hne

private theorem natView_marker {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    natView (holeTape B x w) (pairLength n m) = some true := by
  have h : pairLength n m < tapeLength (pairLength n m) B := by
    unfold tapeLength
    omega
  unfold natView
  rw [dif_pos h]
  exact holeTape_marker x w

private theorem natView_beyond {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : pairLength n m < k) :
    natView (holeTape B x w) k = none := by
  unfold natView
  split_ifs with h
  · exact holeTape_beyond x w ⟨k, h⟩ hk
  · rfl

private theorem natView_data {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (i : Fin n) :
    natView (holeTape B x w) (2 * i.val + 1) = some (x i) := by
  have hk : 2 * i.val + 1 < pairLength n m := by
    unfold pairLength
    omega
  have hne : 2 * i.val + 1 ≠ 2 * n := by omega
  rw [natView_input x w _ hk hne]
  exact congrArg some (encodePair_data x w i)

private theorem natView_witness {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (j : Fin m) :
    natView (holeTape B x w) (2 * n + 1 + j.val) = some (w j) := by
  have hk : 2 * n + 1 + j.val < pairLength n m := by
    unfold pairLength
    omega
  have hne : 2 * n + 1 + j.val ≠ 2 * n := by omega
  rw [natView_input x w _ hk hne]
  exact congrArg some (encodePair_witness x w j)

private theorem words_of_natView_eq {n m B B' : Nat}
    (x x' : Bitstring n) (w w' : Bitstring m)
    (h : natView (holeTape B x w) = natView (holeTape B' x' w')) :
    x = x' ∧ w = w' := by
  refine ⟨funext fun i => ?_, funext fun j => ?_⟩
  · have h1 := congrFun h (2 * i.val + 1)
    rw [natView_data x w i, natView_data x' w' i] at h1
    exact Option.some.inj h1
  · have h1 := congrFun h (2 * n + 1 + j.val)
    rw [natView_witness x w j, natView_witness x' w' j] at h1
    exact Option.some.inj h1

/-- The final tape alone determines the packed pair.  Two hole tapes with the
same total address view, on any two budgets, come from the same query length,
the same witness length, and the same words.  This is exactly the property
that separator deletion with gap closing lacks. -/
theorem holeTape_natView_injective {n m n' m' : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (x' : Bitstring n') (w' : Bitstring m')
    (h : natView (holeTape B x w) = natView (holeTape B' x' w')) :
    ((⟨n, x⟩, ⟨m, w⟩) : DecodedPair) =
      ((⟨n', x'⟩, ⟨m', w'⟩) : DecodedPair) := by
  have hN : pairLength n m = pairLength n' m' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := congrFun h (pairLength n' m')
      rw [natView_beyond x w _ hlt, natView_marker x' w'] at h1
      cases h1
    · have h1 := congrFun h (pairLength n m)
      rw [natView_marker x w, natView_beyond x' w' _ hgt] at h1
      cases h1
  have hn : n = n' := by
    by_contra hne
    have hne2 : 2 * n ≠ 2 * n' := by omega
    have hlt : 2 * n < pairLength n' m' := by
      rw [← hN]
      unfold pairLength
      omega
    have h1 := congrFun h (2 * n)
    rw [natView_hole x w, natView_input x' w' _ hlt hne2] at h1
    cases h1
  subst hn
  have hm : m = m' := by
    unfold pairLength at hN
    omega
  subst hm
  obtain ⟨hx, hw⟩ := words_of_natView_eq x x' w w' h
  subst hx
  subst hw
  rfl

/-- Configuration-level form: equal final tapes, read as total address views
on any two budgets, force equal packed pairs.  Together with the literal head
address `2*n` this is why the full final configuration retains the split. -/
theorem final_tape_determines_pair {n m n' m' : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (x' : Bitstring n') (w' : Bitstring m')
    (h : natView (machine.run clock (startConfig B x w)).tape =
      natView (machine.run clock (startConfig B' x' w')).tape) :
    ((⟨n, x⟩, ⟨m, w⟩) : DecodedPair) =
      ((⟨n', x'⟩, ⟨m', w'⟩) : DecodedPair) := by
  rw [run_encoded_exact B x w, run_encoded_exact B' x' w'] at h
  exact holeTape_natView_injective B B' x w x' w' h

/-- Within one index type and one budget, the final configuration is
injective in the two words. -/
theorem finalConfig_injective {n m B : Nat}
    (x x' : Bitstring n) (w w' : Bitstring m)
    (h : finalConfig B x w = finalConfig B x' w') :
    x = x' ∧ w = w' := by
  have ht : holeTape B x w = holeTape B x' w' := congrArg Config.tape h
  exact words_of_natView_eq x x' w w' (congrArg natView ht)

/-! ## Footprint, budget independence, and boundary safety -/

private theorem run_le_clock_cases (s : Nat) (hs : s ≤ clock) :
    s = 0 ∨ s = 1 := by
  unfold clock at hs
  omega

/-- The head never moves: at every time through the clock it is the
phase-start head, at address `2*n`. -/
theorem head_fixed_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock) :
    (machine.run s (startConfig B x w)).head = (startConfig B x w).head ∧
    (machine.run s (startConfig B x w)).head.val = 2 * n := by
  rcases run_le_clock_cases s hs with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [run_one]
    exact ⟨rfl, rfl⟩

/-- Every cell other than the hole address is literally unchanged at every
time through the clock. -/
theorem tape_off_hole_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock)
    (i : Fin (tapeLength (pairLength n m) B)) (hi : i.val ≠ 2 * n) :
    (machine.run s (startConfig B x w)).tape i =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) i := by
  rcases run_le_clock_cases s hs with rfl | rfl
  · rfl
  · rw [run_one]
    exact holeTape_off x w i hi

/-- The hole cell itself: the separator value before the transition and
blank after it. -/
theorem hole_cell_trace {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run 0 (startConfig B x w)).tape
      ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (machine.run clock (startConfig B x w)).tape
      ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = none := by
  refine ⟨start_read_separator x w, ?_⟩
  rw [final_tape_eq_holeTape]
  exact holeTape_hole x w

/-- Execution is independent of padding: state and natural head agree, and
every pair of common addresses has the same exact tape symbol, at every time
through the clock. -/
theorem run_budget_independent {n m : Nat}
    (B B' : Nat) (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock) :
    (machine.run s (startConfig B x w)).state =
      (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
      (machine.run s (startConfig B' x w)).head.val ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i') := by
  rcases run_le_clock_cases s hs with rfl | rfl
  · refine ⟨rfl, rfl, fun i i' hii' => ?_⟩
    change FixedPairConcatSentinel.sentinelTape B (encodePair x w) i =
      FixedPairConcatSentinel.sentinelTape B' (encodePair x w) i'
    simp [FixedPairConcatSentinel.sentinelTape, hii']
  · rw [run_one B x w, run_one B' x w]
    refine ⟨rfl, rfl, fun i i' hii' => ?_⟩
    change holeTape B x w i = holeTape B' x w i'
    simp [holeTape, FixedPairConcatSentinel.sentinelTape, hii']

/-- The only transition through the clock is a stay, so neither boundary
clamp of `moveHead` can fire. -/
theorem no_boundary_clamp_before_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock) :
    let c := machine.run s (startConfig B x w)
    let move := (machine.step c.state (c.tape c.head)).2.2
    move = .stay ∧
    (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (move = .left → 0 < c.head.val) := by
  dsimp
  have hs0 : s = 0 := by
    unfold clock at hs
    omega
  subst hs0
  change (machine.step qStart
      ((startConfig B x w).tape (startConfig B x w).head)).2.2 = .stay ∧
    ((machine.step qStart
      ((startConfig B x w).tape (startConfig B x w).head)).2.2 = .right →
        2 * n + 1 < tapeLength (pairLength n m) B) ∧
    ((machine.step qStart
      ((startConfig B x w).tape (startConfig B x w).head)).2.2 = .left →
        0 < 2 * n)
  rw [start_read_separator x w, step_start_true]
  exact ⟨rfl, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-! ## Strict terminal behavior -/

theorem noEarlyTerminal {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock) :
    (machine.run s (startConfig B x w)).state ≠ qAccept ∧
    (machine.run s (startConfig B x w)).state ≠ qReject := by
  have hs0 : s = 0 := by
    unfold clock at hs
    omega
  subst hs0
  change qStart ≠ qAccept ∧ qStart ≠ qReject
  decide

theorem run_after_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (extra : Nat) :
    machine.run (clock + extra) (startConfig B x w) = finalConfig B x w := by
  rw [machine.run_add, run_encoded_exact,
    machine.run_accept (finalConfig B x w) rfl extra]

/-! ## Explicit zero cases -/

/-- Empty query: the hole is at the origin and there is no tagged query to
its left. -/
theorem run_zero_query_exact {m : Nat} (B : Nat)
    (x : Bitstring 0) (w : Bitstring m) :
    machine.run clock (startConfig B x w) = finalConfig B x w ∧
    (machine.run clock (startConfig B x w)).head.val = 0 ∧
    (machine.run clock (startConfig B x w)).tape
      ⟨0, by unfold tapeLength; omega⟩ = none := by
  refine ⟨run_encoded_exact B x w, ?_, ?_⟩
  · rw [run_encoded_exact]
    rfl
  · rw [final_tape_eq_holeTape]
    exact holeTape_hole x w

/-- Empty witness: the hole's right neighbour is the marker itself. -/
theorem run_empty_witness_exact {n : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring 0) :
    machine.run clock (startConfig B x w) = finalConfig B x w ∧
    pairLength n 0 = 2 * n + 1 ∧
    (machine.run clock (startConfig B x w)).tape
      ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ = some true :=
  ⟨run_encoded_exact B x w, rfl, (hole_interior x w).2.2.1 rfl⟩

/-- Zero budget: the allocation is exactly `N + 1` cells and the phase still
runs exactly. -/
theorem run_zero_budget_exact {n m : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    tapeLength (pairLength n m) 0 = pairLength n m + 1 ∧
    machine.run clock (startConfig 0 x w) = finalConfig 0 x w :=
  ⟨rfl, run_encoded_exact 0 x w⟩

/-- The smallest valid instance, `n = m = B = 0`: the two cells
`[separator][marker]` become `[hole][marker]`. -/
theorem run_minimal_literal :
    let x : Bitstring 0 := fun i => Fin.elim0 i
    let w : Bitstring 0 := fun i => Fin.elim0 i
    List.ofFn (startConfig 0 x w).tape = [some true, some true] ∧
    List.ofFn (machine.run clock (startConfig 0 x w)).tape =
      [none, some true] := by
  dsimp
  rw [run_encoded_exact]
  constructor <;> decide

/-! ## Bundled honest phase contract -/

/-- The bundled valid-pair contract: exact retagged handoff, exact final
configuration after one transition, strict preterminality, fixed head, the
single-cell write, literal acceptance at the hole address, and the blank
characterization that a later tag-removal or hole-shift phase needs.  Budget
independence, boundary-clamp safety, and the packed injectivity are proved
separately by `run_budget_independent`, `no_boundary_clamp_before_clock`, and
`final_tape_determines_pair`. -/
theorem phase_contract {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let c₀ := startConfig B x w
    c₀ = retag (FixedPairSeparatorCursor.finalConfig B x w) ∧
    machine.run clock c₀ = finalConfig B x w ∧
    (∀ s, s < clock →
      (machine.run s c₀).state ≠ qAccept ∧
      (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ clock → (machine.run s c₀).head.val = 2 * n) ∧
    (∀ s, s ≤ clock → ∀ i : Fin (tapeLength (pairLength n m) B),
      i.val ≠ 2 * n →
      (machine.run s c₀).tape i =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w) i) ∧
    (machine.run clock c₀).state = qAccept ∧
    (machine.run clock c₀).head.val = 2 * n ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      (machine.run clock c₀).tape i = none ↔
        (i.val = 2 * n ∨ pairLength n m < i.val)) := by
  dsimp
  exact ⟨rfl, run_encoded_exact B x w,
    fun s hs => noEarlyTerminal x w s hs,
    fun s hs => (head_fixed_through_clock x w s hs).2,
    fun s hs i hi => tape_off_hole_through_clock x w s hs i hi,
    (final_literal_fields x w).1,
    (final_literal_fields x w).2.2.1,
    fun i => final_blank_iff x w i⟩

end FixedPairSeparatorHole

end Pnp3.Complexity.Uniform.V1
