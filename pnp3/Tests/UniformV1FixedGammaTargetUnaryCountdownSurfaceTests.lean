import Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown

/-!
Surface pins for the Part A G2s-a unary countdown round: a **new** fixed 11-state, 33-row machine
that subtracts one more from the target register G2q decremented and lays one mark in a tally lane.
All 33 transition rows are restated literally below, not aliased.

What is pinned.  The navigation is symbol-driven throughout — `qSeekSep` stops on the separator
blank, `qBorrow` on the first set digit or on the boundary blank, `qPadL` and `qPadR` on those two
blanks, `qRunEnd` on the first blank of the lane and `qBackRun` back on the separator
(`check_table_rows`).  `check_entry_generic` *enters* `qLoop` in exactly `d + 2` steps writing
nothing; `check_round_generic` costs exactly `roundClock zeros r = 2*zeros + 2*r + 7` and leaves the
register holding `v - 1` with one more mark; `check_exhaust_generic` costs exactly
`zeroClock zeros = 2*zeros + 5` and leaves the tape unchanged; `check_first_round` runs the entry
and the first round out of the phase-local `startConfig`, whose handoff time is G2q's own
length-only `deadline (a+m)`.  `check_loopTape_pins` places every cell with no hypothesis at all,
and `check_loopTape_zero_eq_decTape` identifies the entry tape with G2q's endpoint tape.

Not here and not available to pin.  The **iteration**: no wrapper iterates the round, and none may
before the fence below is settled in the family plan.  The **fence**: the lane is uncapped here, so
a register too large for the budget runs `qRunEnd` off the tape and sticks, which is a timeout and
so neither verdict; the `qRunEnd`-on-`some false` row is pinned and deliberately unexercised.  Any
**pnp4 bridge**, and with it every connection to `contentHeader?`, `contentInput?` or a parsed
target — nothing supplies the `v` of `check_first_round`, whose `check_first_round_instance` values
`24` and `23` are hand-written literals.  A **footprint or budget theorem**, so no room premise is
shown necessary.  Every **converse** — no wrapper says that `qLoop`, `qDone` or any endpoint cell
implies anything about `zeros`, about `v` or about the incoming digits.  A malformed-gamma branch,
since G2q characterises none.  And any restoration of the gamma leading-digit convention.

The lane holds marks, not a target in unary: no wrapper here decodes anything.  `qLoop` does not
absorb, so every `qLoop` endpoint below is an exact time and not a deadline, and
`check_exhaust_generic`'s last conjunct is persistence, not first arrival.  `qDone` is an internal
control tag of a machine started here from a phase-local retag of an actual prior run, so it is
neither halting of a composed machine nor language acceptance, and the clocks compose no earlier
clock. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetUnaryCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (finishTape)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (decBit decTape borrow deadline)

def check_stateCount : Nat := stateCount
def check_states : List (Fin stateCount) :=
  [qStart, qSeekSep, qLoop, qBorrow, qPadL, qPadR, qRunEnd, qBackRun, qFin, qDone, qReject]
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagDecrement {N B : Nat} :
    Config FixedGammaTargetRegisterDecrement.stateCount N B → Config stateCount N B :=
  retagDecrement
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  startConfig
def check_roundClock (zeros r : Nat) : Nat := roundClock zeros r
def check_zeroClock (zeros : Nat) : Nat := zeroClock zeros
def check_firstClock (zeros d : Nat) : Nat := firstClock zeros d
def check_loopTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros v r : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := loopTape B x w zeros v r

/-- All 33 transition rows of the fixed table, restated literally and re-derived by `rfl`,
with the resource counts and the three distinguished states.  The `qRunEnd`-on-`some false`
row is the reject hook a later fence phase will use; no theorem of this slice exercises it. -/
theorem check_table_rows :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qSeekSep, some false, .right) ∧
    machine.step qStart (some true) = (qReject, some true, .stay) ∧
    machine.step qSeekSep none = (qLoop, none, .stay) ∧
    machine.step qSeekSep (some false) = (qReject, some false, .stay) ∧
    machine.step qSeekSep (some true) = (qSeekSep, some true, .right) ∧
    machine.step qLoop none = (qBorrow, none, .left) ∧
    machine.step qLoop (some false) = (qReject, some false, .stay) ∧
    machine.step qLoop (some true) = (qReject, some true, .stay) ∧
    machine.step qBorrow none = (qFin, none, .right) ∧
    machine.step qBorrow (some false) = (qBorrow, some true, .left) ∧
    machine.step qBorrow (some true) = (qPadL, some false, .left) ∧
    machine.step qPadL none = (qPadR, none, .right) ∧
    machine.step qPadL (some false) = (qPadL, some false, .left) ∧
    machine.step qPadL (some true) = (qPadL, some true, .left) ∧
    machine.step qPadR none = (qRunEnd, none, .right) ∧
    machine.step qPadR (some false) = (qPadR, some false, .right) ∧
    machine.step qPadR (some true) = (qPadR, some true, .right) ∧
    machine.step qRunEnd none = (qBackRun, some true, .left) ∧
    machine.step qRunEnd (some false) = (qReject, some false, .stay) ∧
    machine.step qRunEnd (some true) = (qRunEnd, some true, .right) ∧
    machine.step qBackRun none = (qLoop, none, .stay) ∧
    machine.step qBackRun (some false) = (qReject, some false, .stay) ∧
    machine.step qBackRun (some true) = (qBackRun, some true, .left) ∧
    machine.step qFin none = (qDone, none, .stay) ∧
    machine.step qFin (some false) = (qReject, some false, .stay) ∧
    machine.step qFin (some true) = (qFin, some false, .right) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 11 ∧ machine.start = qStart ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 33 := by
  repeat' apply And.intro
  all_goals rfl

def check_table_and_resource_pins := @table_and_resource_pins

theorem check_per_step_budget_independent :
    ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

/-- Both terminal states absorb.  `qLoop` is not one of them, which is why no `qLoop`
endpoint below is a deadline. -/
theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

/-- The phase-local handoff in full: `startConfig` is the G2q machine retagged at G2q's
length-only `deadline (a + m)`. -/
theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w)
    let c := startConfig B x w
    c = retagDecrement p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_exact x w

/-- The three clocks and the one relation between them.  Each is an exact time out of its
own configuration; none is a deadline. -/
theorem check_clock_pins (zeros d r : Nat) :
    roundClock zeros r = 2 * zeros + 2 * r + 7 ∧ zeroClock zeros = 2 * zeros + 5 ∧
      firstClock zeros d = (d + 2) + roundClock zeros 0 :=
  clock_pins zeros d r

/-- One cell of lane per mark, and that the `r = 0` room implies the entry's and the
exhaustion's.  Sufficient and used; no footprint theorem shows any of it necessary. -/
theorem check_room_iff (a m B zeros r : Nat) :
    (a + m + 3 + zeros + r < tapeLength (pairLength a m) B ↔ zeros + 2 + r ≤ a + B) ∧
      (a + m + 3 + zeros < tapeLength (pairLength a m) B →
        a + m + 2 + zeros < tapeLength (pairLength a m) B) :=
  room_iff a m B zeros r

/-- Every cell of the countdown tape, with no hypothesis at all.  Nothing here decodes `v`,
and the marks are marks. -/
theorem check_loopTape_pins {a m B zeros v r : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ j, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 1 + j →
        loopTape B x w zeros v r i = some (v.testBit (zeros - j))) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m →
        loopTape B x w zeros v r i = none) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 2 + zeros →
        loopTape B x w zeros v r i = none) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros ≤ i.val →
        i.val < a + m + 3 + zeros + r → loopTape B x w zeros v r i = some true) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros + r ≤ i.val →
        loopTape B x w zeros v r i = none) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val < a + m →
        loopTape B x w zeros v r i = finishTape B x w zeros i) :=
  loopTape_pins x w

/-- The entry tape is G2q's endpoint tape, on a `v` matching the decremented digits.  `v` is
universally quantified: no wrapper here supplies one from a parse. -/
theorem check_loopTape_zero_eq_decTape {a m B zeros v : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j) :
    loopTape B x w zeros v 0 = decTape B x w zeros (borrow x w zeros) :=
  loopTape_zero_eq_decTape x w htag hg hv

/-- The entry out of an arbitrary configuration matching the entry ABI, restated in full:
exactly `d + 2` steps, entering `qLoop` on the separator blank and writing nothing. -/
theorem check_entry_generic {a m B zeros v d : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ b, b < d → v.testBit b = true) (hstop : v.testBit d = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a + m + 1 + zeros - d) (ht : c.tape = loopTape B x w zeros v 0) :
    let e := machine.run (d + 2) c
    e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧ e.tape = loopTape B x w zeros v 0 :=
  entry_generic x w hroom hd hlow hstop c hq hh ht

/-- One round out of an arbitrary `qLoop` configuration, restated in full: exact cost
`roundClock zeros r`, the register holding `v - 1`, one more mark in the lane.  No tag,
width, footprint or first-arrival hypothesis or conjunct occurs. -/
theorem check_round_generic {a m B zeros v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 3 + zeros + r < tapeLength (pairLength a m) B) (hpos : 1 ≤ v)
    (hhigh : ∀ b, zeros < b → v.testBit b = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros v r) :
    let e := machine.run (roundClock zeros r) c
    e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros (v - 1) (r + 1) :=
  round_generic x w hroom hpos hhigh c hq hh ht

/-- The exhaustion out of an all-`false` register, restated in full: exact cost
`zeroClock zeros`, the tape unchanged, and the endpoint persisting.  The last conjunct is
persistence, not first arrival: nothing says `qDone` is entered first at that time. -/
theorem check_exhaust_generic {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros 0 r) :
    let e := machine.run (zeroClock zeros) c
    e.state = qDone ∧ e.head.val = a + m + 2 + zeros ∧ e.tape = loopTape B x w zeros 0 r ∧
      (∀ t, zeroClock zeros ≤ t → machine.run t c = e) :=
  exhaust_generic x w hroom c hq hh ht

/-- The concrete exact run out of the phase-local `startConfig`, restated in full: the entry
at `d + 2` and the first round at `firstClock zeros d`.  No conjunct decodes the register
into a number, and no wrapper of this slice supplies the `v`. -/
theorem check_first_round {a m B zeros v : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 + zeros < tapeLength (pairLength a m) B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) (hpos : 1 ≤ v) :
    let d := borrow x w zeros
    let c0 := machine.run (d + 2) (startConfig B x w)
    let e := machine.run (firstClock zeros d) (startConfig B x w)
    c0.state = qLoop ∧ c0.head.val = a + m + 2 + zeros ∧ c0.tape = loopTape B x w zeros v 0 ∧
      e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros (v - 1) 1 ∧ (∀ b, zeros < b → (v - 1).testBit b = false) :=
  first_round x w htag hg hzeros hroom hv hhigh hpos

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's execution theorems.  `check_*_handoff`
identifies the *actual* phase-local start configuration with an explicit configuration for every
budget, using only the landed G2q endpoint theorem and G2q's own clock bound, an arithmetic
statement about clocks that executes nothing; the runs below are then reduced by kernel computation
on that configuration at `B = 0`.  Each probe is a claim about its own input.  The tag is `10110010`
and both words decode to `zeros = 4`, so the register is five digits wide.  `physWord` has `N = 17`
and a physically present payload; `virtWord` has `N = 15`, with the payload truncated after two
digits.  They exercise the two entry offsets: `physWord`'s decremented register ends in a `false`,
so `d = 0`, while `virtWord`'s ends in three `true` digits, so `d = 3`. -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def virtWord : Bitstring 7 := ![false, false, false, false, true, true, false]

/-- Rebuild a configuration from its three projections.  Stated over a configuration
*variable*, so that identifying the phase-local start configuration never has to reduce the
G2q run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) :
    c = ⟨q, ⟨k, hk⟩, T⟩ := by
  obtain ⟨cs, ch, ct⟩ := c
  cases hq; cases ht
  exact congrArg (fun h => (⟨cs, h, ct⟩ : Config K n B)) (Fin.ext hh)

theorem check_phys_handoff (B : Nat) :
    startConfig B tag physWord =
      ⟨qStart, ⟨22, by unfold tapeLength pairLength; omega⟩,
        decTape B tag physWord 4 0⟩ := by
  obtain ⟨-, hh, ht, -, -, -⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented (B := B) (zeros := 4) tag physWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  obtain ⟨-, -, -, -, -, hclamp⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented (B := B) (zeros := 4) tag physWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  have hb : borrow tag physWord 4 = 0 := by decide
  have hstart := hclamp (deadline (8 + 9))
    ((FixedGammaTargetRegisterDecrement.clock_pins (8 + 9) 4
      (borrow tag physWord 4)).2.2.2.2 (by omega) (by rw [hb]; omega))
  refine config_of_parts rfl ?_ ?_
  · change (FixedGammaTargetRegisterDecrement.machine.run (deadline (8 + 9))
      (FixedGammaTargetRegisterDecrement.startConfig B tag physWord)).head.val = 22
    rw [hstart, hh, hb]
  · change (FixedGammaTargetRegisterDecrement.machine.run (deadline (8 + 9))
      (FixedGammaTargetRegisterDecrement.startConfig B tag physWord)).tape = _
    rw [hstart, ht, hb]

theorem check_virt_handoff (B : Nat) :
    startConfig B tag virtWord =
      ⟨qStart, ⟨17, by unfold tapeLength pairLength; omega⟩,
        decTape B tag virtWord 4 3⟩ := by
  obtain ⟨-, hh, ht, -, -, -⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented (B := B) (zeros := 4) tag virtWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  obtain ⟨-, -, -, -, -, hclamp⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented (B := B) (zeros := 4) tag virtWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  have hb : borrow tag virtWord 4 = 3 := by decide
  have hstart := hclamp (deadline (8 + 7))
    ((FixedGammaTargetRegisterDecrement.clock_pins (8 + 7) 4
      (borrow tag virtWord 4)).2.2.2.2 (by omega) (by rw [hb]; omega))
  refine config_of_parts rfl ?_ ?_
  · change (FixedGammaTargetRegisterDecrement.machine.run (deadline (8 + 7))
      (FixedGammaTargetRegisterDecrement.startConfig B tag virtWord)).head.val = 17
    rw [hstart, hh, hb]
  · change (FixedGammaTargetRegisterDecrement.machine.run (deadline (8 + 7))
      (FixedGammaTargetRegisterDecrement.startConfig B tag virtWord)).tape = _
    rw [hstart, ht, hb]

/-- Both probe inputs really do satisfy the hypotheses the general theorems above assume:
each decodes to `zeros = 4` behind a matching tag, and at the probes' own budget `B = 0` each
allocates the first lane cell, which is this phase's room premise at `r = 0`.  So none of the
theorems above is a statement about an unsatisfiable hypothesis set. -/
theorem check_probe_inputs_valid :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      8 + 9 + 3 + 4 < tapeLength (pairLength 8 9) 0 ∧
      FixedContentTagGate.tagMatches (Fin.append tag virtWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag virtWord) = some 4 ∧
      8 + 7 + 3 + 4 < tapeLength (pairLength 8 7) 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The literal entry offsets and clocks the three probes execute, pinned by kernel
reduction.  The two entry costs differ by exactly the offset: `physWord` is already on the
separator's neighbour, `virtWord` walks over three set digits. -/
theorem check_clock_values :
    borrow tag physWord 4 = 0 ∧ firstClock 4 0 = 17 ∧ roundClock 4 0 = 15 ∧
      borrow tag virtWord 4 = 3 ∧ firstClock 4 3 = 20 ∧ zeroClock 4 = 13 ∧
      roundClock 4 1 = 17 :=
  ⟨by decide, rfl, rfl, by decide, rfl, rfl, rfl⟩

/-- `check_first_round`'s hypotheses are satisfiable, so it is not a statement about an empty
premise set: `physWord`'s five decremented register digits are the bits of `24` and `virtWord`'s
are the bits of `23`.  Those literals are supplied **by hand**, chosen to match the digits; no
theorem of this slice or of pnp3 produces either from a parse, which is exactly the deferred pnp4
step.  Nothing here calls the marks a target in unary. -/
theorem check_first_round_instance :
    (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) ∧ 1 ≤ 24 ∧
      (∀ j, j ≤ 4 → (23 : Nat).testBit (4 - j) = decBit tag virtWord 4 (borrow tag virtWord 4) j) ∧
      (∀ b, 4 < b → (23 : Nat).testBit b = false) ∧ 1 ≤ 23 :=
  ⟨fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega),
    by omega, fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega),
    by omega⟩

set_option maxRecDepth 1000000 in
/-- The physically present payload (`N = 17`, `zeros = 4`, entry offset `d = 0`,
`firstClock 4 0 = 17`).  G2q left the register `[18,22]` reading `t t f f f` with the head on the
cleared digit `22`, so `qSeekSep` needs one step to reach the separator blank `23` and the entry
costs two.  the `qLoop` row then steps left, so step three is `qBorrow` on `22`; the borrow sets `22, 21, 20`
and clears `19`, so step seven is `qPadL` on `18` and the register reads `t f t t t`.  `qPadL` reaches the
boundary blank `17` and turns, `qPadR` is on `18` at step nine and runs to the separator, and step
fifteen is `qRunEnd` on the empty lane cell `24`; it writes the **one mark** there and step sixteen
is `qBackRun` on `23`, which is blank, so step seventeen re-enters `qLoop` there.  Cells `17` and
`23` pin the two blanks the sweeps turn on, and `24` with `25` pin that exactly one mark was laid.  As a bit
pattern read from cell `18`, `11000` became `10111`, which nothing here claims to be a decoded
value; the marks are marks. -/
theorem check_phys_probe :
    (machine.run 1 (startConfig 0 tag physWord)).state = qSeekSep ∧
    (machine.run 1 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 2 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 2 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 3 (startConfig 0 tag physWord)).state = qBorrow ∧
    (machine.run 3 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 7 (startConfig 0 tag physWord)).state = qPadL ∧
    (machine.run 7 (startConfig 0 tag physWord)).head.val = 18 ∧
    (machine.run 9 (startConfig 0 tag physWord)).state = qPadR ∧
    (machine.run 9 (startConfig 0 tag physWord)).head.val = 18 ∧
    (machine.run 15 (startConfig 0 tag physWord)).state = qRunEnd ∧
    (machine.run 15 (startConfig 0 tag physWord)).head.val = 24 ∧
    (machine.run 16 (startConfig 0 tag physWord)).state = qBackRun ∧
    (machine.run 16 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 17 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 17 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some false ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨21, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨17, by decide⟩ = none ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨23, by decide⟩ = none ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨24, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨25, by decide⟩ = none := by
  rw [check_phys_handoff 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- The truncated payload (`N = 15`, `zeros = 4`, entry offset `d = 3`, `firstClock 4 3 = 20`).
G2q left the register `[16,20]` reading `t f t t t` with the head on the cleared digit `17`, so
`qSeekSep` walks over the three set digits `18, 19, 20` and the entry costs five, reaching the
separator blank `21`.  the `qLoop` row then steps left, so step six is `qBorrow` on `20`; that digit is
already set, so the borrow clears it at once and step seven is `qPadL` on `19`, with the register
reading `t f t t f`.
`qPadL` walks to the boundary blank `15` and turns, `qPadR` is on `16` at step twelve, step eighteen
is `qRunEnd` on the empty lane cell `22` where it writes the **one mark**, step nineteen is
`qBackRun` on the blank `21` and step twenty re-enters `qLoop` there.  Cells `22` and `23` pin that exactly one
mark was laid.  As a bit pattern read from cell `16`, `10111` became `10110`; nothing here
claims that to be a decoded value. -/
theorem check_virt_probe :
    (machine.run 1 (startConfig 0 tag virtWord)).state = qSeekSep ∧
    (machine.run 1 (startConfig 0 tag virtWord)).head.val = 18 ∧
    (machine.run 5 (startConfig 0 tag virtWord)).state = qLoop ∧
    (machine.run 5 (startConfig 0 tag virtWord)).head.val = 21 ∧
    (machine.run 6 (startConfig 0 tag virtWord)).state = qBorrow ∧
    (machine.run 6 (startConfig 0 tag virtWord)).head.val = 20 ∧
    (machine.run 7 (startConfig 0 tag virtWord)).state = qPadL ∧
    (machine.run 7 (startConfig 0 tag virtWord)).head.val = 19 ∧
    (machine.run 12 (startConfig 0 tag virtWord)).state = qPadR ∧
    (machine.run 12 (startConfig 0 tag virtWord)).head.val = 16 ∧
    (machine.run 18 (startConfig 0 tag virtWord)).state = qRunEnd ∧
    (machine.run 18 (startConfig 0 tag virtWord)).head.val = 22 ∧
    (machine.run 19 (startConfig 0 tag virtWord)).state = qBackRun ∧
    (machine.run 19 (startConfig 0 tag virtWord)).head.val = 21 ∧
    (machine.run 20 (startConfig 0 tag virtWord)).state = qLoop ∧
    (machine.run 20 (startConfig 0 tag virtWord)).head.val = 21 ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨17, by decide⟩ = some false ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨15, by decide⟩ = none ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨21, by decide⟩ = none ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 20 (startConfig 0 tag virtWord)).tape ⟨23, by decide⟩ = none := by
  rw [check_virt_handoff 0]
  repeat' apply And.intro
  all_goals decide

/-- An explicit exhausted configuration: `qLoop` on the separator blank `23` of `physWord`'s
layout, an all-`false` register `[18,22]`, and one mark already in the lane at `24`.  It is
written out here rather than reached by a run, because no theorem of this slice iterates the
round down to an empty register. -/
private def zeroConfig : Config stateCount (pairLength 8 9) 0 :=
  ⟨qLoop, ⟨23, by decide⟩, loopTape 0 tag physWord 4 0 1⟩

set_option maxRecDepth 1000000 in
/-- The exhaustion (`N = 17`, `zeros = 4`, `zeroClock 4 = 13`).  the `qLoop` row steps left, so step one is `qBorrow` on
`22`; the borrow finds only `false` digits, so it sets all five and walks off the register's left end
onto the boundary blank `17`, where step seven hands over to `qFin` on `18`.  `qFin` clears the five
digits it just set and step thirteen is `qDone` on the separator blank `23`, with all five
register cells back to `false` and the lane's one mark at `24` untouched — the exhaustion leaves the tape exactly as
it found it.  Step twenty shows `qDone` absorbing, which is persistence and not a claim that
thirteen is the first arrival. -/
theorem check_zero_probe :
    (machine.run 1 zeroConfig).state = qBorrow ∧
    (machine.run 1 zeroConfig).head.val = 22 ∧
    (machine.run 7 zeroConfig).state = qFin ∧
    (machine.run 7 zeroConfig).head.val = 18 ∧
    (machine.run 13 zeroConfig).state = qDone ∧
    (machine.run 13 zeroConfig).head.val = 23 ∧
    (machine.run 13 zeroConfig).tape ⟨18, by decide⟩ = some false ∧
    (machine.run 13 zeroConfig).tape ⟨19, by decide⟩ = some false ∧
    (machine.run 13 zeroConfig).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 13 zeroConfig).tape ⟨21, by decide⟩ = some false ∧
    (machine.run 13 zeroConfig).tape ⟨22, by decide⟩ = some false ∧
    (machine.run 13 zeroConfig).tape ⟨23, by decide⟩ = none ∧
    (machine.run 13 zeroConfig).tape ⟨24, by decide⟩ = some true ∧
    (machine.run 13 zeroConfig).tape ⟨25, by decide⟩ = none ∧
    (machine.run 20 zeroConfig).state = qDone ∧
    (machine.run 20 zeroConfig).head.val = 23 := by
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetUnaryCountdownSurfaceTests
