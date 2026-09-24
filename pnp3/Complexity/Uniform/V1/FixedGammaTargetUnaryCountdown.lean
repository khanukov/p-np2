import Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement

/-!
# The gamma target unary countdown round (Part A G2s-a)

One **new** fixed 11-state, 33-row machine, the second new table since the G2p-d round.  Write
`N = a + m`.  `pnp3/Docs/UniformP_V1.md` carries the long-form design notes.  Classification:
**Infrastructure**.  Nothing here is P-vs-NP mainline progress.

G2q left the target register `[N + 1, N + 1 + zeros]` decremented in place: the digit the borrow
stopped on cleared, the `d` digits below it set, the digits above it untouched, and the head on the
cleared cell.  This phase turns that register into a *countdown*: one round subtracts one more from
it and lays **one mark** in the tally lane past the boundary blank `N + 2 + zeros`, so after `r`
rounds the lane holds `r` marks.  The register and the lane are the only cells it writes.

**Entry ABI**, which any phase inserted before this machine must re-establish: control `qStart` on
the cleared stopping digit `some false` at `N + 1 + zeros - d`, exactly `d` cells of `some true` to
its right, the separator blank at `N + 2 + zeros`, and a blank lane beyond it.  `startConfig` meets
it by retagging the *actual* G2q run at G2q's own length-only `deadline N = 3 * N`.

Everything is symbol-driven.  `qSeekSep` runs right over the set digits to the separator blank;
`qLoop` steps left off it onto the least significant digit; `qBorrow` flips the low run of `false`
digits to `true` and clears the `true` that stops it, which is subtraction of one, or — when every
digit is `false` — walks off the register's left end onto the boundary blank and hands over to
`qFin`; `qPadL` walks left to that same boundary blank and `qPadR` right to the separator, which is
what makes the round cost independent of how long the borrow ran; `qRunEnd` runs right over the
marks already in the lane and writes one more on the first blank; `qBackRun` walks back over them to
the separator and re-enters `qLoop`.  No width, digit index, register address, mark count, clock,
counter, proof term, advice or producer mark occurs in any row: every branch is decided by the one
symbol under the head.  `lowRun` is read off the value for the statements' sake only — the machine
finds the same cell by reading symbols, and no row mentions it.

`roundClock zeros r = 2 * zeros + 2 * r + 7` is the **exact** cost of one round out of `qLoop`, and
`zeroClock zeros = 2 * zeros + 5` the exact cost of the exhaustion; `firstClock zeros d` is the
entry plus the first round.  None of them is a deadline: `qLoop` is not terminal, so a `qLoop`
endpoint holds at that time and says nothing about any other time.  Only `exhaust_generic`'s `qDone`
endpoint persists, and persistence is all that conjunct claims — no theorem here says `qDone` is
entered for the *first* time at `zeroClock zeros`, and none is proved.

Deferred, and deliberately not claimed.  The **iteration**: this slice runs one round out of an
arbitrary `qLoop` configuration and one first round out of `startConfig`, and stops there; no
theorem iterates the round, and none may until the fence below is settled.  The **fence**: the lane
is unbounded here, so a register too large for the budget runs `qRunEnd` off the end of the tape and
sticks there, which is a timeout and therefore neither verdict.  Capping the lane needs an executed
`some false` at a length-derived offset, laid by its own phase inserted between G2q and this one;
the `qRunEnd`-on-`some false` row is the hook that phase will use, and it is pinned and unexercised
until then.  The **pnp4 bridge**, and with it every connection to `contentHeader?`, to
`contentInput?` or to a parsed target: `v` is universally quantified here and no theorem of this
module supplies one.  A **footprint or budget theorem**, so every room premise is sufficient and
used but never shown necessary.  Every **converse**: nothing says that `qLoop` at `roundClock`, that
`qDone`, or that any endpoint cell implies anything about `zeros`, about `v` or about the incoming
digits.  A **malformed-gamma branch**, since G2q characterises no non-`qDone` endpoint to route.
And any restoration of the **gamma leading-digit convention**, which G2q already destroyed and which
this phase destroys further at every round.

The tally is `r` marks in a lane; calling it the target in unary would be a claim about a decoded
value, and no theorem here decodes anything.  `qDone` is an internal control tag of this phase, and
`startConfig` is a phase-local retag of an actual prior run rather than `initialConfig` on a raw
pair input: reaching `qDone` is neither halting of a composed machine nor language acceptance, and
the clocks here count the steps of this phase alone — not one of the steps `startConfig` embeds.
This module states no `accepts`, no `AcceptsAt` and no language membership.  Clock composition, the
fixed parser, advice freedom, `NP` membership and `ContentVerifierBridge` are out of scope. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown

open PairEncoding
open FixedGammaTargetPayloadLoopFoundation (registerBit walk)
open FixedGammaTargetPayloadExhaustion (termWalk finishTape)
open FixedGammaTargetRegisterDecrement (decBit decTape borrow deadline)

abbrev stateCount : Nat := 11

def qStart : Fin stateCount := ⟨0, by decide⟩
def qSeekSep : Fin stateCount := ⟨1, by decide⟩
def qLoop : Fin stateCount := ⟨2, by decide⟩
def qBorrow : Fin stateCount := ⟨3, by decide⟩
def qPadL : Fin stateCount := ⟨4, by decide⟩
def qPadR : Fin stateCount := ⟨5, by decide⟩
def qRunEnd : Fin stateCount := ⟨6, by decide⟩
def qBackRun : Fin stateCount := ⟨7, by decide⟩
def qFin : Fin stateCount := ⟨8, by decide⟩
def qDone : Fin stateCount := ⟨9, by decide⟩
def qReject : Fin stateCount := ⟨10, by decide⟩

/-- The complete fixed 11-state, 33-row table.  No width, digit index, register address, mark
count, clock, counter, proof term, advice or producer mark occurs in it: every branch is decided by
the symbol under the head.  The `qRunEnd`-on-`some false` row is the reject hook a later fence
phase will use; nothing in this slice exercises it. -/
def raw (q : Fin stateCount) (s : Option Bool) : Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some false => (qSeekSep, some false, .right)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | none => (qLoop, none, .stay)
    | some true => (qSeekSep, some true, .right)
    | s => (qReject, s, .stay)
  | 2 => match s with
    | none => (qBorrow, none, .left)
    | s => (qReject, s, .stay)
  | 3 => match s with
    | none => (qFin, none, .right)
    | some false => (qBorrow, some true, .left)
    | some true => (qPadL, some false, .left)
  | 4 => match s with
    | none => (qPadR, none, .right)
    | s => (qPadL, s, .left)
  | 5 => match s with
    | none => (qRunEnd, none, .right)
    | s => (qPadR, s, .right)
  | 6 => match s with
    | none => (qBackRun, some true, .left)
    | some true => (qRunEnd, some true, .right)
    | s => (qReject, s, .stay)
  | 7 => match s with
    | none => (qLoop, none, .stay)
    | some true => (qBackRun, some true, .left)
    | s => (qReject, s, .stay)
  | 8 => match s with
    | none => (qDone, none, .stay)
    | some true => (qFin, some false, .right)
    | s => (qReject, s, .stay)
  | 9 => (qDone, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qDone
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Phase-local handoff ABI: only the control of the actual G2q configuration is replaced.  The
retag is unconditional — G2q characterises no non-`qDone` endpoint, so there is nothing to guard
against and nothing this could route. -/
def retagDecrement {N B : Nat}
    (c : Config FixedGammaTargetRegisterDecrement.stateCount N B) : Config stateCount N B :=
  ⟨qStart, c.head, c.tape⟩

/-- The retagged *actual* G2q endpoint configuration, taken at G2q's own length-only
`deadline (a + m)`: a phase-local handoff, not a composed raw-input execution, and the clocks below
count none of its embedded steps. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagDecrement (FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
    (FixedGammaTargetRegisterDecrement.startConfig B x w))

/-- Exact cost of one round out of `qLoop` at `r` marks already laid.  It does not depend on how
long the borrow ran: `qPadL` and `qPadR` pad the sweep back out to the full register either way. -/
def roundClock (zeros r : Nat) : Nat := 2 * zeros + 2 * r + 7

/-- Exact cost of the exhaustion out of `qLoop` on an all-`false` register. -/
def zeroClock (zeros : Nat) : Nat := 2 * zeros + 5

/-- Exact cost of the entry plus the first round out of it, at entry offset `d`. -/
def firstClock (zeros d : Nat) : Nat := 2 * zeros + d + 9

/-- The tape of the countdown: the G2q/G2p-f content below the boundary blank `N`, the register
`[N + 1, N + 1 + zeros]` holding the `zeros + 1` digits of `v` with digit `zeros - j` at cell
`N + 1 + j`, the separator blank at `N + 2 + zeros`, `r` marks in the lane
`[N + 3 + zeros, N + 3 + zeros + r)`, and blanks beyond.  `v` is an arbitrary natural: nothing here
decodes it, and the `r` marks are marks, not a value in unary. -/
def loopTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros v r : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val < a + m then finishTape B x w zeros i
  else if i.val = a + m then none
  else if i.val ≤ a + m + 1 + zeros then some (v.testBit (a + m + 1 + zeros - i.val))
  else if a + m + 3 + zeros ≤ i.val ∧ i.val < a + m + 3 + zeros + r then some true
  else none

/-! ### Table, resource, handoff, clock and room pins -/

/-- Every row of the fixed table, pinned literally, with the resource counts and the three
distinguished states: thirty-three rows, eleven states against the three symbols. -/
theorem table_and_resource_pins :
    machine.stateCount = 11 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 33 ∧
    machine.start = qStart ∧ machine.accept = qDone ∧ machine.reject = qReject ∧
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
    machine.step qReject (some true) = (qReject, some true, .stay) := by
  repeat' apply And.intro
  all_goals rfl

/-- The public step never consults the budget, and it agrees with the raw table on every one of the
thirty-three rows: the terminal rows of `raw` are already absorbing. -/
theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- Both terminal states absorb, so a configuration in one is a fixed point.  `qLoop` is not among
them, which is why no `qLoop` endpoint below is a deadline. -/
theorem endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧ (c.state = qReject → ∀ n, machine.run n c = c) :=
  ⟨fun h n => machine.run_accept c h n, fun h n => machine.run_reject c h n⟩

/-- The phase-local handoff, pinned: the start configuration *is* the G2q machine retagged at G2q's
length-only `deadline (a + m)`, with the same head and the same tape.  Retagging replaces the
control and nothing else. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w)
    let c := startConfig B x w
    c = retagDecrement p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Closed forms of this phase's three clocks, and the one relation between them.  Each is an exact
time out of its own configuration; none is a deadline, because `qLoop` does not absorb. -/
theorem clock_pins (zeros d r : Nat) :
    roundClock zeros r = 2 * zeros + 2 * r + 7 ∧ zeroClock zeros = 2 * zeros + 5 ∧
      firstClock zeros d = (d + 2) + roundClock zeros 0 := by
  refine ⟨rfl, rfl, ?_⟩
  unfold firstClock roundClock
  omega

/-- The lane costs one cell per mark.  `qRunEnd` writes on the first blank past `r` marks, so a
round at `r` marks allocates `N + 3 + zeros + r`; on the budget that is `zeros + 2 + r ≤ a + B`.
The `r = 0` room implies the entry's and the exhaustion's.  Sufficient and used; no footprint
theorem shows any of it necessary. -/
theorem room_iff (a m B zeros r : Nat) :
    (a + m + 3 + zeros + r < tapeLength (pairLength a m) B ↔ zeros + 2 + r ≤ a + B) ∧
      (a + m + 3 + zeros < tapeLength (pairLength a m) B →
        a + m + 2 + zeros < tapeLength (pairLength a m) B) := by
  unfold tapeLength pairLength
  omega

/-! ### The tape, read through Nat addresses

The same kernel every phase of this pipeline uses.  The head never moves left of the boundary blank
`N`, so only cells at or past `N` are ever read; the low part is carried unexamined. -/

private def lowNat {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool :=
  if h : k < tapeLength (pairLength a m) B then finishTape B x w zeros ⟨k, h⟩ else none

private def loopNat {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros v r k : Nat) : Option Bool :=
  if k < a + m then lowNat B x w zeros k
  else if k = a + m then none
  else if k ≤ a + m + 1 + zeros then some (v.testBit (a + m + 1 + zeros - k))
  else if a + m + 3 + zeros ≤ k ∧ k < a + m + 3 + zeros + r then some true
  else none

private theorem loopTape_eq {a m B zeros v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) :
    loopTape B x w zeros v r i = loopNat B x w zeros v r i.val := by
  unfold loopTape loopNat lowNat
  by_cases h : i.val < a + m
  · rw [if_pos h, if_pos h, dif_pos i.isLt]
  · rw [if_neg h, if_neg h]

private theorem loopNat_gap {a m B zeros v r : Nat} (x : Bitstring a) (w : Bitstring m) :
    loopNat B x w zeros v r (a + m) = none := by
  unfold loopNat
  rw [if_neg (by omega), if_pos rfl]

private theorem loopNat_reg {a m B zeros v r k : Nat} (x : Bitstring a) (w : Bitstring m)
    (h1 : a + m < k) (h2 : k ≤ a + m + 1 + zeros) :
    loopNat B x w zeros v r k = some (v.testBit (a + m + 1 + zeros - k)) := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]

private theorem loopNat_sep {a m B zeros v r k : Nat} (x : Bitstring a) (w : Bitstring m)
    (h1 : a + m + 1 + zeros < k) (h2 : k < a + m + 3 + zeros) :
    loopNat B x w zeros v r k = none := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem loopNat_mark {a m B zeros v r k : Nat} (x : Bitstring a) (w : Bitstring m)
    (h1 : a + m + 3 + zeros ≤ k) (h2 : k < a + m + 3 + zeros + r) :
    loopNat B x w zeros v r k = some true := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]

private theorem loopNat_blank {a m B zeros v r k : Nat} (x : Bitstring a) (w : Bitstring m)
    (h : a + m + 3 + zeros + r ≤ k) : loopNat B x w zeros v r k = none := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem loopNat_high {a m B zeros v k : Nat} (x : Bitstring a) (w : Bitstring m)
    (h : a + m + 1 + zeros < k) : loopNat B x w zeros v 0 k = none := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem loopNat_out {a m B zeros v v' r k : Nat} (x : Bitstring a) (w : Bitstring m)
    (h : k ≤ a + m ∨ a + m + 1 + zeros < k) :
    loopNat B x w zeros v r k = loopNat B x w zeros v' r k := by
  unfold loopNat
  split_ifs <;> first | rfl | omega

private theorem loopNat_step {a m B zeros v r k : Nat} (x : Bitstring a) (w : Bitstring m)
    (h : k ≠ a + m + 3 + zeros + r) :
    loopNat B x w zeros v (r + 1) k = loopNat B x w zeros v r k := by
  unfold loopNat
  split_ifs <;> first | rfl | omega

/-- **Where every cell of the countdown tape is**, with no hypothesis at all: the `zeros + 1`
register digits, the boundary blank, the separator blank, the `r` marks, the blank lane past them,
and the untouched content below `N`.  Nothing here decodes `v`, and the marks are marks. -/
theorem loopTape_pins {a m B zeros v r : Nat} (x : Bitstring a) (w : Bitstring m) :
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
        loopTape B x w zeros v r i = finishTape B x w zeros i) := by
  refine ⟨fun j hj i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, fun i h => ?_,
    fun i h => ?_⟩
  · rw [loopTape_eq, hi, loopNat_reg x w (by omega) (by omega),
      show a + m + 1 + zeros - (a + m + 1 + j) = zeros - j by omega]
  · rw [loopTape_eq, hi, loopNat_gap]
  · rw [loopTape_eq, hi]
    exact loopNat_sep x w (by omega) (by omega)
  · rw [loopTape_eq]
    exact loopNat_mark x w h1 h2
  · rw [loopTape_eq]
    exact loopNat_blank x w h
  · unfold loopTape
    rw [if_pos h]

/-! ### The incoming G2q endpoint -/

private theorem width_le {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    9 + zeros ≤ a + m := by
  have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
  omega

/-- At a decoded width the boundary cell `N` and every cell past the register are blank on the
G2p-f finish tape: the terminator trail fits inside the content, and the content stops at `N`. -/
private theorem finish_blank {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hN : 9 + zeros ≤ a + m) (i : Fin (tapeLength (pairLength a m) B))
    (h : i.val = a + m ∨ a + m + 1 + zeros < i.val) : finishTape B x w zeros i = none := by
  have hw : 9 + zeros + termWalk (a + m) zeros ≤ a + m := by
    unfold termWalk walk
    omega
  unfold finishTape FixedPairContentMarkerErase.contentTape
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

/-- **The entry tape is G2q's endpoint tape.**  On a value `v` whose digit `zeros - j` is the
decremented register digit `j` at every `j ≤ zeros` — the fact the G2r bridge proves on a decoded
header, and which nothing here supplies — the countdown tape at zero marks *is* `decTape`.  The tag
and the width enter because `decTape` falls back to the finish tape at `N` and past the register,
and only a decoded width makes those cells blank. -/
theorem loopTape_zero_eq_decTape {a m B zeros v : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j) :
    loopTape B x w zeros v 0 = decTape B x w zeros (borrow x w zeros) := by
  have hN := width_le x w hg
  have hd := (FixedGammaTargetRegisterDecrement.borrow_pins x w zeros).1
  obtain ⟨hreg, hout, -, -, -⟩ :=
    FixedGammaTargetRegisterDecrement.decTape_pins (B := B) x w htag hg hd
  funext i
  rcases Nat.lt_trichotomy i.val (a + m) with h | h | h
  · unfold loopTape
    rw [if_pos h]
    exact (hout i (Or.inl (by omega))).symm
  · rw [loopTape_eq, h, loopNat_gap, hout i (Or.inl (by omega))]
    exact (finish_blank x w hN i (Or.inl h)).symm
  · rcases Nat.lt_or_ge (a + m + 1 + zeros) i.val with h2 | h2
    · rw [loopTape_eq, loopNat_high x w h2, hout i (Or.inr h2)]
      exact (finish_blank x w hN i (Or.inr h2)).symm
    · rw [loopTape_eq, loopNat_reg x w h h2,
        hreg (i.val - (a + m + 1)) (by omega) i (by omega),
        show a + m + 1 + zeros - i.val = zeros - (i.val - (a + m + 1)) by omega]
      exact congrArg some (hv _ (by omega))

/-! ### The borrow index, read off the value

`lowRun` is a statement-level quantity: the machine finds the same cell by reading tape symbols, no
row of the table mentions it, and the recursion is structural in a fuel bound, not a search. -/

private def lowFrom (v b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if v.testBit b then 0 else lowFrom v (b + 1) n + 1

private theorem lowFrom_pins (v : Nat) : ∀ n b : Nat, lowFrom v b n ≤ n ∧
    (∀ i, i < lowFrom v b n → v.testBit (b + i) = false) ∧
    (lowFrom v b n < n → v.testBit (b + lowFrom v b n) = true) := by
  intro n
  induction n with
  | zero =>
      intro b
      exact ⟨le_rfl, fun i hi => absurd hi (by simp [lowFrom]), fun h => absurd h (by simp [lowFrom])⟩
  | succ n ih =>
      intro b
      by_cases hb : v.testBit b = true
      · have hz : lowFrom v b (n + 1) = 0 := by simp [lowFrom, hb]
        refine ⟨by omega, fun i hi => by rw [hz] at hi; omega, fun _ => ?_⟩
        rw [hz, Nat.add_zero]
        exact hb
      · have hf : v.testBit b = false := Bool.not_eq_true _ |>.mp hb
        have hs : lowFrom v b (n + 1) = lowFrom v (b + 1) n + 1 := by simp [lowFrom, hf]
        obtain ⟨hle, hlow, hstop⟩ := ih (b + 1)
        refine ⟨by omega, fun i hi => ?_, fun h => ?_⟩
        · rw [hs] at hi
          match i with
          | 0 => simpa using hf
          | i + 1 =>
              rw [show b + (i + 1) = b + 1 + i by omega]
              exact hlow i (by omega)
        · rw [hs] at h ⊢
          rw [show b + (lowFrom v (b + 1) n + 1) = b + 1 + lowFrom v (b + 1) n by omega]
          exact hstop (by omega)

private def lowRun (v zeros : Nat) : Nat := lowFrom v 0 (zeros + 1)

private theorem lowRun_pins {v zeros : Nat} (hpos : 1 ≤ v)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    lowRun v zeros ≤ zeros ∧ (∀ i, i < lowRun v zeros → v.testBit i = false) ∧
      v.testBit (lowRun v zeros) = true := by
  unfold lowRun
  obtain ⟨hle, hlow, hstop⟩ := lowFrom_pins v (zeros + 1) 0
  have hlt : lowFrom v 0 (zeros + 1) < zeros + 1 := by
    by_contra hcon
    have hv0 : v = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.zero_testBit]
      rcases Nat.lt_or_ge zeros i with h | h
      · exact hhigh i h
      · simpa using hlow i (by omega)
    omega
  exact ⟨by omega, fun i hi => by simpa using hlow i hi, by simpa using hstop hlt⟩

private theorem high_sub_one {v zeros : Nat} (hpos : 1 ≤ v)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    ∀ b, zeros < b → (v - 1).testBit b = false := by
  obtain ⟨hle, hlow, hstop⟩ := lowRun_pins hpos hhigh
  intro b hb
  rw [FixedGammaTargetRegisterDecrement.sub_one_bits hlow hstop b, if_neg (by omega),
    if_neg (by omega)]
  exact hhigh b hb

/-! ### Address-level execution kernel

A configuration is described by its control, its numeric head and every tape cell read through its
Nat address, and one `machine.step` row is consumed at a time.  The neighbouring modules' copies are
`private`, so this is restated, not imported. -/

private def At {n B : Nat} (c : Config stateCount n B) (q : Fin stateCount) (k : Nat)
    (T : Nat → Option Bool) : Prop := c.state = q ∧ c.head.val = k ∧ ∀ i, c.tape i = T i.val

private def shift (k : Nat) : Move → Nat
  | .left => k - 1
  | .stay => k
  | .right => k + 1

private theorem step_at {n B : Nat} {c : Config stateCount n B} {q q' : Fin stateCount}
    {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool} {mv : Move}
    (hc : At c q k T) (hread : T k = r) (hrow : machine.step q r = (q', s', mv))
    (hk : shift k mv = k') (hfit : mv = .right → k + 1 < tapeLength n B)
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.stepConfig c) q' k' T' := by
  obtain ⟨hq, hh, ht⟩ := hc
  have haction : machine.step c.state (c.tape c.head) = (q', s', mv) := by
    rw [hq, ht, hh, hread, hrow]
  refine ⟨?_, ?_, fun i => ?_⟩
  · change (machine.step c.state (c.tape c.head)).1 = q'
    rw [haction]
  · change (moveHead c.head (machine.step c.state (c.tape c.head)).2.2).val = k'
    rw [haction, ← hk]
    cases mv with
    | left => change c.head.val - 1 = k - 1; rw [hh]
    | stay => exact hh
    | right =>
        have hlt : c.head.val + 1 < tapeLength n B := by rw [hh]; exact hfit rfl
        unfold moveHead
        rw [dif_pos hlt]
        change c.head.val + 1 = k + 1
        rw [hh]
  · change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = T' i.val
    rw [haction]
    by_cases hi : i.val = k
    · rw [if_pos (Fin.ext (hi.trans hh.symm)), hi, hwrite]
    · rw [if_neg (fun h => hi (by rw [h, hh])), hkeep i.val hi, ht]

private theorem stepAt_right {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .right)) (hk : k + 1 = k')
    (hfit : k + 1 < tapeLength n B) (hwrite : T' k = s')
    (hkeep : ∀ i, i ≠ k → T' i = T i) : At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun _ => hfit) hwrite hkeep

private theorem stepAt_left {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .left)) (hk : k - 1 = k')
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) : At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep

private theorem stepAt_stay {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .stay)) (hk : k = k')
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) : At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep

private theorem At_time {n B : Nat} {c : Config stateCount n B} {q : Fin stateCount}
    {k k' t t' : Nat} {T : Nat → Option Bool} (h : At (machine.run t c) q k T)
    (ht : t = t') (hk : k = k') : At (machine.run t' c) q k' T := by
  subst ht; subst hk; exact h

/-- A same-symbol leftward scan: `d` steps in `q`, rewriting each read, moving left. -/
private theorem walk_left {n B : Nat} {c : Config stateCount n B} {q : Fin stateCount}
    {T : Nat → Option Bool} {t k : Nat} :
    ∀ d : Nat, d ≤ k → At (machine.run t c) q k T →
      (∀ j, k - d < j → j ≤ k → machine.step q (T j) = (q, T j, .left)) →
      At (machine.run (t + d) c) q (k - d) T := by
  intro d
  induction d with
  | zero => intro _ hc _; simpa using hc
  | succ d ih =>
      intro hd hc hrow
      have h1 : At (machine.run (t + d) c) q (k - d) T :=
        ih (by omega) hc (fun j h1 h2 => hrow j (by omega) h2)
      have h2 : At (machine.run (t + d + 1) c) q (k - d - 1) T :=
        stepAt_left h1 rfl (hrow (k - d) (by omega) (by omega)) rfl rfl (fun _ _ => rfl)
      rw [show t + (d + 1) = t + d + 1 by omega, show k - (d + 1) = k - d - 1 by omega]
      exact h2

/-- A same-symbol rightward scan: `d` steps in `q`, rewriting each read, moving right. -/
private theorem walk_right {n B : Nat} {c : Config stateCount n B} {q : Fin stateCount}
    {T : Nat → Option Bool} {t k : Nat} :
    ∀ d : Nat, At (machine.run t c) q k T →
      (∀ j, k ≤ j → j < k + d → machine.step q (T j) = (q, T j, .right)) →
      k + d < tapeLength n B →
      At (machine.run (t + d) c) q (k + d) T := by
  intro d
  induction d with
  | zero => intro hc _ _; simpa using hc
  | succ d ih =>
      intro hc hrow hfit
      have h1 : At (machine.run (t + d) c) q (k + d) T :=
        ih hc (fun j h1 h2 => hrow j h1 (by omega)) (by omega)
      have h2 : At (machine.run (t + d + 1) c) q (k + (d + 1)) T :=
        stepAt_right h1 rfl (hrow (k + d) (by omega) (by omega)) (by omega) (by omega) rfl
          (fun _ _ => rfl)
      rw [show t + (d + 1) = t + d + 1 by omega]
      exact h2

private theorem At_of {a m B zeros v r : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Config stateCount (pairLength a m) B} {q : Fin stateCount} {k : Nat}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = loopTape B x w zeros v r) :
    At c q k (loopNat B x w zeros v r) :=
  ⟨hq, hh, fun i => by rw [ht]; exact loopTape_eq x w i⟩

private theorem At_tape {a m B zeros v r : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Config stateCount (pairLength a m) B} {q : Fin stateCount} {k : Nat}
    (h : At c q k (loopNat B x w zeros v r)) :
    c.state = q ∧ c.head.val = k ∧ c.tape = loopTape B x w zeros v r :=
  ⟨h.1, h.2.1, funext fun i => (h.2.2 i).trans (loopTape_eq x w i).symm⟩

private theorem row_padL {r : Option Bool} (h : r ≠ none) :
    machine.step qPadL r = (qPadL, r, .left) := by
  match r with
  | none => exact absurd rfl h
  | some false | some true => rfl

private theorem row_padR {r : Option Bool} (h : r ≠ none) :
    machine.step qPadR r = (qPadR, r, .right) := by
  match r with
  | none => exact absurd rfl h
  | some false | some true => rfl

/-! ### The borrow segment

The tape changes in the register here and nowhere else.  After `i` borrow steps the `i` least
significant digits have been set; `mixNat` is that tape.  One induction covers both uses: the round,
where the borrow stops on the first `true` digit, and the exhaustion, where every digit is `false`
and the sweep walks off the register's left end onto the boundary blank. -/

private def mixNat {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros v r i k : Nat) : Option Bool :=
  if a + m + 2 + zeros - i ≤ k ∧ k ≤ a + m + 1 + zeros then some true
  else loopNat B x w zeros v r k

private theorem borrow_at {a m B zeros v r : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Config stateCount (pairLength a m) B}
    (hc : At c qLoop (a + m + 2 + zeros) (loopNat B x w zeros v r)) :
    ∀ i, i ≤ zeros + 1 → (∀ b, b < i → v.testBit b = false) →
      At (machine.run (i + 1) c) qBorrow (a + m + 1 + zeros - i)
        (mixNat B x w zeros v r i) := by
  intro i
  induction i with
  | zero =>
      intro _ _
      refine At_time (stepAt_left (t := 0) hc (loopNat_sep x w (by omega) (by omega)) rfl rfl
        ?_ ?_) rfl (by omega)
      · unfold mixNat
        rw [if_neg (by omega)]
        exact loopNat_sep x w (by omega) (by omega)
      · intro j hj
        unfold mixNat
        rw [if_neg (by omega)]
  | succ i ih =>
      intro hi hf
      have h := ih (by omega) (fun b hb => hf b (by omega))
      have hread : mixNat B x w zeros v r i (a + m + 1 + zeros - i) = some false := by
        unfold mixNat
        rw [if_neg (by omega), loopNat_reg x w (by omega) (by omega),
          show a + m + 1 + zeros - (a + m + 1 + zeros - i) = i by omega]
        exact congrArg some (hf i (by omega))
      refine At_time (stepAt_left h hread rfl rfl ?_ ?_) (by omega) (by omega)
      · unfold mixNat
        rw [if_pos (show a + m + 2 + zeros - (i + 1) ≤ a + m + 1 + zeros - i ∧
          a + m + 1 + zeros - i ≤ a + m + 1 + zeros from ⟨by omega, by omega⟩)]
      · intro j hj
        unfold mixNat
        by_cases hin : a + m + 2 + zeros - i ≤ j ∧ j ≤ a + m + 1 + zeros
        · rw [if_pos (show a + m + 2 + zeros - (i + 1) ≤ j ∧ j ≤ a + m + 1 + zeros
            from ⟨by omega, hin.2⟩), if_pos hin]
        · rw [if_neg (show ¬ (a + m + 2 + zeros - (i + 1) ≤ j ∧ j ≤ a + m + 1 + zeros) by omega),
            if_neg hin]

/-- Clearing the digit the borrow stopped on turns the borrow tape into the register of `v - 1`:
the set low run, the cleared stopping digit and the untouched higher digits are exactly the bits of
`v - 1`, by G2q's `sub_one_bits`. -/
private theorem clear_tape {a m B zeros v r d : Nat} (x : Bitstring a) (w : Bitstring m)
    (hd : d ≤ zeros) (hlow : ∀ i, i < d → v.testBit i = false) (hstop : v.testBit d = true)
    (j : Nat) (hj : j ≠ a + m + 1 + zeros - d) :
    loopNat B x w zeros (v - 1) r j = mixNat B x w zeros v r d j := by
  have hsub := FixedGammaTargetRegisterDecrement.sub_one_bits hlow hstop
  unfold mixNat
  rcases Nat.lt_or_ge (a + m) j with h1 | h1
  · rcases Nat.lt_or_ge (a + m + 1 + zeros) j with h2 | h2
    · rw [if_neg (show ¬ (a + m + 2 + zeros - d ≤ j ∧ j ≤ a + m + 1 + zeros) by omega)]
      exact loopNat_out x w (Or.inr h2)
    · rw [loopNat_reg x w h1 h2, hsub]
      by_cases h3 : a + m + 1 + zeros - d < j
      · rw [if_pos (show a + m + 2 + zeros - d ≤ j ∧ j ≤ a + m + 1 + zeros
          from ⟨by omega, h2⟩), if_pos (show a + m + 1 + zeros - j < d by omega)]
      · rw [if_neg (show ¬ (a + m + 2 + zeros - d ≤ j ∧ j ≤ a + m + 1 + zeros) by omega),
          loopNat_reg x w h1 h2, if_neg (show ¬ (a + m + 1 + zeros - j < d) by omega),
          if_neg (show ¬ (a + m + 1 + zeros - j = d) by omega)]
  · rw [if_neg (show ¬ (a + m + 2 + zeros - d ≤ j ∧ j ≤ a + m + 1 + zeros) by omega)]
    exact loopNat_out x w (Or.inl h1)

/-! ### The restoring segment of the exhaustion

`qFin` walks back right over the register the all-`false` borrow set, clearing every digit it reads,
so the exhaustion leaves the tape exactly as it found it. -/

private def clearNat {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros r i k : Nat) : Option Bool :=
  if a + m + 1 + i ≤ k ∧ k ≤ a + m + 1 + zeros then some true
  else loopNat B x w zeros 0 r k

private theorem mix_eq_clear {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m) :
    mixNat B x w zeros 0 r (zeros + 1) = clearNat B x w zeros r 0 := by
  funext k
  unfold mixNat clearNat
  split_ifs <;> first | rfl | omega

private theorem clear_final {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m) :
    clearNat B x w zeros r (zeros + 1) = loopNat B x w zeros 0 r := by
  funext k
  unfold clearNat
  rw [if_neg (by omega)]

private theorem clear_at {a m B zeros r t : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Config stateCount (pairLength a m) B}
    (hc : At (machine.run t c) qFin (a + m + 1) (clearNat B x w zeros r 0))
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) :
    ∀ i, i ≤ zeros + 1 →
      At (machine.run (t + i) c) qFin (a + m + 1 + i) (clearNat B x w zeros r i) := by
  intro i
  induction i with
  | zero => intro _; simpa using hc
  | succ i ih =>
      intro hi
      have h := ih (by omega)
      have hread : clearNat B x w zeros r i (a + m + 1 + i) = some true := by
        unfold clearNat
        rw [if_pos (show a + m + 1 + i ≤ a + m + 1 + i ∧ a + m + 1 + i ≤ a + m + 1 + zeros
          from ⟨le_rfl, by omega⟩)]
      refine At_time (stepAt_right h hread rfl rfl (by omega) ?_ ?_) (by omega) (by omega)
      · unfold clearNat
        rw [if_neg (show ¬ (a + m + 1 + (i + 1) ≤ a + m + 1 + i ∧
            a + m + 1 + i ≤ a + m + 1 + zeros) by omega),
          loopNat_reg x w (by omega) (by omega)]
        simp
      · intro j hj
        unfold clearNat
        by_cases hin : a + m + 1 + i ≤ j ∧ j ≤ a + m + 1 + zeros
        · rw [if_pos (show a + m + 1 + (i + 1) ≤ j ∧ j ≤ a + m + 1 + zeros
            from ⟨by omega, hin.2⟩), if_pos hin]
        · rw [if_neg (show ¬ (a + m + 1 + (i + 1) ≤ j ∧ j ≤ a + m + 1 + zeros) by omega),
            if_neg hin]

/-! ### Public execution theorems -/

/-- **The entry.**  Out of an arbitrary configuration matching the entry ABI — `qStart` on the
cleared stopping digit at `N + 1 + zeros - d`, with the `d` digits to its right set, which is what
`hlow`/`hstop` say about `v` — the machine *enters* `qLoop` on the separator blank after exactly
`d + 2` steps, writing nothing: `qSeekSep` rewrites every symbol it reads.  `d` enters the statement
through the hypotheses only; no row of the table mentions it.  `qLoop` does not absorb, so this is
an exact time, not a deadline, and no converse is claimed. -/
theorem entry_generic {a m B zeros v d : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ b, b < d → v.testBit b = true) (hstop : v.testBit d = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a + m + 1 + zeros - d) (ht : c.tape = loopTape B x w zeros v 0) :
    let e := machine.run (d + 2) c
    e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧ e.tape = loopTape B x w zeros v 0 := by
  have hc : At c qStart (a + m + 1 + zeros - d) (loopNat B x w zeros v 0) := At_of hq hh ht
  have hread : loopNat B x w zeros v 0 (a + m + 1 + zeros - d) = some false := by
    rw [loopNat_reg x w (by omega) (by omega),
      show a + m + 1 + zeros - (a + m + 1 + zeros - d) = d by omega]
    exact congrArg some hstop
  have h1 : At (machine.run 1 c) qSeekSep (a + m + 2 + zeros - d) (loopNat B x w zeros v 0) :=
    stepAt_right (t := 0) hc hread rfl (by omega) (by omega) hread (fun _ _ => rfl)
  have h2 : At (machine.run (d + 1) c) qSeekSep (a + m + 2 + zeros)
      (loopNat B x w zeros v 0) := by
    refine At_time (walk_right d h1 ?_ (by omega)) (by omega) (by omega)
    intro j hj1 hj2
    rw [loopNat_reg x w (by omega) (by omega), hlow _ (by omega)]
    rfl
  exact At_tape (At_time (stepAt_stay h2 (loopNat_sep x w (by omega) (by omega)) rfl rfl
    (loopNat_sep x w (by omega) (by omega)) (fun _ _ => rfl)) rfl rfl)

/-- **One round.**  Out of an arbitrary `qLoop` configuration on the separator blank with a register
holding a positive `v` that has no digit above `zeros`, the machine is after exactly
`roundClock zeros r = 2*zeros + 2*r + 7` steps back in `qLoop` on the same cell, with the register
holding `v - 1` and **one more mark** in the lane.  The cost does not depend on how long the borrow
ran, because `qPadL` and `qPadR` pad the sweep back out to the full register; that is what makes the
round clock closed-form.  No tag, width, footprint or first-arrival hypothesis or conjunct occurs:
the round never reads a cell left of `N`, and `loopTape` places the blank at `N` explicitly.
`qLoop` does not absorb, so this is an exact time and not a deadline, and nothing here iterates
it. -/
theorem round_generic {a m B zeros v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 3 + zeros + r < tapeLength (pairLength a m) B) (hpos : 1 ≤ v)
    (hhigh : ∀ b, zeros < b → v.testBit b = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros v r) :
    let e := machine.run (roundClock zeros r) c
    e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros (v - 1) (r + 1) := by
  obtain ⟨hd, hlow, hstop⟩ := lowRun_pins hpos hhigh
  set d := lowRun v zeros with hdef
  have hc : At c qLoop (a + m + 2 + zeros) (loopNat B x w zeros v r) := At_of hq hh ht
  have hB := borrow_at hc d (by omega) hlow
  have hread : mixNat B x w zeros v r d (a + m + 1 + zeros - d) = some true := by
    unfold mixNat
    rw [if_neg (by omega), loopNat_reg x w (by omega) (by omega),
      show a + m + 1 + zeros - (a + m + 1 + zeros - d) = d by omega]
    exact congrArg some hstop
  have hC : At (machine.run (d + 2) c) qPadL (a + m + zeros - d)
      (loopNat B x w zeros (v - 1) r) := by
    refine stepAt_left hB hread rfl (by omega) ?_ (fun j hj => clear_tape x w hd hlow hstop j hj)
    rw [loopNat_reg x w (by omega) (by omega),
      show a + m + 1 + zeros - (a + m + 1 + zeros - d) = d by omega,
      FixedGammaTargetRegisterDecrement.sub_one_bits hlow hstop d,
      if_neg (by omega), if_pos rfl]
  have hD : At (machine.run (zeros + 2) c) qPadL (a + m) (loopNat B x w zeros (v - 1) r) := by
    refine At_time (walk_left (zeros - d) (by omega) hC ?_) (by omega) (by omega)
    intro j h1 h2
    exact row_padL (by rw [loopNat_reg x w (by omega) (by omega)]; exact fun h => nomatch h)
  have hE : At (machine.run (zeros + 3) c) qPadR (a + m + 1) (loopNat B x w zeros (v - 1) r) :=
    stepAt_right hD (loopNat_gap x w) rfl rfl (by omega) (loopNat_gap x w) (fun _ _ => rfl)
  have hF : At (machine.run (2 * zeros + 4) c) qPadR (a + m + 2 + zeros)
      (loopNat B x w zeros (v - 1) r) := by
    refine At_time (walk_right (zeros + 1) hE ?_ (by omega)) (by omega) (by omega)
    intro j h1 h2
    exact row_padR (by rw [loopNat_reg x w (by omega) (by omega)]; exact fun h => nomatch h)
  have hG : At (machine.run (2 * zeros + 5) c) qRunEnd (a + m + 3 + zeros)
      (loopNat B x w zeros (v - 1) r) :=
    stepAt_right hF (loopNat_sep x w (by omega) (by omega)) rfl (by omega) (by omega)
      (loopNat_sep x w (by omega) (by omega)) (fun _ _ => rfl)
  have hH : At (machine.run (2 * zeros + 5 + r) c) qRunEnd (a + m + 3 + zeros + r)
      (loopNat B x w zeros (v - 1) r) := by
    refine walk_right r hG ?_ (by omega)
    intro j h1 h2
    rw [loopNat_mark x w h1 h2]
    rfl
  have hI : At (machine.run (2 * zeros + 5 + r + 1) c) qBackRun (a + m + 2 + zeros + r)
      (loopNat B x w zeros (v - 1) (r + 1)) :=
    stepAt_left hH (loopNat_blank x w le_rfl) rfl (by omega)
      (loopNat_mark x w (by omega) (by omega)) (fun j hj => loopNat_step x w hj)
  have hJ : At (machine.run (2 * zeros + 2 * r + 6) c) qBackRun (a + m + 2 + zeros)
      (loopNat B x w zeros (v - 1) (r + 1)) := by
    refine At_time (walk_left r (by omega) hI ?_) (by omega) (by omega)
    intro j h1 h2
    rw [loopNat_mark x w (by omega) (by omega)]
    rfl
  refine At_tape (At_time (stepAt_stay hJ (loopNat_sep x w (by omega) (by omega)) rfl rfl
    (loopNat_sep x w (by omega) (by omega)) (fun _ _ => rfl)) ?_ rfl)
  unfold roundClock
  omega

/-- **The exhaustion.**  Out of a `qLoop` configuration whose register is all `false`, the borrow
walks off the register's left end onto the boundary blank, `qFin` walks back clearing every digit it
set, and after exactly `zeroClock zeros = 2*zeros + 5` steps the machine is in `qDone` on the
separator blank with the tape **unchanged**, marks and all.  The last conjunct is persistence, not
first arrival: `qDone` absorbs, so the endpoint holds at every later time, and no theorem here says
`qDone` is entered for the first time at `zeroClock zeros`.  `qDone` is an internal control tag of
this phase, not language acceptance. -/
theorem exhaust_generic {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros 0 r) :
    let e := machine.run (zeroClock zeros) c
    e.state = qDone ∧ e.head.val = a + m + 2 + zeros ∧ e.tape = loopTape B x w zeros 0 r ∧
      (∀ t, zeroClock zeros ≤ t → machine.run t c = e) := by
  have hc : At c qLoop (a + m + 2 + zeros) (loopNat B x w zeros 0 r) := At_of hq hh ht
  have hB : At (machine.run (zeros + 2) c) qBorrow (a + m) (clearNat B x w zeros r 0) := by
    rw [← mix_eq_clear]
    exact At_time (borrow_at hc (zeros + 1) le_rfl (fun b _ => by simp)) rfl (by omega)
  have hread : clearNat B x w zeros r 0 (a + m) = none := by
    unfold clearNat
    rw [if_neg (by omega)]
    exact loopNat_gap x w
  have hC : At (machine.run (zeros + 3) c) qFin (a + m + 1) (clearNat B x w zeros r 0) :=
    stepAt_right hB hread rfl rfl (by omega) hread (fun _ _ => rfl)
  have hD : At (machine.run (2 * zeros + 4) c) qFin (a + m + 2 + zeros)
      (loopNat B x w zeros 0 r) := by
    have h := clear_at hC hroom (zeros + 1) le_rfl
    rw [clear_final] at h
    exact At_time h (by omega) (by omega)
  have hE : At (machine.run (zeroClock zeros) c) qDone (a + m + 2 + zeros)
      (loopNat B x w zeros 0 r) := by
    refine At_time (stepAt_stay hD (loopNat_sep x w (by omega) (by omega)) rfl rfl
      (loopNat_sep x w (by omega) (by omega)) (fun _ _ => rfl)) ?_ rfl
    unfold zeroClock
    omega
  obtain ⟨h1, h2, h3⟩ := At_tape hE
  refine ⟨h1, h2, h3, fun t hts => ?_⟩
  rw [show t = zeroClock zeros + (t - zeroClock zeros) by omega, machine.run_add]
  exact machine.run_accept _ h1 _

/-- **The concrete exact run: the entry and the first round out of `startConfig`.**  On a matching
tag, a decoded `2 ≤ zeros`, the room `a+m+3+zeros < tapeLength …` and a positive `v` whose digit
`zeros - j` is G2q's decremented register digit `j` at every `j ≤ zeros` and which has no digit
above `zeros`, the phase-local `startConfig` — the G2q machine retagged at G2q's length-only
`deadline (a+m)`, which G2q's own `clock_pins` shows is at or past its exact endpoint time — enters
`qLoop` on the separator blank after exactly `d + 2` steps with the register holding `v`, and after
exactly `firstClock zeros d = 2*zeros + d + 9` steps is back in `qLoop` there with the register
holding `v - 1`, **one mark** in the lane, and `v - 1` still free of digits above `zeros`.  Nothing
here supplies `v`: it is universally quantified, and producing one from a parsed target is the
deferred pnp4 step.  The clocks count the steps of this phase alone, and neither endpoint is a
deadline. -/
theorem first_round {a m B zeros v : Nat} (x : Bitstring a) (w : Bitstring m)
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
      e.tape = loopTape B x w zeros (v - 1) 1 ∧ (∀ b, zeros < b → (v - 1).testBit b = false) := by
  have hN := width_le x w hg
  have hroom2 : a + m + 2 + zeros < tapeLength (pairLength a m) B := (room_iff a m B zeros 0).2 hroom
  have hd := (FixedGammaTargetRegisterDecrement.borrow_pins x w zeros).1
  obtain ⟨-, hh0, ht0, -, -, hclamp⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented x w htag hg hzeros hroom2
  have hcover : FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w) =
      FixedGammaTargetRegisterDecrement.machine.run
        (FixedGammaTargetRegisterDecrement.decClock (a + m) zeros (borrow x w zeros))
        (FixedGammaTargetRegisterDecrement.startConfig B x w) :=
    hclamp _ ((FixedGammaTargetRegisterDecrement.clock_pins (a + m) zeros
      (borrow x w zeros)).2.2.2.2 hN hd)
  have hcq : (startConfig B x w).state = qStart := rfl
  have hch : (startConfig B x w).head.val = a + m + 1 + zeros - borrow x w zeros := by
    change (FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w)).head.val = _
    rw [hcover]
    exact hh0
  have hct : (startConfig B x w).tape = loopTape B x w zeros v 0 := by
    change (FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w)).tape = _
    rw [hcover, ht0]
    exact (loopTape_zero_eq_decTape x w htag hg hv).symm
  have hlowb : ∀ b, b < borrow x w zeros → v.testBit b = true := by
    intro b hb
    have h := hv (zeros - b) (by omega)
    rw [show zeros - (zeros - b) = b by omega] at h
    rw [h]
    unfold decBit
    rw [if_neg (by omega), if_neg (by omega)]
  have hstopb : v.testBit (borrow x w zeros) = false := by
    have h := hv (zeros - borrow x w zeros) (by omega)
    rw [show zeros - (zeros - borrow x w zeros) = borrow x w zeros by omega] at h
    rw [h]
    unfold decBit
    rw [if_neg (by omega), if_pos rfl]
  obtain ⟨he1, he2, he3⟩ :=
    entry_generic (v := v) x w hroom2 hd hlowb hstopb (startConfig B x w) hcq hch hct
  obtain ⟨hr1, hr2, hr3⟩ := round_generic (v := v) (r := 0) x w (by omega) hpos hhigh
    (machine.run (borrow x w zeros + 2) (startConfig B x w)) he1 he2 he3
  have htime : firstClock zeros (borrow x w zeros)
      = (borrow x w zeros + 2) + roundClock zeros 0 := by
    unfold firstClock roundClock
    omega
  refine ⟨he1, he2, he3, ?_, ?_, ?_, high_sub_one hpos hhigh⟩ <;>
    rw [htime, machine.run_add]
  · exact hr1
  · exact hr2
  · exact hr3

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown
