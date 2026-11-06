import Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion

/-!
# The gamma target register decrement (Part A G2q)

One **new** fixed 7-state, 21-row machine — the first new table since the G2p-d round machine,
because the gamma payload loop before it only appends digits and no row of its 22-state table
performs a borrow.  `pnp3/Docs/UniformP_V1.md` carries the long-form design notes.

Write `N = a + m`.  G2p-f halted on the tag cell `7` with the tape `finishTape B x w zeros`, whose
shape is that slice's `finishTape_pins`: the restored gamma zero field `[7, 8 + zeros)`, the blank
terminator trail, the walking terminator at `8 + zeros + termWalk N zeros`, the content, the
boundary blank at `N`, and the completed target register `[N + 1, N + 1 + zeros]` holding its
`zeros + 1` digits — on a decoded header the digits of the *encoded* integer `n + 1`, as the G2p-g
pnp4 bridge states on the parser side.  This phase subtracts one from that register, in place, by
the schoolbook borrow.  Everything is symbol-driven: no width, digit index, register address,
counter, proof term, advice or producer mark occurs in control, and every branch is decided by the
one symbol under the head.

`qSeekTerm` runs right over everything that is not `some true` — the restored gamma zeros are
`some false`, the consumed trail is blank — so the first it meets is the walking terminator;
`qSeekGap` then runs right over the non-blank content, so the first blank it meets is the boundary
cell `N`; `qRegEnd` then runs right over the register, so the first blank past it is
`N + 2 + zeros`, and one left step lands on the least significant digit `N + 1 + zeros`.  The
register's right end is found by that blank and by nothing else — the one cell of room this phase
needs beyond G2p-f's, which `room_iff` reads as `zeros + 1 ≤ a + B`.  `qBorrow` then reads a digit:
`some false` becomes `some true` and the borrow moves one cell left; `some true` becomes
`some false` and the machine halts in the absorbing `qDone` on that cell.  So the low run of `false`
digits is flipped, the `true` that stops it is cleared and every higher digit is left alone — which
is subtraction of one.  The borrow never leaves the register, because digit `0` is the bootstrap's
leading `true`: `borrow_pins` produces the stopping index from that fact and bounds it by `zeros`.

`decClock N zeros d = N + zeros + d - 3` is the exact cost at borrow length `d`, decomposed step by
step in `clock_pins`.  It is not length-only — it depends on the decoded width *and*, through `d`,
on the stored digits — while `deadline N = 3 * N` is the length-only bound it meets at every decoded
width and borrow length, in the guarded form `clock_pins` states.  `d` is not advice: `borrow`
computes it from the register digits for the statement's sake, while the machine finds the same cell
by reading symbols.  The handoff consults no decoded data either: `startConfig` retags the G2p-d
round machine at the **length-only** time `priorDeadline N = 3 * (N * N)`, and `prior_covers` proves
that time is at or past G2p-f's `totalClock N zeros` for every decoded width, so the G2p-f clamp
identifies the incoming configuration.  That bound is the length-only deadline the G2p-e/G2p-f loop
itself never stated; it bounds that loop's own phase-local clock and nothing else.

`qDone` is an internal control tag of this phase, and `startConfig` is a phase-local retag of an
*actual* prior run rather than `initialConfig` on a raw pair input: it composes no earlier clock —
`decClock` counts the steps of this phase alone, and not one of the steps `startConfig` embeds — and
reaching `qDone` is neither halting of a composed machine nor language acceptance.  This module
states no `accepts`, no `AcceptsAt` and no language membership.  What the decrement *means* is kept
apart from what it *does*: `sub_one_bits` and `decBit_sub_one` are arithmetic, saying that for an
**arbitrary** natural `v` whose bits are the incoming register's digits the endpoint digits are the
bits of `v - 1`.  No parser, codec, header or tape occurs in them, no machine here executes a
decoder, and no theorem here supplies such a `v`; composing them with the G2p-g bridge — which is
where `v = n + 1` would come from — is a pnp4 step this slice does not take.

Deferred, and deliberately not claimed: that pnp4 bridge, and with it every connection to
`contentHeader?`, to `contentInput?`, or to a parsed target; a footprint or budget theorem, so the
room premise is sufficient and used but not shown necessary; every converse — nothing says that
`qDone` at `decClock`, or any endpoint cell, implies anything about `zeros`, about `d`, or about the
incoming digits; a malformed-gamma branch; first arrival measured from the G2p-d `startConfig` of
the *previous* phase rather than from this one; the handoff of this endpoint to a next phase; and
any restoration of the gamma leading-digit convention — when the register holds exactly `2 ^ zeros`
the borrow clears digit `0`, so the decremented register need not begin with a `true`, and nothing
here re-establishes that invariant.  Clock composition, the fixed parser, advice freedom, `NP`
membership and `ContentVerifierBridge` are out of scope: infrastructure, not P-vs-NP mainline
progress. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement

open PairEncoding
open FixedGammaTargetPayloadLoopFoundation (walk registerBit)
open FixedGammaTargetPayloadExhaustion (termWalk exhaustClock totalClock finishTape)

abbrev stateCount : Nat := 7

def qStart : Fin stateCount := ⟨0, by decide⟩
def qSeekTerm : Fin stateCount := ⟨1, by decide⟩
def qSeekGap : Fin stateCount := ⟨2, by decide⟩
def qRegEnd : Fin stateCount := ⟨3, by decide⟩
def qBorrow : Fin stateCount := ⟨4, by decide⟩
def qDone : Fin stateCount := ⟨5, by decide⟩
def qReject : Fin stateCount := ⟨6, by decide⟩

/-- The complete fixed 7-state, 21-row table.  No width, digit index, register address, counter,
proof term, advice or producer mark occurs in it: every branch is decided by the symbol under the
head.  `qSeekTerm` stops on the walking terminator's `some true`, `qSeekGap` on the boundary blank,
`qRegEnd` on the blank past the register, and `qBorrow` flips a `false` digit and walks on or
clears a `true` digit and halts. -/
def raw (q : Fin stateCount) (s : Option Bool) : Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some false => (qSeekTerm, some false, .right)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some true => (qSeekGap, some true, .right)
    | s => (qSeekTerm, s, .right)
  | 2 => match s with
    | none => (qRegEnd, none, .right)
    | s => (qSeekGap, s, .right)
  | 3 => match s with
    | none => (qBorrow, none, .left)
    | s => (qRegEnd, s, .right)
  | 4 => match s with
    | some false => (qBorrow, some true, .left)
    | some true => (qDone, some false, .stay)
    | none => (qReject, none, .stay)
  | 5 => (qDone, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qDone
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Phase-local handoff ABI: only the control of the actual G2p-f configuration is
replaced. -/
def retagExhausted {N B : Nat}
    (c : Config FixedGammaTargetPayloadRound.stateCount N B) : Config stateCount N B :=
  ⟨qStart, c.head, c.tape⟩

/-- Length-only time by which the G2p-e rounds and the G2p-f finish have certainly run: the handoff
below consults no decoded width, and `prior_covers` proves this time is at or past
`totalClock N zeros` for every decoded width.  It bounds that loop's own phase-local clock and
nothing else; it counts no step of the phases `FixedGammaTargetPayloadRound.startConfig` embeds. -/
def priorDeadline (N : Nat) : Nat := 3 * (N * N)

/-- The retagged *actual* G2p-f endpoint configuration: a phase-local handoff, not a composed
raw-input execution, and the clocks below count none of its embedded steps. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagExhausted (FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
    (FixedGammaTargetPayloadRound.startConfig B x w))

/-- Exact cost of the decrement at borrow length `d`.  At a decoded width, under the `9 + zeros ≤ N`
guard `clock_pins` carries, it splits as `N - 7` steps to the boundary blank, one onto the register,
`zeros + 1` to the blank past its right end, one back onto the last digit, `d` borrows, the halt. -/
def decClock (N zeros d : Nat) : Nat := N + zeros + d - 3

/-- Public length-only deadline for **this phase only**: it omits the steps `startConfig`
embeds and is not the intended full pipeline's deadline. -/
def deadline (N : Nat) : Nat := 3 * N

/-- The borrow length below digit `j`: the number of consecutive `false` digits at the low end of
the register `[0, j]`, counted from digit `j` down.  It stops at digit `0`, made `true` by the
bootstrap. -/
private def borrowAux {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => if registerBit x w zeros (j + 1) then 0 else borrowAux x w zeros j + 1

/-- The borrow length of the whole register: the number of `false` digits at its low end.  This is
a statement-level quantity read off the digits, not advice — the machine finds the same cell by
reading tape symbols, and no row of the table mentions it. -/
def borrow {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) : Nat :=
  borrowAux x w zeros zeros

/-- Digit `j` of the decremented register at borrow length `d`: the digits above the borrow
are the incoming ones, the digit the borrow stopped on is cleared, and the `d` digits below
it are set. -/
def decBit {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros d j : Nat) : Bool :=
  if j < zeros - d then registerBit x w zeros j
  else if j = zeros - d then false
  else true

/-- The endpoint tape of the decrement: the G2p-f finish tape with the low run of `d` digits set,
the digit the borrow stopped on cleared, and every other cell — the restored gamma zero field, the
blank trail, the walking terminator, the content and the register digits above the borrow —
untouched. -/
def decTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros d : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = a + m + 1 + zeros - d then some false
  else if a + m + 1 + zeros - d < i.val ∧ i.val ≤ a + m + 1 + zeros then some true
  else finishTape B x w zeros i

/-! ### Table, resource, handoff, clock and room pins -/

/-- Every row of the fixed table, pinned literally, with the resource counts and the three
distinguished states: twenty-one rows, seven states against the three symbols. -/
theorem table_and_resource_pins :
    machine.stateCount = 7 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 21 ∧
    machine.start = qStart ∧ machine.accept = qDone ∧ machine.reject = qReject ∧
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qStart (some true) = (qReject, some true, .stay) ∧
    machine.step qSeekTerm none = (qSeekTerm, none, .right) ∧
    machine.step qSeekTerm (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qSeekTerm (some true) = (qSeekGap, some true, .right) ∧
    machine.step qSeekGap none = (qRegEnd, none, .right) ∧
    machine.step qSeekGap (some false) = (qSeekGap, some false, .right) ∧
    machine.step qSeekGap (some true) = (qSeekGap, some true, .right) ∧
    machine.step qRegEnd none = (qBorrow, none, .left) ∧
    machine.step qRegEnd (some false) = (qRegEnd, some false, .right) ∧
    machine.step qRegEnd (some true) = (qRegEnd, some true, .right) ∧
    machine.step qBorrow none = (qReject, none, .stay) ∧
    machine.step qBorrow (some false) = (qBorrow, some true, .left) ∧
    machine.step qBorrow (some true) = (qDone, some false, .stay) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The public step never consults the budget, and it agrees with the raw table on every one
of the twenty-one rows: the terminal rows of `raw` are already absorbing. -/
theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- Both terminal states absorb, so a configuration in one is a fixed point. -/
theorem endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧ (c.state = qReject → ∀ n, machine.run n c = c) :=
  ⟨fun h n => machine.run_accept c h n, fun h n => machine.run_reject c h n⟩

/-- The phase-local handoff, pinned: the start configuration *is* the G2p-d round machine
retagged at the length-only time `priorDeadline (a + m)`, with the same head and the same
tape.  Retagging replaces the control and nothing else. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w)
    let c := startConfig B x w
    c = retagExhausted p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Closed forms of this phase's clocks, its step decomposition, and the length-only bound it
meets.  The decomposition guard `9 + zeros ≤ N` is the decoded-width fact `gamma_contract`
supplies; the deadline also needs `d ≤ zeros`, which `borrow_pins` supplies. -/
theorem clock_pins (N zeros d : Nat) :
    decClock N zeros d = N + zeros + d - 3 ∧ deadline N = 3 * N ∧ priorDeadline N = 3 * (N * N) ∧
      (9 + zeros ≤ N → decClock N zeros d = (N - 7) + 1 + (zeros + 1) + 1 + d + 1) ∧
      (9 + zeros ≤ N → d ≤ zeros → decClock N zeros d ≤ deadline N) := by
  refine ⟨rfl, rfl, rfl, fun h => ?_, fun h1 h2 => ?_⟩
  · unfold decClock; omega
  · unfold decClock deadline; omega

/-- The one extra cell.  `qRegEnd` finds the register's right end by the blank past it, so this
phase allocates `N + 2 + zeros`, one cell more than G2p-f's `N + 1 + zeros`; on the budget that is
`zeros + 1 ≤ a + B` rather than `zeros ≤ a + B`.  It implies the G2p-f room premise, so the
composite run below assumes only this one.  Sufficient and used; no footprint theorem shows it
necessary. -/
theorem room_iff (a m B zeros : Nat) :
    (a + m + 2 + zeros < tapeLength (pairLength a m) B ↔ zeros + 1 ≤ a + B) ∧
      (a + m + 2 + zeros < tapeLength (pairLength a m) B →
        a + m + 1 + zeros < tapeLength (pairLength a m) B) := by
  unfold tapeLength pairLength; omega

/-- The length-only handoff really covers the G2p-e rounds and the G2p-f finish: at every decoded
width `9 + zeros ≤ N` the G2p-f exact time `totalClock N zeros` is at or before `priorDeadline N`.
This is the length-only deadline that loop never stated — a bound on its own phase-local clock,
counting no step its own `startConfig` embeds. -/
theorem prior_covers {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    totalClock N zeros ≤ priorDeadline N := by
  have hsplit : totalClock N zeros =
      (zeros - 2) * FixedGammaTargetPayloadRound.roundClock N + exhaustClock N zeros :=
    (FixedGammaTargetPayloadExhaustion.clock_pins N zeros).2.2.2.1
  have hmul : (zeros - 2) * FixedGammaTargetPayloadRound.roundClock N ≤ N * (2 * N) :=
    Nat.mul_le_mul (by omega) (by unfold FixedGammaTargetPayloadRound.roundClock; omega)
  have hsq : N * (2 * N) = 2 * (N * N) := by ring
  have hnn : 9 * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  have hfin : exhaustClock N zeros ≤ 2 * zeros + 2 := by
    unfold exhaustClock termWalk walk; omega
  unfold priorDeadline; omega

/-! ### The borrow length -/

private theorem borrowAux_pins {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : ∀ j : Nat, borrowAux x w zeros j ≤ j ∧
      (∀ i, i < borrowAux x w zeros j → registerBit x w zeros (j - i) = false) ∧
      registerBit x w zeros (j - borrowAux x w zeros j) = true := by
  intro j
  induction j with
  | zero =>
      exact ⟨le_rfl, fun i hi => absurd hi (by simp [borrowAux]),
        (FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).1⟩
  | succ j ih =>
      obtain ⟨hle, hlow, hstop⟩ := ih
      by_cases hb : registerBit x w zeros (j + 1) = true
      · have hz : borrowAux x w zeros (j + 1) = 0 := by simp [borrowAux, hb]
        exact ⟨by omega, fun i hi => by rw [hz] at hi; omega, by rw [hz, Nat.sub_zero]; exact hb⟩
      · have hfalse : registerBit x w zeros (j + 1) = false := Bool.not_eq_true _ |>.mp hb
        have hstep : borrowAux x w zeros (j + 1) = borrowAux x w zeros j + 1 := by
          simp [borrowAux, hfalse]
        refine ⟨by omega, fun i hi => ?_, ?_⟩
        · rw [hstep] at hi
          match i with
          | 0 => simpa using hfalse
          | i + 1 => rw [show j + 1 - (i + 1) = j - i by omega]; exact hlow i (by omega)
        · rw [hstep, show j + 1 - (borrowAux x w zeros j + 1) = j - borrowAux x w zeros j by
            omega]
          exact hstop

/-- **The borrow stops inside the register.**  The bound `borrow x w zeros ≤ zeros` holds because
digit `0` is the bootstrap's leading `true`, and it is why the sweep never walks off the register's
left end; the other two conjuncts — the low `borrow x w zeros` digits are `false`, the digit above
them is `true` — are the symbol-level facts the two `qBorrow` rows read. -/
theorem borrow_pins {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    borrow x w zeros ≤ zeros ∧
      (∀ i, i < borrow x w zeros → registerBit x w zeros (zeros - i) = false) ∧
      registerBit x w zeros (zeros - borrow x w zeros) = true := borrowAux_pins x w zeros zeros

/-! ### What the decrement means

Pure arithmetic about `Nat`: no machine, no tape, no parser and no codec occurs below.  `v` is an
arbitrary natural whose bits are the incoming register's digits; where that `v` comes from — the
G2p-g bridge identifies it with the encoded gamma integer `n + 1` — is a pnp4 step not taken here.
-/

private theorem low_mod {v d : Nat} (h1 : ∀ i, i < d → v.testBit i = false)
    (h2 : v.testBit d = true) : v % 2 ^ (d + 1) = 2 ^ d := by
  refine Nat.eq_of_testBit_eq (fun i => ?_); rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i d with h | h | h
  · rw [h1 i h]; simp; omega
  · subst h; rw [h2]; simp
  · simp [Nat.not_lt.2 (show d + 1 ≤ i by omega)]; omega

/-- **Subtracting one is flipping the low run.**  If `v`'s bits below `d` are `false` and its bit
`d` is `true` — exactly what the borrow rule reads off the register — then `v - 1` sets every bit
below `d`, clears bit `d`, and leaves every higher bit alone. -/
theorem sub_one_bits {v d : Nat} (h1 : ∀ i, i < d → v.testBit i = false)
    (h2 : v.testBit d = true) (j : Nat) :
    (v - 1).testBit j = if j < d then true else if j = d then false else v.testBit j := by
  have hmod := low_mod h1 h2
  have hsplit : v = 2 ^ (d + 1) * (v / 2 ^ (d + 1)) + 2 ^ d := by
    conv_lhs => rw [← Nat.div_add_mod v (2 ^ (d + 1))]
    rw [hmod]
  have hone : 1 ≤ (2 : Nat) ^ d := Nat.one_le_two_pow
  have hsub : v - 1 = 2 ^ (d + 1) * (v / 2 ^ (d + 1)) + (2 ^ d - 1) := by omega
  have hlt1 : (2 : Nat) ^ d < 2 ^ (d + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hlt2 : (2 : Nat) ^ d - 1 < 2 ^ (d + 1) := by omega
  rw [hsub, Nat.testBit_two_pow_mul_add _ hlt2]
  conv_rhs => rw [hsplit]
  rw [Nat.testBit_two_pow_mul_add _ hlt1]
  by_cases hj : j < d
  · rw [if_pos (by omega), if_pos hj, Nat.testBit_two_pow_sub_one]; simp [hj]
  · by_cases hj2 : j = d
    · subst hj2
      rw [if_pos (by omega), if_neg hj, if_pos rfl, Nat.testBit_two_pow_sub_one]; simp
    · split_ifs <;> first | rfl | omega

/-- **The endpoint digits are the digits of `v - 1`.**  On a value `v` whose bit `zeros - j` is
register digit `j` at every `j ≤ zeros`, and which has no bit above `zeros` — the two facts the
G2p-g bridge proves for the encoded gamma integer `n + 1` — the decremented register at the borrow
length `borrow x w zeros` holds the bits of `v - 1` at exactly the same positions, and `v - 1` has
no bit above `zeros` either, so those `zeros + 1` cells carry all of its digits.  Only the second
conjunct uses `hhigh`: the borrow never reaches past digit `zeros`, so the low digits of `v - 1`
do not depend on the high bits of `v`.  Nothing here parses anything: `v` is universally
quantified, and no theorem of this module supplies one. -/
theorem decBit_sub_one {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros v : Nat)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = registerBit x w zeros j)
    (hhigh : ∀ i, zeros < i → v.testBit i = false) :
    (∀ j, j ≤ zeros → (v - 1).testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j) ∧
      (∀ i, zeros < i → (v - 1).testBit i = false) := by
  obtain ⟨hd, hlow, hstop⟩ := borrow_pins x w zeros
  set d := borrow x w zeros with hdef
  have hbit : ∀ i, i ≤ zeros → v.testBit i = registerBit x w zeros (zeros - i) := by
    intro i hi
    have := hv (zeros - i) (by omega)
    rwa [show zeros - (zeros - i) = i by omega] at this
  have h1 : ∀ i, i < d → v.testBit i = false := fun i hi => by
    rw [hbit i (by omega)]; exact hlow i hi
  have h2 : v.testBit d = true := by rw [hbit d hd]; exact hstop
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · rw [sub_one_bits h1 h2]
    unfold decBit
    by_cases hc1 : j < zeros - d
    · rw [if_neg (by omega), if_neg (by omega), if_pos hc1, hbit (zeros - j) (by omega),
        show zeros - (zeros - j) = j by omega]
    · by_cases hc2 : j = zeros - d
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos hc2]
      · rw [if_pos (by omega), if_neg (by omega), if_neg hc2]
  · rw [sub_one_bits h1 h2, if_neg (by omega), if_neg (by omega)]; exact hhigh i hi

/-! ### Address-level execution kernel

The same kernel every phase of this pipeline uses: a configuration is described by its control, its
numeric head and every tape cell read through its Nat address, and one `machine.step` row is
consumed at a time.  The neighbouring modules' copies are `private`, so this is restated, not
imported. -/

private def content {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Nat → Option Bool :=
  FixedContentTagGate.physicalSymbol (Fin.append x w)

/-- Control, numeric head, and every tape cell read through its address. -/
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
        unfold moveHead; rw [dif_pos hlt]
        change c.head.val + 1 = k + 1; rw [hh]
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

/-! ### The rows the phase runs, and the incoming tape -/

private theorem row_seekTerm {r : Option Bool} (h : r ≠ some true) :
    machine.step qSeekTerm r = (qSeekTerm, r, .right) := by
  match r with
  | none | some false => rfl
  | some true => exact absurd rfl h

private theorem row_seekGap {r : Option Bool} (h : r ≠ none) :
    machine.step qSeekGap r = (qSeekGap, r, .right) := by
  match r with
  | none => exact absurd rfl h
  | some false | some true => rfl

private theorem row_regEnd {r : Option Bool} (h : r ≠ none) :
    machine.step qRegEnd r = (qRegEnd, r, .right) := by
  match r with
  | none => exact absurd rfl h
  | some false | some true => rfl

private theorem content_lt {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : k < a + m) : ∃ b, content x w k = some b := ⟨Fin.append x w ⟨k, hk⟩, by
    unfold content FixedContentTagGate.physicalSymbol; rw [dif_pos hk]⟩

private theorem content_ge {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : a + m ≤ k) : content x w k = none := by
  unfold content FixedContentTagGate.physicalSymbol; rw [dif_neg (show ¬ k < a + m by omega)]

private theorem contentTape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) :
    FixedPairContentMarkerErase.contentTape B x w i = content x w i.val := by
  unfold content FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
  split_ifs <;> rfl

/-- Tag cell `7` and the restored gamma zeros: the whole field `[7, 8 + zeros)` reads
`some false` in the incoming content, and the decoded width leaves room for the terminator
trail inside the content. -/
private theorem gamma_cells {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    9 + zeros ≤ a + m ∧ ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false := by
  obtain ⟨hlt, hterm, hzero⟩ :=
    (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hall := ((FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.1).1 htag
  have h7 := hall ⟨7, by decide⟩
  refine ⟨by omega, fun i h1 h2 => ?_⟩
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [show i = 7 by omega]; exact h7
  · have hi := hzero (i - 8) (by omega)
    rwa [show 8 + (i - 8) = i by omega] at hi

/-- Nat-addressed form of the incoming G2p-f endpoint tape. -/
private def startNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool := if 8 + zeros ≤ k ∧ k < 8 + zeros + termWalk (a + m) zeros then none
  else if k = 8 + zeros + termWalk (a + m) zeros then some true
  else if a + m + 1 ≤ k ∧ k ≤ a + m + 1 + zeros then
    some (registerBit x w zeros (k - (a + m + 1)))
  else content x w k

private theorem startNat_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) (i : Fin (tapeLength (pairLength a m) B)) :
    finishTape B x w zeros i = startNat x w zeros i.val := by
  unfold finishTape startNat; split_ifs <;> first | exact contentTape_eq x w i | rfl

/-- The terminator trail fits inside the content, so the register never collides with the
walking terminator. -/
private theorem trail_le {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    9 + zeros + termWalk N zeros ≤ N := by
  unfold termWalk walk; omega

private theorem startNat_low {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hN : 9 + zeros ≤ a + m) {k : Nat} (hk : k < 8 + zeros)
    (hfalse : ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false) (h7 : 7 ≤ k) :
    startNat x w zeros k = some false := by
  unfold startNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact hfalse k h7 hk

private theorem startNat_trail {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    {k : Nat} (h1 : 8 + zeros ≤ k) (h2 : k < 8 + zeros + termWalk (a + m) zeros) :
    startNat x w zeros k = none := by
  unfold startNat; rw [if_pos ⟨h1, h2⟩]

private theorem startNat_term {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    startNat x w zeros (8 + zeros + termWalk (a + m) zeros) = some true := by
  unfold startNat; rw [if_neg (by omega), if_pos rfl]

private theorem startNat_mid {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    {k : Nat} (h1 : 8 + zeros + termWalk (a + m) zeros < k)
    (h2 : k < a + m) : startNat x w zeros k ≠ none := by
  obtain ⟨b, hb⟩ := content_lt x w h2
  unfold startNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hb]; exact fun h => nomatch h

private theorem startNat_gap {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hN : 9 + zeros ≤ a + m) : startNat x w zeros (a + m) = none := by
  have h := trail_le (N := a + m) (zeros := zeros) hN
  unfold startNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact content_ge x w le_rfl

private theorem startNat_reg {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hN : 9 + zeros ≤ a + m) {k : Nat} (h1 : a + m + 1 ≤ k) (h2 : k ≤ a + m + 1 + zeros) :
    startNat x w zeros k = some (registerBit x w zeros (k - (a + m + 1))) := by
  have h := trail_le (N := a + m) (zeros := zeros) hN
  unfold startNat; rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]

private theorem startNat_beyond {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hN : 9 + zeros ≤ a + m) : startNat x w zeros (a + m + 2 + zeros) = none := by
  have h := trail_le (N := a + m) (zeros := zeros) hN
  unfold startNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact content_ge x w (by omega)

/-! ### The navigation segment

The head walks monotonically right from the tag cell `7` to the blank past the register and takes
one step back, writing every symbol it reads back unchanged, so the tape is constant throughout.
One induction on the step index carries the whole segment, which is what makes every intermediate
control available to `decrement_schedule` and `decrement_strict`. -/

private def decState (N zeros d s : Nat) : Fin stateCount := if s = 0 then qStart
  else if s ≤ zeros + termWalk N zeros + 1 then qSeekTerm
  else if s ≤ N - 7 then qSeekGap
  else if s ≤ N + zeros - 5 then qRegEnd
  else if s ≤ N + zeros + d - 4 then qBorrow
  else qDone

private def decHead (N zeros d s : Nat) : Nat := if s ≤ N + zeros - 5 then 7 + s
  else if s ≤ N + zeros + d - 4 then 2 * N + 2 * zeros - 3 - s
  else N + 1 + zeros - d

private theorem decState_zero (N zeros d : Nat) : decState N zeros d 0 = qStart := by
  unfold decState; rw [if_pos rfl]

private theorem decHead_zero (N zeros d : Nat) : decHead N zeros d 0 = 7 := by
  unfold decHead; rw [if_pos (Nat.zero_le _)]

private theorem decHead_nav {N zeros d s : Nat} (h : s ≤ N + zeros - 5) :
    decHead N zeros d s = 7 + s := by
  unfold decHead; rw [if_pos h]

private theorem decState_seekTerm {N zeros d s : Nat} (h1 : 1 ≤ s)
    (h2 : s ≤ zeros + termWalk N zeros + 1) : decState N zeros d s = qSeekTerm := by
  unfold decState; rw [if_neg (by omega), if_pos h2]

private theorem decState_seekGap {N zeros d s : Nat} (h1 : zeros + termWalk N zeros + 2 ≤ s)
    (h2 : s ≤ N - 7) : decState N zeros d s = qSeekGap := by
  unfold decState; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

private theorem decState_regEnd {N zeros d s : Nat} (hN : 9 + zeros ≤ N)
    (hW : 9 + zeros + termWalk N zeros ≤ N) (h1 : N - 6 ≤ s) (h2 : s ≤ N + zeros - 5) :
    decState N zeros d s = qRegEnd := by
  unfold decState; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

private theorem decState_borrow {N zeros d s : Nat} (hN : 9 + zeros ≤ N)
    (hW : 9 + zeros + termWalk N zeros ≤ N) (h1 : N + zeros - 4 ≤ s)
    (h2 : s ≤ N + zeros + d - 4) : decState N zeros d s = qBorrow := by
  unfold decState
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

private theorem decHead_borrow {N zeros d s : Nat} (h1 : N + zeros - 4 ≤ s)
    (h2 : s ≤ N + zeros + d - 4) (hN : 9 + zeros ≤ N) :
    decHead N zeros d s = 2 * N + 2 * zeros - 3 - s := by
  unfold decHead; rw [if_neg (by omega), if_pos h2]

private theorem decState_end {N zeros d : Nat} (hN : 9 + zeros ≤ N) :
    decState N zeros d (decClock N zeros d) = qDone := by
  have hw : termWalk N zeros ≤ zeros := by unfold termWalk walk; omega
  unfold decState decClock
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

private theorem decHead_end {N zeros d : Nat} (hN : 9 + zeros ≤ N) :
    decHead N zeros d (decClock N zeros d) = N + 1 + zeros - d := by
  unfold decHead decClock; rw [if_neg (by omega), if_neg (by omega)]

private theorem nav_at {a m B zeros d : Nat} {x : Bitstring a} {w : Bitstring m}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B)
    {c : Config stateCount (pairLength a m) B} (hc : At c qStart 7 (startNat x w zeros))
    (s : Nat) (hs : s ≤ a + m + zeros - 4) :
    At (machine.run s c) (decState (a + m) zeros d s) (decHead (a + m) zeros d s)
      (startNat x w zeros) := by
  obtain ⟨hN, hfalse⟩ := gamma_cells x w htag hg
  have hW := trail_le (N := a + m) (zeros := zeros) hN
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := hc
      exact ⟨hq.trans (decState_zero _ _ _).symm, hh.trans (decHead_zero _ _ _).symm, ht⟩
  | succ s ih =>
      have ih := ih (by omega)
      rcases (show s = 0 ∨ (1 ≤ s ∧ s ≤ zeros + termWalk (a + m) zeros) ∨
          s = zeros + termWalk (a + m) zeros + 1 ∨
          (zeros + termWalk (a + m) zeros + 2 ≤ s ∧ s ≤ a + m - 8) ∨
          s = a + m - 7 ∨
          (a + m - 6 ≤ s ∧ s ≤ a + m + zeros - 6) ∨
          s = a + m + zeros - 5 by omega) with h | h | h | h | h | h | h
      · -- Leave the tag cell.
        subst h; simp (disch := omega) only [decState, decHead, if_pos, if_neg] at ih ⊢
        refine stepAt_right ih rfl ?_ (by omega) (by omega) rfl (fun _ _ => rfl)
        rw [startNat_low x w hN (by omega) hfalse (by omega)]; rfl
      · -- Run right over the restored gamma zeros and the blank trail.
        simp (disch := omega) only [decState, decHead, if_pos, if_neg] at ih ⊢
        refine stepAt_right ih rfl (row_seekTerm ?_) (by omega) (by omega) rfl
          (fun _ _ => rfl)
        rcases Nat.lt_or_ge (7 + s) (8 + zeros) with hlt | hge
        · rw [startNat_low x w hN hlt hfalse (by omega)]; exact fun h => nomatch h
        · rw [startNat_trail x w hge (by omega)]; exact fun h => nomatch h
      · -- The walking terminator is the first `some true`: enter `qSeekGap`.
        subst h; simp (disch := omega) only [decState, decHead, if_pos, if_neg] at ih ⊢
        have hrd : startNat x w zeros (7 + (zeros + termWalk (a + m) zeros + 1))
            = some true := by
          rw [show 7 + (zeros + termWalk (a + m) zeros + 1)
            = 8 + zeros + termWalk (a + m) zeros by omega]
          exact startNat_term x w zeros
        exact stepAt_right ih hrd rfl (by omega) (by omega) hrd (fun _ _ => rfl)
      · -- Run right over the content cells left of the boundary blank.
        simp (disch := omega) only [decState, decHead, if_pos, if_neg] at ih ⊢
        exact stepAt_right ih rfl (row_seekGap (startNat_mid x w (by omega) (by omega)))
          (by omega) (by omega) rfl (fun _ _ => rfl)
      · -- The boundary blank at `N`: step onto the register's leading digit.
        subst h; simp (disch := omega) only [decState, decHead, if_pos, if_neg] at ih ⊢
        have hrd : startNat x w zeros (7 + (a + m - 7)) = none := by
          rw [show 7 + (a + m - 7) = a + m by omega]; exact startNat_gap x w hN
        exact stepAt_right ih hrd rfl (by omega) (by omega) hrd (fun _ _ => rfl)
      · -- Run right over the register digits.
        simp (disch := omega) only [decState, decHead, if_pos, if_neg] at ih ⊢
        refine stepAt_right ih rfl (row_regEnd ?_) (by omega) (by omega) rfl
          (fun _ _ => rfl)
        rw [startNat_reg x w hN (by omega) (by omega)]; exact fun h => nomatch h
      · -- The blank past the register: step back onto the least significant digit.
        subst h; simp (disch := omega) only [decState, decHead, if_pos, if_neg] at ih ⊢
        have hrd : startNat x w zeros (7 + (a + m + zeros - 5)) = none := by
          rw [show 7 + (a + m + zeros - 5) = a + m + 2 + zeros by omega]
          exact startNat_beyond x w hN
        exact stepAt_left ih hrd rfl (by omega) hrd (fun _ _ => rfl)

/-! ### The borrow segment

The tape changes here and nowhere else.  After `i` borrow steps the `i` least significant digits
have been set; `borrowNat` is that tape. -/

private def borrowNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros i k : Nat) :
    Option Bool := if a + m + 2 + zeros - i ≤ k ∧ k ≤ a + m + 1 + zeros then some true
  else startNat x w zeros k

private def endNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros d k : Nat) :
    Option Bool := if k = a + m + 1 + zeros - d then some false
  else if a + m + 1 + zeros - d < k ∧ k ≤ a + m + 1 + zeros then some true
  else startNat x w zeros k

private theorem decTape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros d : Nat) (i : Fin (tapeLength (pairLength a m) B)) :
    decTape B x w zeros d i = endNat x w zeros d i.val := by
  unfold decTape endNat; split_ifs <;> first | exact startNat_eq x w zeros i | rfl

private theorem borrow_at {a m B zeros d : Nat} {x : Bitstring a} {w : Bitstring m}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    {c : Config stateCount (pairLength a m) B} (hc : At c qStart 7 (startNat x w zeros))
    (i : Nat) (hi : i ≤ d) :
    At (machine.run (a + m + zeros - 4 + i) c) qBorrow (a + m + 1 + zeros - i)
      (borrowNat x w zeros i) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg; have hW := trail_le (N := a + m) (zeros := zeros) hN
  induction i with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := nav_at (d := d) htag hg hroom hc (a + m + zeros - 4) (by omega)
      refine ⟨hq.trans (decState_borrow hN hW le_rfl (by omega)),
        hh.trans ((decHead_borrow le_rfl (by omega) hN).trans (by omega)),
        fun j => (ht j).trans ?_⟩
      unfold borrowNat; rw [if_neg (by omega)]
  | succ i ih =>
      have ih := ih (by omega)
      have hcell : borrowNat x w zeros i (a + m + 1 + zeros - i) = some false := by
        unfold borrowNat
        rw [if_neg (by omega), startNat_reg x w hN (by omega) (by omega),
          show a + m + 1 + zeros - i - (a + m + 1) = zeros - i by omega]
        exact congrArg some (hlow i (by omega))
      rw [show a + m + zeros - 4 + (i + 1) = a + m + zeros - 4 + i + 1 by omega]
      exact stepAt_left ih hcell rfl (by omega)
        (by unfold borrowNat; rw [if_pos ⟨by omega, by omega⟩])
        (fun j hj => by
          unfold borrowNat
          by_cases hin : a + m + 2 + zeros - i ≤ j ∧ j ≤ a + m + 1 + zeros
          · rw [if_pos ⟨by omega, hin.2⟩, if_pos hin]
          · rw [if_neg (by omega), if_neg hin])

private theorem end_at {a m B zeros d : Nat} {x : Bitstring a} {w : Bitstring m}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    {c : Config stateCount (pairLength a m) B} (hc : At c qStart 7 (startNat x w zeros)) :
    At (machine.run (decClock (a + m) zeros d) c) qDone (a + m + 1 + zeros - d)
      (endNat x w zeros d) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  have hb := borrow_at htag hg hroom hd hlow hc d le_rfl
  have hcell : borrowNat x w zeros d (a + m + 1 + zeros - d) = some true := by
    unfold borrowNat
    rw [if_neg (by omega), startNat_reg x w hN (by omega) (by omega),
      show a + m + 1 + zeros - d - (a + m + 1) = zeros - d by omega]
    exact congrArg some hstop
  have hstep := stepAt_stay (T' := endNat x w zeros d) hb hcell rfl rfl
    (by unfold endNat; rw [if_pos rfl])
    (fun j hj => by
      unfold endNat borrowNat
      by_cases hin : a + m + 2 + zeros - d ≤ j ∧ j ≤ a + m + 1 + zeros
      · rw [if_neg (by omega), if_pos ⟨by omega, hin.2⟩, if_pos hin]
      · rw [if_neg (by omega), if_neg (by omega), if_neg hin])
  rw [show decClock (a + m) zeros d = a + m + zeros - 4 + d + 1 by unfold decClock; omega]
  exact hstep

/-- Control and head at every time of the phase, in closed form. -/
private theorem phase_at {a m B zeros d : Nat} {x : Bitstring a} {w : Bitstring m}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    {c : Config stateCount (pairLength a m) B} (hc : At c qStart 7 (startNat x w zeros))
    (s : Nat) (hs : s ≤ decClock (a + m) zeros d) :
    (machine.run s c).state = decState (a + m) zeros d s ∧
      (machine.run s c).head.val = decHead (a + m) zeros d s := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg; have hW := trail_le (N := a + m) (zeros := zeros) hN
  rcases Nat.lt_or_ge s (a + m + zeros - 4) with hlt | hge
  · have h := nav_at (d := d) htag hg hroom hc s (by omega)
    exact ⟨h.1, h.2.1⟩
  rcases Nat.lt_or_ge s (decClock (a + m) zeros d) with hlt | hge2
  · have hb : s ≤ a + m + zeros + d - 4 := by unfold decClock at hlt; omega
    have h := borrow_at htag hg hroom hd hlow hc (s - (a + m + zeros - 4)) (by omega)
    rw [show a + m + zeros - 4 + (s - (a + m + zeros - 4)) = s by omega] at h
    refine ⟨h.1.trans (decState_borrow hN hW hge hb).symm, ?_⟩
    rw [h.2.1, decHead_borrow hge hb hN]; omega
  · have h := end_at htag hg hroom hd hlow hstop hc
    rw [show s = decClock (a + m) zeros d by omega]
    exact ⟨h.1.trans (decState_end hN).symm, h.2.1.trans (decHead_end hN).symm⟩

/-! ### Public execution theorems -/

/-- **What the decrement writes, and what it leaves alone.**  Every register cell `N+1+j` holds
`decBit x w zeros d j`; below the borrow's stopping digit the incoming digits survive, the stopping
digit is cleared, the `d` digits under it are set, and every cell outside the register — the
restored gamma zero field, the blank trail, the walking terminator, the content and the boundary
blank — is the incoming G2p-f endpoint cell.  `d ≤ zeros` is a hypothesis: at
`d = borrow x w zeros` it is `borrow_pins`. -/
theorem decTape_pins {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hd : d ≤ zeros) :
    (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j →
        decTape B x w zeros d i = some (decBit x w zeros d j)) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B),
        i.val < a + m + 1 ∨ a + m + 1 + zeros < i.val →
        decTape B x w zeros d i = finishTape B x w zeros i) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 1 + zeros - d →
        decTape B x w zeros d i = some false) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 + zeros - d < i.val →
        i.val ≤ a + m + 1 + zeros → decTape B x w zeros d i = some true) ∧
      (∀ j : Nat, j < zeros - d → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j →
        decTape B x w zeros d i = some (registerBit x w zeros j)) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  refine ⟨fun j hj i hi => ?_, fun i h => ?_, fun i h => ?_, fun i h1 h2 => ?_,
    fun j hj i hi => ?_⟩
  · rw [decTape_eq, hi]
    unfold endNat decBit
    by_cases hc1 : j < zeros - d
    · rw [if_neg (by omega), if_neg (by omega), if_pos hc1,
        startNat_reg x w hN (by omega) (by omega),
        show a + m + 1 + j - (a + m + 1) = j by omega]
    · by_cases hc2 : j = zeros - d
      · rw [if_pos (by omega), if_neg (by omega), if_pos hc2]
      · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, if_neg (by omega),
          if_neg (by omega)]
  · rw [decTape_eq, startNat_eq, endNat, if_neg (by omega), if_neg (by omega)]
  · rw [decTape_eq, endNat, if_pos h]
  · rw [decTape_eq, endNat, if_neg (by omega), if_pos ⟨h1, h2⟩]
  · rw [decTape_eq, hi, endNat, if_neg (by omega), if_neg (by omega),
      startNat_reg x w hN (by omega) (by omega),
      show a + m + 1 + j - (a + m + 1) = j by omega]

/-- **The control schedule of the decrement.**  Out of an arbitrary configuration matching the
G2p-f endpoint, the head runs monotonically right from the tag cell to the blank past the register
and then monotonically left to the digit the borrow stops on, and the control is `qStart`, then
`qSeekTerm` to the walking terminator, then `qSeekGap` to the boundary blank, then `qRegEnd` to the
blank past the register, then `qBorrow` to the halt.  `qReject` is never entered, and together with
`decrement_generic` these conjuncts name the control at *every* time up to and including the halt,
so no time is left at which another state could occur. -/
theorem decrement_schedule {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart) (hh : c.head.val = 7)
    (ht : c.tape = finishTape B x w zeros) :
    (∀ t, t ≤ a + m + zeros - 5 → (machine.run t c).head.val = 7 + t) ∧
      (∀ t, a + m + zeros - 4 ≤ t → t < decClock (a + m) zeros d →
        (machine.run t c).head.val = 2 * (a + m) + 2 * zeros - 3 - t) ∧
      (machine.run 0 c).state = qStart ∧
      (∀ t, 1 ≤ t → t ≤ zeros + termWalk (a + m) zeros + 1 →
        (machine.run t c).state = qSeekTerm) ∧
      (∀ t, zeros + termWalk (a + m) zeros + 2 ≤ t → t ≤ a + m - 7 →
        (machine.run t c).state = qSeekGap) ∧
      (∀ t, a + m - 6 ≤ t → t ≤ a + m + zeros - 5 →
        (machine.run t c).state = qRegEnd) ∧
      (∀ t, a + m + zeros - 4 ≤ t → t < decClock (a + m) zeros d →
        (machine.run t c).state = qBorrow) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg; have hW := trail_le (N := a + m) (zeros := zeros) hN
  have hc : At c qStart 7 (startNat x w zeros) :=
    ⟨hq, hh, fun i => by rw [ht]; exact startNat_eq x w zeros i⟩
  have hphase := fun s hs => phase_at htag hg hroom hd hlow hstop hc s hs
  refine ⟨fun t htle => ?_, fun t h1 h2 => ?_, ?_,
    fun t h1 h2 => ?_, fun t h1 h2 => ?_, fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
  · rw [(hphase t (by unfold decClock; omega)).2, decHead_nav (by omega)]
  · rw [(hphase t (by omega)).2, decHead_borrow h1 (by unfold decClock at h2; omega) hN]
  · rw [(hphase 0 (by omega)).1, decState_zero]
  · rw [(hphase t (by unfold decClock; omega)).1, decState_seekTerm h1 h2]
  · rw [(hphase t (by unfold decClock; omega)).1, decState_seekGap h1 h2]
  · rw [(hphase t (by unfold decClock; omega)).1, decState_regEnd hN hW h1 h2]
  · rw [(hphase t (by omega)).1, decState_borrow hN hW h1 (by unfold decClock at h2; omega)]

/-- **The decrement, out of an arbitrary G2p-f endpoint configuration.**  Nine propositional
hypotheses: a matching tag, a decoded width, the room `a+m+2+zeros < tapeLength …` — one cell more
than G2p-f's, because `qRegEnd` finds the register's end by the blank past it — a borrow length `d`
with `d ≤ zeros` and the two symbol-level facts the borrow rule reads, and the three projections of
the incoming configuration.  Then the machine is after exactly `decClock (a+m) zeros d` steps, which
is `a+m+zeros+d-3`, in `qDone` on the cell `a+m+1+zeros-d` the borrow stopped on, with the whole
tape equal to `decTape B x w zeros d`.  `d` enters the statement through those three hypotheses
only; no row of the table mentions it.  `qDone` is an internal control tag of this phase: this is
neither halting of a composed machine nor language acceptance, and no converse is claimed. -/
theorem decrement_generic {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart) (hh : c.head.val = 7)
    (ht : c.tape = finishTape B x w zeros) :
    let e := machine.run (decClock (a + m) zeros d) c
    e.state = qDone ∧ e.head.val = a + m + 1 + zeros - d ∧
      e.tape = decTape B x w zeros d := by
  have hc : At c qStart 7 (startNat x w zeros) :=
    ⟨hq, hh, fun i => by rw [ht]; exact startNat_eq x w zeros i⟩
  obtain ⟨he1, he2, he3⟩ := end_at htag hg hroom hd hlow hstop hc
  exact ⟨he1, he2, funext fun i => (he3 i).trans (decTape_eq x w zeros d i).symm⟩

/-- **The decrement endpoint is a deadline, and `decClock` is its first arrival.**  Because `qDone`
absorbs, the endpoint of `decrement_generic` holds at every later time — in particular at the
length-only `deadline (a+m)` of `clock_pins` — and at every strictly earlier time the control is one
of `qStart`, `qSeekTerm`, `qSeekGap`, `qRegEnd`, `qBorrow`, so `decClock (a+m) zeros d` is the
*first* time `qDone` is entered out of this configuration.  Minimality is measured from this
configuration, not from the G2p-d `startConfig` of the previous phase. -/
theorem decrement_strict {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart) (hh : c.head.val = 7)
    (ht : c.tape = finishTape B x w zeros) :
    (∀ t, t < decClock (a + m) zeros d → (machine.run t c).state ≠ qDone) ∧
      (∀ t, decClock (a + m) zeros d ≤ t →
        machine.run t c = machine.run (decClock (a + m) zeros d) c) ∧
      (∀ t, decClock (a + m) zeros d ≤ t →
        (machine.run t c).state = qDone ∧
          (machine.run t c).head.val = a + m + 1 + zeros - d ∧
          (machine.run t c).tape = decTape B x w zeros d) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  have hc : At c qStart 7 (startNat x w zeros) :=
    ⟨hq, hh, fun i => by rw [ht]; exact startNat_eq x w zeros i⟩
  obtain ⟨hdq, hdh, hdt⟩ := decrement_generic x w htag hg hroom hd hlow hstop c hq hh ht
  have hclamp : ∀ t, decClock (a + m) zeros d ≤ t →
      machine.run t c = machine.run (decClock (a + m) zeros d) c := by
    intro t hge
    rw [show t = decClock (a + m) zeros d + (t - decClock (a + m) zeros d) by omega, machine.run_add]
    exact machine.run_accept _ hdq _
  refine ⟨fun t htlt => ?_, hclamp, fun t hge => ?_⟩
  · rw [(phase_at htag hg hroom hd hlow hstop hc t (by omega)).1]
    unfold decClock at htlt
    unfold decState; split_ifs <;> first | decide | omega
  · rw [hclamp t hge]; exact ⟨hdq, hdh, hdt⟩

/-- **The concrete exact run: the on-tape target register is decremented.**  On a matching tag, a
decoded `2 ≤ zeros` and the room `a+m+2+zeros < tapeLength (pairLength a m) B`, the phase-local
`startConfig` — the G2p-d round machine retagged at the length-only time `priorDeadline (a+m)`,
which `prior_covers` shows is at or past G2p-f's exact endpoint time — is after exactly
`decClock (a+m) zeros (borrow x w zeros)` steps of this machine in `qDone` on the stopping cell,
its tape is `decTape B x w zeros (borrow x w zeros)`, every register cell `a+m+1+j` holds
`decBit x w zeros (borrow x w zeros) j`, every cell outside the register is the incoming G2p-f
endpoint cell, and the endpoint persists at every later time.  `decClock` counts the steps of this
phase only: not one of the steps `startConfig` embeds, so it clocks no composed pipeline, and
`qDone` is an internal control tag, not language acceptance.  Nothing here decodes the register
into a number or mentions `contentHeader?`; `decBit_sub_one` says separately, and arithmetically,
that those digits are the digits of `v - 1`. -/
theorem register_decremented {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) :
    let e := machine.run (decClock (a + m) zeros (borrow x w zeros)) (startConfig B x w)
    e.state = qDone ∧ e.head.val = a + m + 1 + zeros - borrow x w zeros ∧
      e.tape = decTape B x w zeros (borrow x w zeros) ∧
      (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j →
        e.tape i = some (decBit x w zeros (borrow x w zeros) j)) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B),
        i.val < a + m + 1 ∨ a + m + 1 + zeros < i.val →
        e.tape i = finishTape B x w zeros i) ∧
      (∀ t, decClock (a + m) zeros (borrow x w zeros) ≤ t →
        machine.run t (startConfig B x w) = e) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  obtain ⟨hd, hlow, hstop⟩ := borrow_pins x w zeros
  obtain ⟨-, hfh, hft, -, -, -, hprior⟩ :=
    FixedGammaTargetPayloadExhaustion.payload_exhausted x w htag hg hzeros
      ((room_iff a m B zeros).2 hroom)
  have hstart : FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w) =
      FixedGammaTargetPayloadRound.machine.run (totalClock (a + m) zeros)
        (FixedGammaTargetPayloadRound.startConfig B x w) :=
    hprior _ (prior_covers hN)
  have hq : (startConfig B x w).state = qStart := rfl
  have hh : (startConfig B x w).head.val = 7 := by
    change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w)).head.val = 7
    rw [hstart]; exact hfh
  have ht : (startConfig B x w).tape = finishTape B x w zeros := by
    change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w)).tape = finishTape B x w zeros
    rw [hstart]; exact hft
  obtain ⟨heq, hhd, htp⟩ :=
    decrement_generic x w htag hg hroom hd hlow hstop (startConfig B x w) hq hh ht
  obtain ⟨-, hclamp, -⟩ :=
    decrement_strict x w htag hg hroom hd hlow hstop (startConfig B x w) hq hh ht
  obtain ⟨hpin1, hpin2, -, -, -⟩ := decTape_pins (B := B) x w htag hg hd
  exact ⟨heq, hhd, htp, fun j hj i hi => by rw [htp]; exact hpin1 j hj i hi,
    fun i h => by rw [htp]; exact hpin2 i h, fun t hge => hclamp t hge⟩

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement
