import Complexity.Uniform.V1.SequentialComposition
import Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration

/-!
# The decrement and the countdown as one machine (Part A G2x, concrete half)

**No new table row.**  `machine` is `FixedGammaTargetRegisterDecrement.machine.seq
FixedGammaTargetUnaryCountdown.machine`: G2q's 7-state, 21-row decrement table on the left block
`[0, 7)`, G2s-a's 11-state, 33-row countdown table on the right block `[7, 18)`, one closed 18-state,
54-row table whose every row is a row of one of those two with its target routed.  Write `N = a + m`
and `d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

The one executed handoff.  G2q's `qBorrow`-on-`some true` row targets G2q's absorbing `qDone`;
routed, it targets the countdown's `qStart` at index `7`, in that same transition: the composed
machine hands over the moment the borrow stops, on that cell, with the tape G2q leaves — exactly
the entry ABI G2s-a pins — at no cost.  Until now this handoff was a proof-level retag of G2q's run
at G2q's length-only deadline `3N`; a running composed machine switches at the borrow's **first**
arrival `decClock N zeros d`, so `handoff_exact` rests on G2q's `decrement_strict`.

`handoff_exact`: out of `startConfig` — G2q's own `startConfig` routed, hence still the retagged
*actual* G2p-f endpoint — the composed run is G2q's run up to `decClock`, is in neither composed
verdict before it, at exactly `decClock` *is* the countdown's landed `startConfig` re-embedded, and
every later step is a countdown step.  `decrement_countdown_drained`: at exactly
`composedClock N zeros d v = decClock N zeros d + fullClock zeros d v` the composed machine is in
its accept — the countdown's `qDone` — on the separator blank with the register cleared, `v` marks
laid and blanks beyond, persisting; its seven hypotheses are G2u's, and `v` is universally
quantified here.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
sixteen handoffs before this one remain proof-level identifications, no raw-input `initialConfig` is
executed, and no clock here counts a step of any earlier phase.  **First arrival** of the composed
accept: nothing says `composedClock` is the first time it is entered, since G2s-a and G2u prove no
first arrival for `qDone`.  The **fence**: both tables are uncapped, hence so is this one; an
oversized register runs `qRunEnd` off the tape and sticks, a timeout and neither verdict.  The rows
routed to the composed reject are never exercised, since G2q characterises no non-`qDone` endpoint.
Every **converse**, a **footprint** theorem and the pnp4 bridge (taken in
`ContentFixedGammaTargetDecrementCountdownBridge`).  The composed `accept` is the countdown's
phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance; no `accepts`, `AcceptsAt`, `DecidesWithin` or `UniformP` is stated. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown

open PairEncoding
open FixedGammaTargetPayloadExhaustion (totalClock finishTape payload_exhausted)
open FixedGammaTargetRegisterDecrement (decClock deadline priorDeadline borrow decBit borrow_pins
  prior_covers)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetUnaryCountdownIteration (fullClock lane_room register_drained)

/-- The composed machine: G2q's decrement, then G2s-a's countdown, as one closed table.  No row
is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedGammaTargetRegisterDecrement.machine.seq FixedGammaTargetUnaryCountdown.machine

/-- A G2q state in the composed control, at its own index. -/
def inDecrement (q : Fin FixedGammaTargetRegisterDecrement.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetRegisterDecrement.machine.seqLeft FixedGammaTargetUnaryCountdown.machine q

/-- A countdown state in the composed control, shifted past the seven G2q states. -/
def inCountdown (q : Fin FixedGammaTargetUnaryCountdown.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetRegisterDecrement.machine.seqRight FixedGammaTargetUnaryCountdown.machine q

/-- The routed target of a G2q row: `qDone` becomes the countdown's `qStart`, `qReject` the
composed reject, every working state itself. -/
def route (q : Fin FixedGammaTargetRegisterDecrement.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetRegisterDecrement.machine.seqRoute FixedGammaTargetUnaryCountdown.machine q

/-- G2q's own `startConfig` — the retagged *actual* G2p-f endpoint — in the composed control.
Still a phase-local retag of an earlier run, not `initialConfig` on a raw pair input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedGammaTargetRegisterDecrement.machine.seqEmbedRouted FixedGammaTargetUnaryCountdown.machine
    (FixedGammaTargetRegisterDecrement.startConfig B x w)

/-- Exact cost of the decrement followed by the whole countdown: G2q's first arrival plus G2u's
`fullClock`.  The handoff between them costs nothing. -/
def composedClock (N zeros d v : Nat) : Nat := decClock N zeros d + fullClock zeros d v

/-! ### Table, resource, handoff and clock pins -/

/-- The composed table, pinned: eighteen states, fifty-four rows, the distinguished states with
their indices, the block injections, the routing cases, every left row as the routed G2q row, every
right row as the countdown row, and the handoff row `qBorrow`-on-`some true` literally. -/
theorem table_and_resource_pins :
    machine.stateCount = 18 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 54 ∧
      machine.start = inDecrement FixedGammaTargetRegisterDecrement.qStart ∧
      machine.accept = inCountdown FixedGammaTargetUnaryCountdown.qDone ∧
      machine.reject = inCountdown FixedGammaTargetUnaryCountdown.qReject ∧
      machine.start.val = 0 ∧ machine.accept.val = 16 ∧ machine.reject.val = 17 ∧
      (∀ q, (inDecrement q).val = q.val) ∧ (∀ q, (inCountdown q).val = 7 + q.val) ∧
      Function.Injective inDecrement ∧ Function.Injective inCountdown ∧
      (∀ p q, inDecrement p ≠ inCountdown q) ∧
      route FixedGammaTargetRegisterDecrement.qDone =
        inCountdown FixedGammaTargetUnaryCountdown.qStart ∧
      route FixedGammaTargetRegisterDecrement.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetRegisterDecrement.qDone →
        q ≠ FixedGammaTargetRegisterDecrement.qReject → route q = inDecrement q) ∧
      (∀ q s, machine.step (inDecrement q) s =
        (route (FixedGammaTargetRegisterDecrement.machine.step q s).1,
          (FixedGammaTargetRegisterDecrement.machine.step q s).2.1,
          (FixedGammaTargetRegisterDecrement.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inCountdown q) s =
        (inCountdown (FixedGammaTargetUnaryCountdown.machine.step q s).1,
          (FixedGammaTargetUnaryCountdown.machine.step q s).2.1,
          (FixedGammaTargetUnaryCountdown.machine.step q s).2.2)) ∧
      machine.step (inDecrement FixedGammaTargetRegisterDecrement.qBorrow) (some true) =
        (inCountdown FixedGammaTargetUnaryCountdown.qStart, some false, .stay) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedGammaTargetRegisterDecrement.machine.seq_pins FixedGammaTargetUnaryCountdown.machine
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, hli, hri, hne, hra,
    hrr, hrw,
    fun q s => FixedGammaTargetRegisterDecrement.machine.seq_step_left
      FixedGammaTargetUnaryCountdown.machine q s,
    fun q s => FixedGammaTargetRegisterDecrement.machine.seq_step_right
      FixedGammaTargetUnaryCountdown.machine q s, rfl⟩

/-- The public step never consults the budget and agrees with the composed raw table everywhere. -/
theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s :=
  fun q s => FixedGammaTargetRegisterDecrement.machine.seq_step_eq_rawStep
    FixedGammaTargetUnaryCountdown.machine q s

/-- The start, pinned: G2q's `startConfig` routed into the composed control — the same head and
tape, the composed start as control.  Routing consults no decoded data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetRegisterDecrement.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetRegisterDecrement.machine.seqEmbedRouted
        FixedGammaTargetUnaryCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The composed clock: its two summands, its expansion — G2q's borrow-length clock plus G2u's
quadratic — and the length-only bound its decrement summand meets under `9 + zeros ≤ N`. -/
theorem clock_pins (N zeros d v : Nat) :
    composedClock N zeros d v = decClock N zeros d + fullClock zeros d v ∧
      composedClock N zeros d v =
        (N + zeros + d - 3) + (d + v * v + v * (2 * zeros + 6) + 2 * zeros + 7) ∧
      (9 + zeros ≤ N → d ≤ zeros →
        composedClock N zeros d v ≤ deadline N + fullClock zeros d v) := by
  have hfull : fullClock zeros d v = d + v * v + v * (2 * zeros + 6) + 2 * zeros + 7 := by
    unfold fullClock FixedGammaTargetUnaryCountdownIteration.drainClock
      FixedGammaTargetUnaryCountdownIteration.roundsClock FixedGammaTargetUnaryCountdown.zeroClock
    ring
  refine ⟨rfl, ?_, fun hN hd => ?_⟩
  · unfold composedClock decClock
    rw [hfull]
  · unfold composedClock
    have := (FixedGammaTargetRegisterDecrement.clock_pins N zeros d).2.2.2.2 hN hd
    omega

/-! ### The executed handoff -/

/-- **The handoff fires at G2q's first arrival, and it costs nothing.**  On a matching tag, a
decoded `2 ≤ zeros` and G2q's room, write `T = decClock (a+m) zeros (borrow x w zeros)`.  Out of
`startConfig`: before `T` the composed control is in neither verdict; up to and including `T` the
composed configuration is G2q's own, routed; at exactly `T` it **is** the countdown's landed
`startConfig B x w`, re-embedded — the head and tape G2s-a retags at G2q's deadline `3(a+m)`,
identified through G2q's persistence from `T` to that deadline; and every further step is a
countdown step.  The second conjunct rests on G2q's `decrement_strict` — `qDone` is entered for the
*first* time at `T`, so the routed edge fires then and not earlier — which G2q's persistence alone
would not give.  `T` occurs in the statement only; no row of either table mentions it. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) :
    let T := decClock (a + m) zeros (borrow x w zeros)
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetRegisterDecrement.machine.seqEmbedRouted
          FixedGammaTargetUnaryCountdown.machine
          (FixedGammaTargetRegisterDecrement.machine.run t
            (FixedGammaTargetRegisterDecrement.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
          FixedGammaTargetUnaryCountdown.machine
          (FixedGammaTargetUnaryCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
          FixedGammaTargetUnaryCountdown.machine
          (FixedGammaTargetUnaryCountdown.machine.run s
            (FixedGammaTargetUnaryCountdown.startConfig B x w))) := by
  intro T c
  have hN : 9 + zeros ≤ a + m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  obtain ⟨hd, hlow, hstop⟩ := borrow_pins x w zeros
  obtain ⟨-, hfh, hft, -, -, -, hprior⟩ :=
    payload_exhausted x w htag hg hzeros
      ((FixedGammaTargetRegisterDecrement.room_iff a m B zeros).2 hroom)
  have hstart : FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w) =
      FixedGammaTargetPayloadRound.machine.run (totalClock (a + m) zeros)
        (FixedGammaTargetPayloadRound.startConfig B x w) :=
    hprior _ (prior_covers hN)
  have hq : (FixedGammaTargetRegisterDecrement.startConfig B x w).state =
      FixedGammaTargetRegisterDecrement.qStart := rfl
  have hh : (FixedGammaTargetRegisterDecrement.startConfig B x w).head.val = 7 := by
    change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w)).head.val = 7
    rw [hstart]
    exact hfh
  have ht : (FixedGammaTargetRegisterDecrement.startConfig B x w).tape =
      finishTape B x w zeros := by
    change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w)).tape = finishTape B x w zeros
    rw [hstart]
    exact hft
  have hstrict := (FixedGammaTargetRegisterDecrement.decrement_strict x w htag hg hroom hd hlow
    hstop _ hq hh ht).1
  obtain ⟨hdq, -, -, -, -, hclamp⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented x w htag hg hzeros hroom
  have hleft : ∀ t, t ≤ T → machine.run t c =
      FixedGammaTargetRegisterDecrement.machine.seqEmbedRouted
        FixedGammaTargetUnaryCountdown.machine
        (FixedGammaTargetRegisterDecrement.machine.run t
          (FixedGammaTargetRegisterDecrement.startConfig B x w)) :=
    FixedGammaTargetRegisterDecrement.machine.seq_run_left
      FixedGammaTargetUnaryCountdown.machine _ hstrict
  have hcover : FixedGammaTargetRegisterDecrement.machine.run (deadline (a + m))
      (FixedGammaTargetRegisterDecrement.startConfig B x w) =
      FixedGammaTargetRegisterDecrement.machine.run T
        (FixedGammaTargetRegisterDecrement.startConfig B x w) :=
    hclamp _ ((FixedGammaTargetRegisterDecrement.clock_pins (a + m) zeros
      (borrow x w zeros)).2.2.2.2 hN hd)
  have hT : machine.run T c =
      FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
        FixedGammaTargetUnaryCountdown.machine
        (FixedGammaTargetUnaryCountdown.startConfig B x w) := by
    rw [hleft T le_rfl]
    obtain ⟨-, hcs, hch, hct⟩ := FixedGammaTargetUnaryCountdown.handoff_exact (B := B) x w
    refine Config.ext_parts ?_ ?_ ?_
    · rw [UniformTM.seqEmbedRouted_state, UniformTM.seqEmbedRight_state, hdq, hcs]
      rfl
    · rw [UniformTM.seqEmbedRouted_head, UniformTM.seqEmbedRight_head, hch, hcover]
    · rw [UniformTM.seqEmbedRouted_tape, UniformTM.seqEmbedRight_tape, hct, hcover]
  have hsuffix : ∀ s, machine.run (T + s) c =
      FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
        FixedGammaTargetUnaryCountdown.machine
        (FixedGammaTargetUnaryCountdown.machine.run s
          (FixedGammaTargetUnaryCountdown.startConfig B x w)) := by
    intro s
    rw [UniformTM.run_add, hT]
    exact FixedGammaTargetRegisterDecrement.machine.seq_run_right
      FixedGammaTargetUnaryCountdown.machine _ s
  have hTs : (machine.run T c).state = inCountdown FixedGammaTargetUnaryCountdown.qStart := by
    rw [hT]
    rfl
  have hTa : (machine.run T c).state ≠ machine.accept := by
    rw [hTs]
    decide
  have hTr : (machine.run T c).state ≠ machine.reject := by
    rw [hTs]
    decide
  exact ⟨fun t ht => machine.no_terminal_of_le c hTa hTr t (Nat.le_of_lt ht), hleft, hT, hsuffix⟩

/-- **The concrete exact run: decrement, handoff, countdown, one machine.**  Under G2u's seven
hypotheses — a matching tag, a decoded `2 ≤ zeros`, the lane cap `v ≤ F`, the room
`zeros + 2 + F ≤ a + B`, and a `v` whose digit `zeros - j` is G2q's decremented register digit `j`
with no digit above `zeros` — after exactly `composedClock (a+m) zeros d v` steps out of
`startConfig` the composed machine is in its accept (the countdown's `qDone`) on the separator blank
`a+m+2+zeros` with tape `loopTape B x w zeros 0 v`: every register cell `some false`, exactly `v`
marks in `[a+m+3+zeros, a+m+3+zeros+v)`, blanks beyond, persisting.  The first `decClock` steps are
G2q's, the routed edge fires at G2q's first arrival, and the remaining `fullClock` steps are G2u's
drain out of the configuration `handoff_exact` identifies.  `v` is universally quantified and
nothing in pnp3 supplies it; persistence is not first arrival of the composed accept; `startConfig`
still embeds every earlier phase as a retag; reaching the composed accept is neither halting on a
raw input nor language acceptance. -/
theorem decrement_countdown_drained {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := composedClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) ∧
      (∀ j, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 1 + j →
        e.tape i = some false) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros ≤ i.val →
        i.val < a + m + 3 + zeros + v → e.tape i = some true) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros + v ≤ i.val →
        e.tape i = none) := by
  have hroom2 : a + m + 2 + zeros < tapeLength (pairLength a m) B :=
    (lane_room (r := 0) (k := 0) (Nat.zero_le F) hroom).2
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg hzeros hroom2
  obtain ⟨-, -, -, he1, he2, he3, -, hreg, hmark, hlane⟩ :=
    register_drained x w htag hg hzeros hfence hroom hv hhigh
  have hE : machine.run (composedClock (a + m) zeros (borrow x w zeros) v) (startConfig B x w) =
      FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
        FixedGammaTargetUnaryCountdown.machine
        (FixedGammaTargetUnaryCountdown.machine.run (fullClock zeros (borrow x w zeros) v)
          (FixedGammaTargetUnaryCountdown.startConfig B x w)) :=
    hsuffix (fullClock zeros (borrow x w zeros) v)
  have hstate : (machine.run (composedClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_, fun j hj i hi => ?_, fun i h1 h2 => ?_, fun i h => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = composedClock (a + m) zeros (borrow x w zeros) v +
      (t - composedClock (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact hreg j hj i hi
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact hmark i h1 h2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact hlane i h

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown
