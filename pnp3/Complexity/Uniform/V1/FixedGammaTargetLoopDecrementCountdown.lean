import Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown

/-!
# The payload loop, the decrement and the countdown as one machine (Part A G2y)

**No new table row.**  `machine` is `FixedGammaTargetPayloadRound.machine.seq
FixedGammaTargetDecrementCountdown.machine`: G2p-d's 22-state, 66-row payload-round table on the
left block `[0, 22)`, G2x's landed 18-state composite on the right block `[22, 40)` — inside it
G2q's seven decrement states at `[22, 29)` and G2s-a's eleven countdown states at `[29, 40)` — one
closed 40-state, 120-row table whose every row is a row of one of those three tables with its
target routed.  Write `N = a + m` and `d = borrow x w zeros`.  `pnp3/Docs/UniformP_V1.md` carries
the long-form notes.  Classification (AGENTS.md): **Infrastructure**.

**Two executed handoffs.**  H16 is the payload loop's `qFin`-on-`some false` row at state index
`19`: unrouted it targets the round machine's own absorbing `qDone`; routed, it targets the tail's
start — G2q's `qStart` at composed index `22` — in that same transition, on that cell, with the
tape the loop leaves, at no cost.  H17 is G2x's `qBorrow`-on-`some true` row at composed index `26`,
inherited unchanged and re-derived here through the right-block row equation.  Until now H16 was a
proof-level retag of the round machine's run at G2q's length-only deadline `priorDeadline N`; a
running composed machine switches at the loop's **first arrival** `totalClock N zeros`, so
`handoff_exact` rests on `loop_strict`.

`loop_strict` is the enabling fact this slice adds, and it is assembled from landed theorems only.
At `loopClock N zeros` the round machine sits in the non-absorbing `qLoop` (G2p-e's
`register_complete`), so `no_terminal_of_le` excludes both of its verdicts at every earlier time;
above that time `run_add` reduces the question to the finish out of exactly the `r = zeros`
configuration `register_complete` describes, and G2p-f's `exhaust_strict` excludes `qDone` before
`exhaustClock N zeros`.  No new trace, schedule or table row is proved here.

`handoff_exact`: out of `startConfig` — the round machine's own `startConfig`, hence still the
retagged *actual* G2p-d foundation endpoint — the composed run is the round machine's run up to
`T = totalClock N zeros`, is in neither composed verdict before `T`, at exactly `T` **is** G2x's
landed `startConfig B x w` re-embedded (its head and whole tape, identified through the round
machine's persistence from `T` to `priorDeadline N`), and every later step is a G2x step.
`loop_decrement_countdown_drained`: at exactly
`chainClock N zeros d v = totalClock N zeros + composedClock N zeros d v` the composed machine is in
its accept — the countdown's `qDone` — on the separator blank `N + 2 + zeros` with the register
cleared, `v` marks laid and blanks beyond, persisting.  Its **seven** hypotheses are exactly G2u's;
the decrement's room and the loop's weaker room are *derived* inside the proof from the countdown's
lane room, not assumed.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the
fifteen handoffs before H16 remain proof-level identifications, no raw-input `initialConfig` is
executed, and no clock here counts a step of any earlier phase.  **First arrival** of the composed
accept: nothing says `chainClock` is the first time it is entered, since G2s-a and G2u prove no
first arrival for `qDone`; the first arrival proved here is the *loop's*, inside the left block.
The **fence**: all three tables are uncapped, hence so is this one; an oversized register runs
`qRunEnd` off the tape and sticks, a timeout and neither verdict.  The rows routed to the composed
reject are pinned but not exercised here: this slice states no rejecting run and composes no
malformed-gamma rejection, although the round machine's `malformed_rejects` (a matching tag with
no decoded width rejects in one step) together with the generic `seq_reject_handoff` would give
one.  Every **converse**, a **footprint** theorem — so every room premise is sufficient
and used, never shown necessary — and the pnp4 bridge (taken in
`ContentFixedGammaTargetLoopDecrementCountdownBridge`).  The composed `accept` is the countdown's
phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance; no `accepts`, `AcceptsAt`, `DecidesWithin` or `UniformP` is stated. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown

open PairEncoding
open FixedGammaTargetPayloadIteration (loopClock register_complete)
open FixedGammaTargetPayloadExhaustion (exhaustClock totalClock exhaust_strict payload_exhausted)
open FixedGammaTargetRegisterDecrement (borrow decBit priorDeadline prior_covers room_iff)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetUnaryCountdownIteration (lane_room)
open FixedGammaTargetDecrementCountdown (composedClock)

/-- The composed machine: G2p-d's payload round, then G2x's decrement-and-countdown composite, as
one closed table.  No row is new; the left rows are routed. -/
def machine : UniformTM :=
  FixedGammaTargetPayloadRound.machine.seq FixedGammaTargetDecrementCountdown.machine

/-- A payload-round state in the composed control, at its own index. -/
def inLoop (q : Fin FixedGammaTargetPayloadRound.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetPayloadRound.machine.seqLeft FixedGammaTargetDecrementCountdown.machine q

/-- A G2x state in the composed control, shifted past the twenty-two payload-round states. -/
def inTail (q : Fin FixedGammaTargetDecrementCountdown.machine.stateCount) :
    Fin machine.stateCount :=
  FixedGammaTargetPayloadRound.machine.seqRight FixedGammaTargetDecrementCountdown.machine q

/-- The routed target of a payload-round row: `qDone` becomes G2x's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedGammaTargetPayloadRound.stateCount) : Fin machine.stateCount :=
  FixedGammaTargetPayloadRound.machine.seqRoute FixedGammaTargetDecrementCountdown.machine q

/-- The payload round's own `startConfig` — the retagged *actual* G2p-d foundation endpoint — in the
composed control.  Still a phase-local retag of an earlier run, not `initialConfig` on a raw pair
input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedGammaTargetPayloadRound.machine.seqEmbedRouted FixedGammaTargetDecrementCountdown.machine
    (FixedGammaTargetPayloadRound.startConfig B x w)

/-- Exact cost of the payload loop followed by the whole of G2x: the loop's first arrival plus G2x's
`composedClock`.  The handoff between them costs nothing. -/
def chainClock (N zeros d v : Nat) : Nat := totalClock N zeros + composedClock N zeros d v

/-! ### Table, resource, handoff and clock pins -/

/-- The composed table, pinned: forty states, one hundred and twenty rows, the distinguished states
with their indices, the two block injections with their disjointness, the two nested sub-blocks and
their indices, the routing cases, every left row as the routed payload-round row, every right row as
the G2x row, the public step against the composed raw table everywhere, both executed handoff rows
literally with the state indices they connect, and the two summands of `chainClock`. -/
theorem table_and_resource_pins :
    machine.stateCount = 40 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 120 ∧
      machine.start = route FixedGammaTargetPayloadRound.qLoop ∧
      machine.start = inLoop FixedGammaTargetPayloadRound.qLoop ∧
      machine.accept = inTail FixedGammaTargetDecrementCountdown.machine.accept ∧
      machine.reject = inTail FixedGammaTargetDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 38 ∧ machine.reject.val = 39 ∧
      (∀ q, (inLoop q).val = q.val) ∧ (∀ q, (inLoop q).val < 22) ∧
      (∀ q, (inTail q).val = 22 + q.val) ∧ (∀ q, 22 ≤ (inTail q).val) ∧
      (∀ q, (inTail (FixedGammaTargetDecrementCountdown.inDecrement q)).val = 22 + q.val) ∧
      (∀ q, (inTail (FixedGammaTargetDecrementCountdown.inCountdown q)).val = 29 + q.val) ∧
      Function.Injective inLoop ∧ Function.Injective inTail ∧
      (∀ p q, inLoop p ≠ inTail q) ∧
      route FixedGammaTargetPayloadRound.qDone =
        inTail FixedGammaTargetDecrementCountdown.machine.start ∧
      route FixedGammaTargetPayloadRound.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetPayloadRound.qDone → q ≠ FixedGammaTargetPayloadRound.qReject →
        route q = inLoop q) ∧
      (∀ q s, machine.step (inLoop q) s =
        (route (FixedGammaTargetPayloadRound.machine.step q s).1,
          (FixedGammaTargetPayloadRound.machine.step q s).2.1,
          (FixedGammaTargetPayloadRound.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (FixedGammaTargetDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inLoop FixedGammaTargetPayloadRound.qFin).val = 19 ∧
      (inTail FixedGammaTargetDecrementCountdown.machine.start).val = 22 ∧
      machine.step (inLoop FixedGammaTargetPayloadRound.qFin) (some false) =
        (inTail FixedGammaTargetDecrementCountdown.machine.start, some false, .stay) ∧
      (inTail (FixedGammaTargetDecrementCountdown.inDecrement
        FixedGammaTargetRegisterDecrement.qBorrow)).val = 26 ∧
      (inTail (FixedGammaTargetDecrementCountdown.inCountdown
        FixedGammaTargetUnaryCountdown.qStart)).val = 29 ∧
      machine.step (inTail (FixedGammaTargetDecrementCountdown.inDecrement
          FixedGammaTargetRegisterDecrement.qBorrow)) (some true) =
        (inTail (FixedGammaTargetDecrementCountdown.inCountdown
          FixedGammaTargetUnaryCountdown.qStart), some false, .stay) ∧
      (∀ N zeros d v, chainClock N zeros d v = totalClock N zeros + composedClock N zeros d v) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedGammaTargetPayloadRound.machine.seq_pins FixedGammaTargetDecrementCountdown.machine
  have hright : ∀ q s, machine.step (inTail q) s =
      (inTail (FixedGammaTargetDecrementCountdown.machine.step q s).1,
        (FixedGammaTargetDecrementCountdown.machine.step q s).2.1,
        (FixedGammaTargetDecrementCountdown.machine.step q s).2.2) :=
    fun q s => FixedGammaTargetPayloadRound.machine.seq_step_right
      FixedGammaTargetDecrementCountdown.machine q s
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun q => q.isLt,
    fun _ => rfl, fun _ => Nat.le_add_right _ _, fun _ => rfl, fun q => ?_, hli, hri, hne, hra,
    hrr, hrw,
    fun q s => FixedGammaTargetPayloadRound.machine.seq_step_left
      FixedGammaTargetDecrementCountdown.machine q s,
    hright,
    fun q s => FixedGammaTargetPayloadRound.machine.seq_step_eq_rawStep
      FixedGammaTargetDecrementCountdown.machine q s,
    rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ _ _ => rfl⟩
  · have h : (inTail (FixedGammaTargetDecrementCountdown.inCountdown q)).val = 22 + (7 + q.val) :=
      rfl
    omega
  · rw [hright]
    exact congrArg (fun r => (inTail r.1, r.2.1, r.2.2))
      FixedGammaTargetDecrementCountdown.table_and_resource_pins.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The start, pinned: the payload round's `startConfig` routed into the composed control — the same
head and tape, the composed start as control.  Routing consults no decoded data. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadRound.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetPayloadRound.machine.seqEmbedRouted
        FixedGammaTargetDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The loop's first arrival -/

/-- **The payload loop enters `qDone` for the first time at `totalClock`.**  This is the enabling
fact for H16, stated about the *payload-round* machine out of its own `startConfig` and nothing
else, and it is assembled from landed theorems without a new trace.  At `loopClock (a+m) zeros`
G2p-e's `register_complete` puts the machine in the non-absorbing `qLoop`, and `no_terminal_of_le`
turns that single non-verdict into "neither verdict at that time or earlier"; above it `run_add`
reduces to the finish out of exactly the `r = zeros` configuration `register_complete` describes,
where G2p-f's `exhaust_strict` excludes `qDone` before `exhaustClock (a+m) zeros`, so strictness
holds below `totalClock (a+m) zeros = loopClock (a+m) zeros + exhaustClock (a+m) zeros`.  Arrival
itself is `payload_exhausted`; only minimality is added here.  The room premise is G2p-e's,
sufficient and used, never shown necessary. -/
theorem loop_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    ∀ t, t < totalClock (a + m) zeros →
      (FixedGammaTargetPayloadRound.machine.run t
        (FixedGammaTargetPayloadRound.startConfig B x w)).state ≠
          FixedGammaTargetPayloadRound.qDone := by
  intro t ht
  obtain ⟨hq, hh, htp, -, -⟩ := register_complete x w htag hg hzeros hroom
  by_cases hle : t ≤ loopClock (a + m) zeros
  · have hna : (FixedGammaTargetPayloadRound.machine.run (loopClock (a + m) zeros)
        (FixedGammaTargetPayloadRound.startConfig B x w)).state ≠
        FixedGammaTargetPayloadRound.machine.accept := by
      rw [hq]; decide
    have hnr : (FixedGammaTargetPayloadRound.machine.run (loopClock (a + m) zeros)
        (FixedGammaTargetPayloadRound.startConfig B x w)).state ≠
        FixedGammaTargetPayloadRound.machine.reject := by
      rw [hq]; decide
    exact (FixedGammaTargetPayloadRound.machine.no_terminal_of_le _ hna hnr t hle).1
  · have hsplit : FixedGammaTargetPayloadRound.machine.run t
        (FixedGammaTargetPayloadRound.startConfig B x w) =
        FixedGammaTargetPayloadRound.machine.run (t - loopClock (a + m) zeros)
          (FixedGammaTargetPayloadRound.machine.run (loopClock (a + m) zeros)
            (FixedGammaTargetPayloadRound.startConfig B x w)) := by
      rw [← UniformTM.run_add,
        show loopClock (a + m) zeros + (t - loopClock (a + m) zeros) = t by omega]
    rw [hsplit]
    exact (exhaust_strict x w htag hg (by omega) _ hq hh htp).1 _
      (by unfold totalClock at ht; omega)

/-! ### The executed handoff -/

/-- **H16 fires at the payload loop's first arrival, and it costs nothing.**  On a matching tag, a
decoded `2 ≤ zeros` and G2p-e's room, write `T = totalClock (a+m) zeros`.  Out of `startConfig`:
before `T` the composed control is in neither verdict; up to and including `T` the composed
configuration is the payload round's own, routed; at exactly `T` it **is** G2x's landed
`startConfig B x w`, re-embedded — the head and tape G2q retags at its length-only deadline
`priorDeadline (a+m)`, identified through the round machine's persistence from `T` to that
deadline; and every further step is a G2x step.  The second conjunct rests on `loop_strict` —
`qDone` is entered for the *first* time at `T`, so the routed edge fires then and not earlier —
which persistence alone would not give.  The fourth conjunct is a simulation equality and needs no
decrement, countdown or budget premise: it holds even where the budget leaves the tail unfinished.
`T` occurs in the statement only; no row of any of the three tables mentions it. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    let T := totalClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetPayloadRound.machine.seqEmbedRouted
          FixedGammaTargetDecrementCountdown.machine
          (FixedGammaTargetPayloadRound.machine.run t
            (FixedGammaTargetPayloadRound.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetPayloadRound.machine.seqEmbedRight
          FixedGammaTargetDecrementCountdown.machine
          (FixedGammaTargetDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetPayloadRound.machine.seqEmbedRight
          FixedGammaTargetDecrementCountdown.machine
          (FixedGammaTargetDecrementCountdown.machine.run s
            (FixedGammaTargetDecrementCountdown.startConfig B x w))) := by
  intro T c
  have hN : 9 + zeros ≤ a + m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  obtain ⟨hdq, -, -, -, -, -, hprior⟩ := payload_exhausted x w htag hg hzeros hroom
  have hstart : FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w) =
      FixedGammaTargetPayloadRound.machine.run T
        (FixedGammaTargetPayloadRound.startConfig B x w) :=
    hprior _ (prior_covers hN)
  have hleft : ∀ t, t ≤ T → machine.run t c =
      FixedGammaTargetPayloadRound.machine.seqEmbedRouted
        FixedGammaTargetDecrementCountdown.machine
        (FixedGammaTargetPayloadRound.machine.run t
          (FixedGammaTargetPayloadRound.startConfig B x w)) :=
    FixedGammaTargetPayloadRound.machine.seq_run_left
      FixedGammaTargetDecrementCountdown.machine _
      (loop_strict x w htag hg hzeros hroom)
  have hT : machine.run T c =
      FixedGammaTargetPayloadRound.machine.seqEmbedRight
        FixedGammaTargetDecrementCountdown.machine
        (FixedGammaTargetDecrementCountdown.startConfig B x w) := by
    rw [hleft T le_rfl]
    refine Config.ext_parts ?_ ?_ ?_
    · rw [UniformTM.seqEmbedRouted_state, UniformTM.seqEmbedRight_state, hdq]
      rfl
    · show (FixedGammaTargetPayloadRound.machine.run T
        (FixedGammaTargetPayloadRound.startConfig B x w)).head =
        (FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
          (FixedGammaTargetPayloadRound.startConfig B x w)).head
      rw [hstart]
    · show (FixedGammaTargetPayloadRound.machine.run T
        (FixedGammaTargetPayloadRound.startConfig B x w)).tape =
        (FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
          (FixedGammaTargetPayloadRound.startConfig B x w)).tape
      rw [hstart]
  have hsuffix : ∀ s, machine.run (T + s) c =
      FixedGammaTargetPayloadRound.machine.seqEmbedRight
        FixedGammaTargetDecrementCountdown.machine
        (FixedGammaTargetDecrementCountdown.machine.run s
          (FixedGammaTargetDecrementCountdown.startConfig B x w)) := by
    intro s
    rw [UniformTM.run_add, hT]
    exact FixedGammaTargetPayloadRound.machine.seq_run_right
      FixedGammaTargetDecrementCountdown.machine _ s
  have hTs : (machine.run T c).state =
      inTail FixedGammaTargetDecrementCountdown.machine.start := by
    rw [hT]; rfl
  have hTa : (machine.run T c).state ≠ machine.accept := by
    rw [hTs]; decide
  have hTr : (machine.run T c).state ≠ machine.reject := by
    rw [hTs]; decide
  exact ⟨fun t ht => machine.no_terminal_of_le c hTa hTr t (Nat.le_of_lt ht), hleft, hT, hsuffix⟩

/-- **The concrete exact run: loop, H16, decrement, H17, countdown, one machine.**  Under G2u's
**seven** hypotheses — a matching tag, a decoded `2 ≤ zeros`, the lane cap `v ≤ F`, the room
`zeros + 2 + F ≤ a + B`, and a `v` whose digit `zeros - j` is G2q's decremented register digit `j`
with no digit above `zeros` — after exactly `chainClock (a+m) zeros d v` steps out of `startConfig`
the composed machine is in its accept (the countdown's `qDone`) on the separator blank
`a+m+2+zeros` with tape `loopTape B x w zeros 0 v`, persisting at every later time.  That one tape
equality already determines the cleared register, the `v` marks and the blanks beyond, which G2u
and G2x state cell by cell; no cell-by-cell conjunct is restated here.  The first
`totalClock (a+m) zeros` steps are the payload loop's, H16 fires at its first arrival, and the
remaining `composedClock (a+m) zeros d v` steps are G2x's out of the configuration `handoff_exact`
identifies.  No eighth hypothesis: the decrement's room is G2u's lane room at `r = k = 0` and the
loop's room follows from it, both derived here.  `v` is universally quantified and nothing in pnp3
supplies it; persistence is not first arrival of the composed accept; `startConfig` still embeds
every earlier phase as a retag; reaching the composed accept is neither halting on a raw input nor
language acceptance. -/
theorem loop_decrement_countdown_drained {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := chainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) := by
  have hroom2 : a + m + 2 + zeros < tapeLength (pairLength a m) B :=
    (lane_room (r := 0) (k := 0) (Nat.zero_le F) hroom).2
  have hroom1 : a + m + 1 + zeros < tapeLength (pairLength a m) B :=
    (room_iff a m B zeros).2 hroom2
  obtain ⟨-, -, -, hsuffix⟩ := handoff_exact x w htag hg hzeros hroom1
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedGammaTargetDecrementCountdown.decrement_countdown_drained x w htag hg hzeros hfence hroom
      hv hhigh
  have hE : machine.run (chainClock (a + m) zeros (borrow x w zeros) v) (startConfig B x w) =
      FixedGammaTargetPayloadRound.machine.seqEmbedRight
        FixedGammaTargetDecrementCountdown.machine
        (FixedGammaTargetDecrementCountdown.machine.run
          (composedClock (a + m) zeros (borrow x w zeros) v)
          (FixedGammaTargetDecrementCountdown.startConfig B x w)) :=
    hsuffix (composedClock (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (chainClock (a + m) zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head]
    exact he2
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = chainClock (a + m) zeros (borrow x w zeros) v +
      (t - chainClock (a + m) zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown
