import Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation

/-!
# The first remaining gamma payload round (Part A G2p-d round)

One fixed 22-state, 66-row machine whose start configuration retags the *actual*
endpoint of the G2p-d `FixedGammaTargetPayloadLoopFoundation` run and executes
**one** round of the self-stopping gamma payload loop — one round, not the loop.
`pnp3/Docs/UniformP_V1.md` carries the long-form design notes.

Write `N = a + m`.  The foundation left the tape in the `r = 2` instance of the loop
invariant `loopTape B x w zeros r`: the counter prefix `[8, 7 + r]` of the gamma zero field
marked `some true`, the terminator trail `[8 + zeros, 8 + zeros + walk N zeros r)` blank,
the walking terminator at `8 + zeros + walk N zeros r`, and the target register
`[N + 1, N + 1 + r]` holding its `r + 1` digits.  This machine carries that invariant from
`r = 2` to `r = 3`: it tests the tape counter, marks the first unconsumed gamma zero (cell
`10`), consumes the next source, **appends** its bit to the register at cell `N + 2 + r`,
and advances the walking terminator when that source was physical.  The source is the third
payload digit — index `2` of the block `[9 + zeros, 9 + 2 * zeros)`, the cell `11 + zeros` —
and there is such a digit exactly when `3 ≤ zeros`, this module's work-remaining premise,
which is also what makes cell `10` an *unconsumed* zero.  Every branch is decided by the
symbol under the head: no width, digit index, bit, address, proof term, advice, or producer
mark occurs in the control.  There is no arithmetic carry: the register write is an append,
and the decrement from `n + 1` to `n` is a separate, deferred phase.  The `qFin` exhaustion
rows go unexecuted only over the bounded `r = 2 → r = 3` segment — the first `roundClock N`
transitions out of `startConfig`, where `3 ≤ zeros` keeps cell `10` unconsumed — and that is
deliberately no claim about later times: run on past that endpoint, even a `zeros = 3`
instance enters `qFin` and then `qDone`, its zero field exhausted at `r = 3`.

`roundClock N = 2 * N - 7` is the exact cost of the round and is **length-only**: the
virtual branch's `qVa`/`qVb` padding makes it independent of the source shape and of the
width.  It counts this phase alone, none of the steps `startConfig` embeds, so it clocks no
composed pipeline.  There is deliberately no phase deadline: `qLoop` is **not** absorbing,
so the endpoint holds at exactly `roundClock N` and may not be transported past it.  The
round needs more room since the register grows: `room_iff` reads
`a + m + 4 < tapeLength (pairLength a m) B` as `3 ≤ a + B`, one cell more than the
foundation's `2 ≤ a + B`, exactly what is needed (the head reaches `N + 4` and writes
there), and it implies the foundation's premise.  On the decoded-width `round_step` path the
head never goes below cell `9`, so the tag prefix and the first counter mark (cell `8`) are
never scanned; the second mark, cell `9`, is what stops `qCntZ`.  `malformed_rejects`
instead sits on the boundary head `a + m`, which is cell `8` when `a + m = 8`.

Deferred: the iteration of this round, the exhaustion finish, the complete target
register, the loop's own deadline, a cell-by-cell `r = 3` layout theorem (the endpoint is
a full tape equality to `loopTape`, whose `r = 2` layout the foundation pins), a
first-arrival/strictness direction, the all-times clamp/footprint/budget package, the
decrement from `n + 1` to `n`, the room the full loop needs
(`N + 1 + zeros < tapeLength …`, assumed nowhere), and the degenerate widths `zeros ≤ 2`.
No converse is stated: nothing says that `qLoop` at `roundClock N`, or the digit at
`N + 4`, implies `3 ≤ zeros`.  Nothing here is connected to `contentHeader?` or to any
parsed header value, and no pnp4 bridge exists.  Public `startConfig` at `zeros = 2` can
take the exhaustion path through `qFin` to `qDone`, but `zeros ≤ 2` and exhaustion are
outside the proved theorem surface; `qDone` is not language acceptance.  `startConfig`
retags an actual prior run, not a composed `UniformTM` execution from the raw pair input.
Clock composition, the fixed parser, advice freedom, `NP` membership, and
`ContentVerifierBridge` are out of scope: infrastructure, not P-vs-NP mainline. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadRound

open PairEncoding
open FixedGammaTargetPayloadLoopFoundation (walk registerBit loopTape)

abbrev stateCount : Nat := 22

def qLoop : Fin stateCount := ⟨0, by decide⟩
def qCntL : Fin stateCount := ⟨1, by decide⟩
def qCntZ : Fin stateCount := ⟨2, by decide⟩
def qCntMark : Fin stateCount := ⟨3, by decide⟩
def qCntBack : Fin stateCount := ⟨4, by decide⟩
def qSrc : Fin stateCount := ⟨5, by decide⟩
def qClear0 : Fin stateCount := ⟨6, by decide⟩
def qClear1 : Fin stateCount := ⟨7, by decide⟩
def qCarry0 : Fin stateCount := ⟨8, by decide⟩
def qCarry1 : Fin stateCount := ⟨9, by decide⟩
def qReg0 : Fin stateCount := ⟨10, by decide⟩
def qReg1 : Fin stateCount := ⟨11, by decide⟩
def qBackReg : Fin stateCount := ⟨12, by decide⟩
def qBackCont : Fin stateCount := ⟨13, by decide⟩
def qVa : Fin stateCount := ⟨14, by decide⟩
def qVb : Fin stateCount := ⟨15, by decide⟩
def qRegV : Fin stateCount := ⟨16, by decide⟩
def qBackRegV : Fin stateCount := ⟨17, by decide⟩
def qVc : Fin stateCount := ⟨18, by decide⟩
def qFin : Fin stateCount := ⟨19, by decide⟩
def qDone : Fin stateCount := ⟨20, by decide⟩
def qReject : Fin stateCount := ⟨21, by decide⟩

/-- Complete fixed 22-state, 66-row table.  `qFin` is not executed under `round_step`'s premises. -/
def raw (q : Fin stateCount) (s : Option Bool) : Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some true => (qCntL, some true, .left)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | none => (qCntL, none, .left)
    | some false => (qCntZ, some false, .left)
    | some true => (qFin, some false, .left)
  | 2 => match s with
    | some false => (qCntZ, some false, .left)
    | some true => (qCntMark, some true, .right)
    | none => (qReject, none, .stay)
  | 3 => match s with
    | some false => (qCntBack, some true, .right)
    | s => (qReject, s, .stay)
  | 4 => match s with
    | some true => (qSrc, some true, .right)
    | s => (qCntBack, s, .right)
  | 5 => match s with
    | some false => (qClear0, some true, .left)
    | some true => (qClear1, some true, .left)
    | none => (qVa, none, .left)
  | 6 => match s with
    | some true => (qCarry0, none, .right)
    | s => (qReject, s, .stay)
  | 7 => match s with
    | some true => (qCarry1, none, .right)
    | s => (qReject, s, .stay)
  | 8 => match s with
    | some b => (qCarry0, some b, .right)
    | none => (qReg0, none, .right)
  | 9 => match s with
    | some b => (qCarry1, some b, .right)
    | none => (qReg1, none, .right)
  | 10 => match s with
    | some b => (qReg0, some b, .right)
    | none => (qBackReg, some false, .left)
  | 11 => match s with
    | some b => (qReg1, some b, .right)
    | none => (qBackReg, some true, .left)
  | 12 => match s with
    | some b => (qBackReg, some b, .left)
    | none => (qBackCont, none, .left)
  | 13 => match s with
    | some b => (qBackCont, some b, .left)
    | none => (qLoop, none, .right)
  | 14 => match s with
    | some true => (qVb, some true, .right)
    | s => (qReject, s, .stay)
  | 15 => match s with
    | none => (qRegV, none, .right)
    | s => (qReject, s, .stay)
  | 16 => match s with
    | some b => (qRegV, some b, .right)
    | none => (qBackRegV, some false, .left)
  | 17 => match s with
    | some b => (qBackRegV, some b, .left)
    | none => (qVc, none, .left)
  | 18 => match s with
    | some true => (qLoop, some true, .stay)
    | s => (qReject, s, .stay)
  | 19 => match s with
    | some true => (qFin, some false, .left)
    | some false => (qDone, some false, .stay)
    | none => (qReject, none, .stay)
  | 20 => (qDone, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qLoop
  accept := qDone
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Phase-local handoff ABI: only the control field of the configuration is replaced. -/
def retagLoopFoundation {N B : Nat}
    (c : Config FixedGammaTargetPayloadLoopFoundation.stateCount N B) :
    Config stateCount N B := ⟨qLoop, c.head, c.tape⟩

/-- The retagged *actual* G2p-d foundation endpoint at the foundation's own
length-only deadline; no clock below counts its embedded steps. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagLoopFoundation (FixedGammaTargetPayloadLoopFoundation.machine.run
    (FixedGammaTargetPayloadLoopFoundation.deadline (a + m))
    (FixedGammaTargetPayloadLoopFoundation.startConfig B x w))

/-- Exact, length-only cost of one round; **not** a time from which the endpoint
persists, since `qLoop` does not absorb. -/
def roundClock (N : Nat) : Nat := 2 * N - 7
/-- A time from which a *malformed* gamma — no decoded width — is in `qReject`;
the matching first-arrival direction is not proved here. -/
def malformedExactClock : Nat := 1
/-- The round's source cell: the neighbour right of the incoming terminator,
read off the tape and never computed from a width. -/
def sourceCell (N zeros : Nat) : Nat := 9 + zeros + walk N zeros 2

/-! ### Table, resources, and the phase ABI -/

/-- Every row of the fixed table, pinned literally, with the resource counts. -/
theorem table_and_resource_pins :
    machine.step qLoop none = (qReject, none, .stay) ∧
    machine.step qLoop (some false) = (qReject, some false, .stay) ∧
    machine.step qLoop (some true) = (qCntL, some true, .left) ∧
    machine.step qCntL none = (qCntL, none, .left) ∧
    machine.step qCntL (some false) = (qCntZ, some false, .left) ∧
    machine.step qCntL (some true) = (qFin, some false, .left) ∧
    machine.step qCntZ none = (qReject, none, .stay) ∧
    machine.step qCntZ (some false) = (qCntZ, some false, .left) ∧
    machine.step qCntZ (some true) = (qCntMark, some true, .right) ∧
    machine.step qCntMark none = (qReject, none, .stay) ∧
    machine.step qCntMark (some false) = (qCntBack, some true, .right) ∧
    machine.step qCntMark (some true) = (qReject, some true, .stay) ∧
    machine.step qCntBack none = (qCntBack, none, .right) ∧
    machine.step qCntBack (some false) = (qCntBack, some false, .right) ∧
    machine.step qCntBack (some true) = (qSrc, some true, .right) ∧
    machine.step qSrc none = (qVa, none, .left) ∧
    machine.step qSrc (some false) = (qClear0, some true, .left) ∧
    machine.step qSrc (some true) = (qClear1, some true, .left) ∧
    machine.step qClear0 none = (qReject, none, .stay) ∧
    machine.step qClear0 (some false) = (qReject, some false, .stay) ∧
    machine.step qClear0 (some true) = (qCarry0, none, .right) ∧
    machine.step qClear1 none = (qReject, none, .stay) ∧
    machine.step qClear1 (some false) = (qReject, some false, .stay) ∧
    machine.step qClear1 (some true) = (qCarry1, none, .right) ∧
    machine.step qCarry0 none = (qReg0, none, .right) ∧
    machine.step qCarry0 (some false) = (qCarry0, some false, .right) ∧
    machine.step qCarry0 (some true) = (qCarry0, some true, .right) ∧
    machine.step qCarry1 none = (qReg1, none, .right) ∧
    machine.step qCarry1 (some false) = (qCarry1, some false, .right) ∧
    machine.step qCarry1 (some true) = (qCarry1, some true, .right) ∧
    machine.step qReg0 none = (qBackReg, some false, .left) ∧
    machine.step qReg0 (some false) = (qReg0, some false, .right) ∧
    machine.step qReg0 (some true) = (qReg0, some true, .right) ∧
    machine.step qReg1 none = (qBackReg, some true, .left) ∧
    machine.step qReg1 (some false) = (qReg1, some false, .right) ∧
    machine.step qReg1 (some true) = (qReg1, some true, .right) ∧
    machine.step qBackReg none = (qBackCont, none, .left) ∧
    machine.step qBackReg (some false) = (qBackReg, some false, .left) ∧
    machine.step qBackReg (some true) = (qBackReg, some true, .left) ∧
    machine.step qBackCont none = (qLoop, none, .right) ∧
    machine.step qBackCont (some false) = (qBackCont, some false, .left) ∧
    machine.step qBackCont (some true) = (qBackCont, some true, .left) ∧
    machine.step qVa none = (qReject, none, .stay) ∧
    machine.step qVa (some false) = (qReject, some false, .stay) ∧
    machine.step qVa (some true) = (qVb, some true, .right) ∧
    machine.step qVb none = (qRegV, none, .right) ∧
    machine.step qVb (some false) = (qReject, some false, .stay) ∧
    machine.step qVb (some true) = (qReject, some true, .stay) ∧
    machine.step qRegV none = (qBackRegV, some false, .left) ∧
    machine.step qRegV (some false) = (qRegV, some false, .right) ∧
    machine.step qRegV (some true) = (qRegV, some true, .right) ∧
    machine.step qBackRegV none = (qVc, none, .left) ∧
    machine.step qBackRegV (some false) = (qBackRegV, some false, .left) ∧
    machine.step qBackRegV (some true) = (qBackRegV, some true, .left) ∧
    machine.step qVc none = (qReject, none, .stay) ∧
    machine.step qVc (some false) = (qReject, some false, .stay) ∧
    machine.step qVc (some true) = (qLoop, some true, .stay) ∧
    machine.step qFin none = (qReject, none, .stay) ∧
    machine.step qFin (some false) = (qDone, some false, .stay) ∧
    machine.step qFin (some true) = (qFin, some false, .left) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 22 ∧ machine.start = qLoop ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    qLoop.val = 0 ∧ qCntL.val = 1 ∧ qCntZ.val = 2 ∧ qCntMark.val = 3 ∧
    qCntBack.val = 4 ∧ qSrc.val = 5 ∧ qClear0.val = 6 ∧ qClear1.val = 7 ∧
    qCarry0.val = 8 ∧ qCarry1.val = 9 ∧ qReg0.val = 10 ∧ qReg1.val = 11 ∧
    qBackReg.val = 12 ∧ qBackCont.val = 13 ∧ qVa.val = 14 ∧ qVb.val = 15 ∧
    qRegV.val = 16 ∧ qBackRegV.val = 17 ∧ qVc.val = 18 ∧ qFin.val = 19 ∧
    qDone.val = 20 ∧ qReject.val = 21 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 66 := by
  repeat' apply And.intro
  all_goals rfl

theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => rfl
  | some b => cases b <;> rfl

theorem endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  ⟨fun h n => machine.run_accept c h n, fun h n => machine.run_reject c h n⟩

/-- The phase-local handoff, pinned: the start configuration *is* the retagged
G2p-d foundation endpoint, with the same head and the same tape. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadLoopFoundation.machine.run
      (FixedGammaTargetPayloadLoopFoundation.deadline (a + m))
      (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)
    let c := startConfig B x w
    c = retagLoopFoundation p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Closed forms of every clock and address of this module. -/
theorem clock_pins (N zeros : Nat) :
    roundClock N = 2 * N - 7 ∧ malformedExactClock = 1 ∧
      sourceCell N zeros = 9 + zeros + walk N zeros 2 :=
  ⟨rfl, rfl, rfl⟩

/-- The round's room premise is exactly `3 ≤ a + B`, one cell more than the
foundation's, because the register grows; it implies the foundation premise.
Room is never inferred from a header. -/
theorem room_iff (a m B : Nat) :
    (a + m + 4 < tapeLength (pairLength a m) B ↔ 3 ≤ a + B) ∧
      (a + m + 4 < tapeLength (pairLength a m) B →
        a + m + 3 < tapeLength (pairLength a m) B) := by
  unfold tapeLength pairLength
  omega

/-- The source of this round is the third payload digit: on a physical source the
cell `11 + zeros`, inside the payload block `[9 + zeros, 9 + 2 * zeros)` exactly
because `3 ≤ zeros`; otherwise the boundary blank `N`.  This direction only. -/
theorem source_pins {N zeros : Nat} (hz : 3 ≤ zeros) (hN : 9 + zeros ≤ N) :
    (11 + zeros < N → sourceCell N zeros = 11 + zeros) ∧
      (N ≤ 11 + zeros → sourceCell N zeros = N) ∧
      (9 + zeros ≤ 11 + zeros ∧ 11 + zeros < 9 + 2 * zeros) ∧
      sourceCell N zeros ≤ N := by
  unfold sourceCell walk
  omega

/-- The appended digit is the register digit `3`: the content symbol at the
payload cell `11 + zeros`, read through the blank padding, so a cell at or past
`a + m` yields the virtual `false`. -/
theorem registerBit_source {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    registerBit x w zeros 3 =
      (FixedContentTagGate.physicalSymbol (Fin.append x w) (11 + zeros)).getD false := by
  have h := (FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).2.2.2 2
  rw [show (2 : Nat) + 1 = 3 from rfl] at h
  rw [h, show 9 + zeros + 2 = 11 + zeros by omega]

/-! ### Address-level execution kernel -/

private def content {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Nat → Option Bool :=
  FixedContentTagGate.physicalSymbol (Fin.append x w)

/-- Control, numeric head, and every tape cell read through its address. -/
private def At {n B : Nat} (c : Config stateCount n B) (q : Fin stateCount) (k : Nat)
    (T : Nat → Option Bool) : Prop :=
  c.state = q ∧ c.head.val = k ∧ ∀ i, c.tape i = T i.val

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
    | left =>
        change c.head.val - 1 = k - 1
        rw [hh]
    | stay => exact hh
    | right =>
        have hlt : c.head.val + 1 < tapeLength n B := by
          rw [hh]
          exact hfit rfl
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
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep
private theorem stepAt_stay {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .stay)) (hk : k = k')
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep

/-- Retime and re-address an `At` along provable equalities. -/
private theorem At_time {n B : Nat} {c : Config stateCount n B} {q : Fin stateCount}
    {k k' t t' : Nat} {T : Nat → Option Bool} (h : At (machine.run t c) q k T)
    (ht : t = t') (hk : k = k') : At (machine.run t' c) q k' T := by
  subst ht; subst hk; exact h

/-- Both terminal states absorb, so an `At` in one holds at every later time. -/
private theorem At_absorb {n B t : Nat} {c : Config stateCount n B} {q : Fin stateCount}
    {k : Nat} {T : Nat → Option Bool} (hc : At (machine.run t c) q k T)
    (hq : q = qDone ∨ q = qReject) (s : Nat) (hs : t ≤ s) : At (machine.run s c) q k T := by
  obtain ⟨u, rfl⟩ : ∃ u, s = t + u := ⟨s - t, by omega⟩
  obtain ⟨hq', hh, ht⟩ := hc
  rw [machine.run_add]
  rcases hq with rfl | rfl
  · rw [machine.run_accept _ hq' u]
    exact ⟨hq', hh, ht⟩
  · rw [machine.run_reject _ hq' u]
    exact ⟨hq', hh, ht⟩

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

/-! ### Rows that select on the carried bit -/

private def clearOf (b : Bool) : Fin stateCount := if b then qClear1 else qClear0
private def carryOf (b : Bool) : Fin stateCount := if b then qCarry1 else qCarry0
private def regOf (b : Bool) : Fin stateCount := if b then qReg1 else qReg0
private theorem row_src (b : Bool) :
    machine.step qSrc (some b) = (clearOf b, some true, .left) := by cases b <;> rfl
private theorem row_clear (b : Bool) :
    machine.step (clearOf b) (some true) = (carryOf b, none, .right) := by cases b <;> rfl
private theorem row_carry (b c : Bool) :
    machine.step (carryOf b) (some c) = (carryOf b, some c, .right) := by
  cases b <;> cases c <;> rfl
private theorem row_carry_blank (b : Bool) :
    machine.step (carryOf b) none = (regOf b, none, .right) := by cases b <;> rfl
private theorem row_reg (b c : Bool) :
    machine.step (regOf b) (some c) = (regOf b, some c, .right) := by
  cases b <;> cases c <;> rfl
private theorem row_reg_blank (b : Bool) :
    machine.step (regOf b) none = (qBackReg, some b, .left) := by cases b <;> rfl
private theorem row_backreg (c : Bool) :
    machine.step qBackReg (some c) = (qBackReg, some c, .left) := by cases c <;> rfl
private theorem row_backcont (c : Bool) :
    machine.step qBackCont (some c) = (qBackCont, some c, .left) := by cases c <;> rfl
private theorem row_regv (c : Bool) :
    machine.step qRegV (some c) = (qRegV, some c, .right) := by cases c <;> rfl
private theorem row_backregv (c : Bool) :
    machine.step qBackRegV (some c) = (qBackRegV, some c, .left) := by cases c <;> rfl

/-! ### Content cells and the incoming tape -/

private theorem content_lt {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : k < a + m) : ∃ b, content x w k = some b :=
  ⟨Fin.append x w ⟨k, hk⟩, by
    unfold content FixedContentTagGate.physicalSymbol
    rw [dif_pos hk]⟩
private theorem content_ge {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : a + m ≤ k) : content x w k = none := by
  unfold content FixedContentTagGate.physicalSymbol
  rw [dif_neg (show ¬ k < a + m by omega)]
private theorem contentTape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) :
    FixedPairContentMarkerErase.contentTape B x w i = content x w i.val := by
  unfold content FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
  split_ifs <;> rfl

/-- Tag cell `7`, the gamma zeros, and the input terminator. -/
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
  · rw [show i = 7 by omega]
    exact h7
  · have hi := hzero (i - 8) (by omega)
    rwa [show 8 + (i - 8) = i by omega] at hi

/-- Nat-addressed form of the foundation's `loopTape`. -/
private def loopNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros r k : Nat) :
    Option Bool :=
  if 8 ≤ k ∧ k ≤ 7 + r then some true
  else if 8 + zeros ≤ k ∧ k < 8 + zeros + walk (a + m) zeros r then none
  else if k = 8 + zeros + walk (a + m) zeros r then some true
  else if a + m + 1 ≤ k ∧ k ≤ a + m + 1 + r then
    some (registerBit x w zeros (k - (a + m + 1)))
  else content x w k

private theorem loopTape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros r : Nat) (i : Fin (tapeLength (pairLength a m) B)) :
    loopTape B x w zeros r i = loopNat x w zeros r i.val := by
  unfold loopTape loopNat
  split_ifs <;> first | exact contentTape_eq x w i | rfl

/-! ### Cell values of the incoming `r = 2` tape: every read of the round is one
of these six shapes. -/

section TwoTape
variable {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
private theorem two_mark (_hz : 3 ≤ zeros) (_hN : 9 + zeros ≤ a + m) :
    loopNat x w zeros 2 9 = some true := by
  unfold loopNat
  rw [if_pos ⟨by omega, by omega⟩]
private theorem two_zero (_hz : 3 ≤ zeros) (hN : 9 + zeros ≤ a + m)
    (hcells : ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false) (j : Nat)
    (h1 : 10 ≤ j) (h2 : j ≤ 7 + zeros) : loopNat x w zeros 2 j = some false := by
  have hw : walk (a + m) zeros 2 ≤ 2 := by unfold walk; omega
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hcells j (by omega) (by omega)
private theorem two_trail (hz : 3 ≤ zeros) (j : Nat) (h1 : 8 + zeros ≤ j)
    (h2 : j < 8 + zeros + walk (a + m) zeros 2) : loopNat x w zeros 2 j = none := by
  unfold loopNat
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]
private theorem two_term (hz : 3 ≤ zeros) :
    loopNat x w zeros 2 (8 + zeros + walk (a + m) zeros 2) = some true := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
private theorem two_content (hz : 3 ≤ zeros) (j : Nat)
    (h1 : 9 + zeros + walk (a + m) zeros 2 ≤ j) (h2 : j ≤ a + m) :
    loopNat x w zeros 2 j = content x w j := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
private theorem two_reg (hz : 3 ≤ zeros) (hN : 9 + zeros ≤ a + m) (j : Nat)
    (h1 : a + m + 1 ≤ j) (h2 : j ≤ a + m + 3) :
    loopNat x w zeros 2 j = some (registerBit x w zeros (j - (a + m + 1))) := by
  have hw : 8 + zeros + walk (a + m) zeros 2 < a + m := by unfold walk; omega
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega⟩]
private theorem two_blank4 (hz : 3 ≤ zeros) (hN : 9 + zeros ≤ a + m) :
    loopNat x w zeros 2 (a + m + 4) = none := by
  have hw : walk (a + m) zeros 2 ≤ 2 := by unfold walk; omega
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact content_ge x w (by omega)

end TwoTape

/-! ### The four intermediate tapes of the round -/

/-- After the counter mark at cell `10` is written. -/
private def tMark {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool := if k = 10 then some true else loopNat x w zeros 2 k

/-- After the new walking terminator is written over the physical source. -/
private def tSrc {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool := if k = 11 + zeros then some true else tMark x w zeros k

/-- After the cell the terminator left is blanked. -/
private def tClr {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool := if k = 10 + zeros then none else tSrc x w zeros k

/-- The physical branch's endpoint tape: the appended digit at `N + 4`. -/
private def tPhys {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) (b : Bool)
    (k : Nat) : Option Bool := if k = a + m + 4 then some b else tClr x w zeros k

/-- The virtual branch's endpoint tape: the appended virtual zero at `N + 4`. -/
private def tVirt {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool := if k = a + m + 4 then some false else tMark x w zeros k

section Stages
variable {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
private theorem tMark_miss (j : Nat) (h : j ≠ 10) :
    tMark x w zeros j = loopNat x w zeros 2 j := if_neg h
private theorem tClr_miss (j : Nat) (h : j ≠ 10) (h1 : j ≠ 10 + zeros)
    (h2 : j ≠ 11 + zeros) : tClr x w zeros j = loopNat x w zeros 2 j := by
  unfold tClr tSrc
  rw [if_neg h1, if_neg h2, tMark_miss x w j h]
private theorem tPhys_miss (b : Bool) (j : Nat) (h : j ≠ a + m + 4) :
    tPhys x w zeros b j = tClr x w zeros j := if_neg h
private theorem tVirt_miss (j : Nat) (h : j ≠ a + m + 4) :
    tVirt x w zeros j = tMark x w zeros j := if_neg h

end Stages

/-! ### Identifying the endpoint tapes with the `r = 3` invariant -/

private theorem loopNat_three_of_two {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hz : 3 ≤ zeros) (hP : 11 + zeros < a + m) {k : Nat} (h10 : k ≠ 10)
    (ht : k ≠ 10 + zeros) (ht' : k ≠ 11 + zeros) (hr : k ≠ a + m + 4) :
    loopNat x w zeros 3 k = loopNat x w zeros 2 k := by
  have hw2 : walk (a + m) zeros 2 = 2 := by unfold walk; omega
  have hw3 : walk (a + m) zeros 3 = 3 := by unfold walk; omega
  unfold loopNat
  rw [hw2, hw3]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem loopNat_three_of_two_tight {a m zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (hz : 3 ≤ zeros) (hN : 9 + zeros ≤ a + m) (hV : a + m ≤ 11 + zeros)
    {k : Nat} (h10 : k ≠ 10) (hr : k ≠ a + m + 4) :
    loopNat x w zeros 3 k = loopNat x w zeros 2 k := by
  have hw2 : walk (a + m) zeros 2 = a + m - 9 - zeros := by unfold walk; omega
  have hw3 : walk (a + m) zeros 3 = a + m - 9 - zeros := by unfold walk; omega
  unfold loopNat
  rw [hw2, hw3]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem tPhys_eq {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m) (b : Bool)
    (hz : 3 ≤ zeros) (hP : 11 + zeros < a + m) (hb : content x w (11 + zeros) = some b)
    (k : Nat) : tPhys x w zeros b k = loopNat x w zeros 3 k := by
  have hw3 : walk (a + m) zeros 3 = 3 := by unfold walk; omega
  have hval : registerBit x w zeros 3 = b := by
    have hb' : FixedContentTagGate.physicalSymbol (Fin.append x w) (11 + zeros) = some b := hb
    simp [registerBit_source x w zeros, hb']
  have hreg4 : loopNat x w zeros 3 (a + m + 4) = some b := by
    unfold loopNat
    rw [hw3, if_neg (show ¬(8 ≤ a + m + 4 ∧ a + m + 4 ≤ 7 + 3) by omega),
      if_neg (show ¬(8 + zeros ≤ a + m + 4 ∧ a + m + 4 < 8 + zeros + 3) by omega),
      if_neg (show ¬(a + m + 4 = 8 + zeros + 3) by omega),
      if_pos (show a + m + 1 ≤ a + m + 4 ∧ a + m + 4 ≤ a + m + 1 + 3 by omega),
      show a + m + 4 - (a + m + 1) = 3 by omega, hval]
  have htr : loopNat x w zeros 3 (10 + zeros) = none := by
    unfold loopNat
    rw [hw3, if_neg (show ¬(8 ≤ 10 + zeros ∧ 10 + zeros ≤ 7 + 3) by omega),
      if_pos (show 8 + zeros ≤ 10 + zeros ∧ 10 + zeros < 8 + zeros + 3 by omega)]
  have hte : loopNat x w zeros 3 (11 + zeros) = some true := by
    unfold loopNat
    rw [hw3, if_neg (show ¬(8 ≤ 11 + zeros ∧ 11 + zeros ≤ 7 + 3) by omega),
      if_neg (show ¬(8 + zeros ≤ 11 + zeros ∧ 11 + zeros < 8 + zeros + 3) by omega),
      if_pos (show 11 + zeros = 8 + zeros + 3 by omega)]
  have hmk : loopNat x w zeros 3 10 = some true := by
    unfold loopNat
    rw [if_pos (show 8 ≤ 10 ∧ 10 ≤ 7 + 3 by omega)]
  by_cases h4 : k = a + m + 4
  · subst h4
    rw [show tPhys x w zeros b (a + m + 4) = some b from if_pos rfl, hreg4]
  · rw [tPhys_miss x w b k h4]
    by_cases h3 : k = 10 + zeros
    · subst h3
      rw [show tClr x w zeros (10 + zeros) = none from if_pos rfl, htr]
    · rw [show tClr x w zeros k = tSrc x w zeros k from if_neg h3]
      by_cases h2 : k = 11 + zeros
      · subst h2
        rw [show tSrc x w zeros (11 + zeros) = some true from if_pos rfl, hte]
      · rw [show tSrc x w zeros k = tMark x w zeros k from if_neg h2]
        by_cases h1 : k = 10
        · subst h1
          rw [show tMark x w zeros 10 = some true from if_pos rfl, hmk]
        · rw [tMark_miss x w k h1]
          exact (loopNat_three_of_two x w hz hP h1 h3 h2 h4).symm

private theorem tVirt_eq {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hz : 3 ≤ zeros) (hN : 9 + zeros ≤ a + m) (hV : a + m ≤ 11 + zeros) (k : Nat) :
    tVirt x w zeros k = loopNat x w zeros 3 k := by
  have hw3 : walk (a + m) zeros 3 = a + m - 9 - zeros := by unfold walk; omega
  have hval : registerBit x w zeros 3 = false := by
    have hb' : FixedContentTagGate.physicalSymbol (Fin.append x w) (11 + zeros) = none :=
      content_ge x w (by omega)
    simp [registerBit_source x w zeros, hb']
  have hreg4 : loopNat x w zeros 3 (a + m + 4) = some false := by
    unfold loopNat
    rw [hw3, if_neg (show ¬(8 ≤ a + m + 4 ∧ a + m + 4 ≤ 7 + 3) by omega),
      if_neg (show ¬(8 + zeros ≤ a + m + 4 ∧
        a + m + 4 < 8 + zeros + (a + m - 9 - zeros)) by omega),
      if_neg (show ¬(a + m + 4 = 8 + zeros + (a + m - 9 - zeros)) by omega),
      if_pos (show a + m + 1 ≤ a + m + 4 ∧ a + m + 4 ≤ a + m + 1 + 3 by omega),
      show a + m + 4 - (a + m + 1) = 3 by omega, hval]
  have hmk : loopNat x w zeros 3 10 = some true := by
    unfold loopNat
    rw [if_pos (show 8 ≤ 10 ∧ 10 ≤ 7 + 3 by omega)]
  by_cases h4 : k = a + m + 4
  · subst h4
    rw [show tVirt x w zeros (a + m + 4) = some false from if_pos rfl, hreg4]
  · rw [tVirt_miss x w k h4]
    by_cases h1 : k = 10
    · subst h1
      rw [show tMark x w zeros 10 = some true from if_pos rfl, hmk]
    · rw [tMark_miss x w k h1]
      exact (loopNat_three_of_two_tight x w hz hN hV h1 h4).symm

/-! ### The execution -/

private theorem start_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 3 ≤ zeros) (hroom : a + m + 4 < tapeLength (pairLength a m) B) :
    At (startConfig B x w) qLoop (8 + zeros + walk (a + m) zeros 2)
      (loopNat x w zeros 2) := by
  obtain ⟨-, hh, ht⟩ :=
    FixedGammaTargetPayloadLoopFoundation.markers_at_deadline (B := B) x w htag hg
      (by omega) (by unfold tapeLength pairLength at hroom ⊢; omega)
  refine ⟨rfl, hh, fun i => ?_⟩
  change (FixedGammaTargetPayloadLoopFoundation.machine.run _ _).tape i = _
  rw [ht]
  exact loopTape_eq x w zeros 2 i

/-- The counter phase shared by both branches: mark the first unconsumed gamma zero,
cell `10`, and land on the cell right of the walking terminator — the next source. -/
private theorem prefix_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 3 ≤ zeros) (hroom : a + m + 4 < tapeLength (pairLength a m) B) :
    At (machine.run (2 * zeros + 2 * walk (a + m) zeros 2 - 1) (startConfig B x w)) qSrc
      (9 + zeros + walk (a + m) zeros 2) (tMark x w zeros) := by
  obtain ⟨hN, hcells⟩ := gamma_cells x w htag hg
  have hwt : 8 + zeros + walk (a + m) zeros 2 < a + m ∧ walk (a + m) zeros 2 ≤ 2 := by
    unfold walk; omega
  have hfit : ∀ k, k ≤ a + m + 4 → k < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    unfold tapeLength pairLength at hroom
    omega
  have hterm : tMark x w zeros (8 + zeros + walk (a + m) zeros 2) = some true := by
    rw [tMark_miss x w (8 + zeros + walk (a + m) zeros 2) (by omega)]
    exact two_term x w hz
  -- 1. off the terminator, left over the blank trail to the gamma zero field
  have h0 : At (machine.run 0 (startConfig B x w)) qLoop
      (8 + zeros + walk (a + m) zeros 2) (loopNat x w zeros 2) :=
    start_at (B := B) x w htag hg hz hroom
  have h1 : At (machine.run 1 (startConfig B x w)) qCntL
      (7 + zeros + walk (a + m) zeros 2) (loopNat x w zeros 2) :=
    At_time (stepAt_left h0 (two_term x w hz) rfl rfl (two_term x w hz) (fun _ _ => rfl))
      rfl (by omega)
  have h2 : At (machine.run (1 + walk (a + m) zeros 2) (startConfig B x w)) qCntL
      (7 + zeros) (loopNat x w zeros 2) := by
    refine At_time (walk_left (walk (a + m) zeros 2) (by omega) h1 (fun j hj1 hj2 => ?_))
      rfl (by omega)
    rw [two_trail x w hz j (by omega) (by omega)]
    rfl
  -- 2. left over the unconsumed zeros to the last counter mark
  have h3 : At (machine.run (2 + walk (a + m) zeros 2) (startConfig B x w)) qCntZ
      (6 + zeros) (loopNat x w zeros 2) :=
    At_time (stepAt_left h2 (two_zero x w hz hN hcells (7 + zeros) (by omega) (by omega))
      rfl rfl (two_zero x w hz hN hcells (7 + zeros) (by omega) (by omega))
      (fun _ _ => rfl)) (by omega) (by omega)
  have h4 : At (machine.run (zeros + walk (a + m) zeros 2 - 1) (startConfig B x w)) qCntZ 9
      (loopNat x w zeros 2) := by
    refine At_time (walk_left (zeros - 3) (by omega) h3 (fun j hj1 hj2 => ?_)) (by omega)
      (by omega)
    rw [two_zero x w hz hN hcells j (by omega) (by omega)]
    rfl
  -- 3. mark the first unconsumed zero, cell `10`
  have h5 : At (machine.run (zeros + walk (a + m) zeros 2) (startConfig B x w)) qCntMark 10
      (loopNat x w zeros 2) :=
    At_time (stepAt_right h4 (two_mark x w hz hN) rfl rfl (hfit 10 (by omega))
      (two_mark x w hz hN) (fun _ _ => rfl)) (by omega) rfl
  have h6 : At (machine.run (zeros + walk (a + m) zeros 2 + 1) (startConfig B x w)) qCntBack
      11 (tMark x w zeros) :=
    stepAt_right h5 (two_zero x w hz hN hcells 10 (by omega) (by omega)) rfl rfl
      (hfit 11 (by omega)) (if_pos rfl) (fun i hi => tMark_miss x w i hi)
  -- 4. right over the rest of the field and the trail, back onto the terminator
  have h7 : At (machine.run (2 * zeros + 2 * walk (a + m) zeros 2 - 2) (startConfig B x w))
      qCntBack (8 + zeros + walk (a + m) zeros 2) (tMark x w zeros) := by
    refine At_time (walk_right (8 + zeros + walk (a + m) zeros 2 - 11) h6
      (fun j hj1 hj2 => ?_) (hfit _ (by omega))) (by omega) (by omega)
    rw [tMark_miss x w j (by omega)]
    rcases Nat.lt_or_ge j (8 + zeros) with hj | hj
    · rw [two_zero x w hz hN hcells j (by omega) (by omega)]
      rfl
    · rw [two_trail x w hz j (by omega) (by omega)]
      rfl
  exact At_time (stepAt_right h7 hterm rfl rfl
    (hfit (8 + zeros + walk (a + m) zeros 2 + 1) (by omega)) hterm (fun _ _ => rfl))
    (by omega) (by omega)

/-- The physical branch: the source cell `11 + zeros` is a content cell, so the
walking terminator advances onto it and the cell it left is blanked. -/
private theorem phys_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 3 ≤ zeros) (hroom : a + m + 4 < tapeLength (pairLength a m) B)
    (hP : 11 + zeros < a + m) :
    At (machine.run (roundClock (a + m)) (startConfig B x w)) qLoop (11 + zeros)
      (loopNat x w zeros 3) := by
  obtain ⟨hN, hcells⟩ := gamma_cells x w htag hg
  have hw : walk (a + m) zeros 2 = 2 := by unfold walk; omega
  have hfit : ∀ k, k ≤ a + m + 4 → k < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    unfold tapeLength pairLength at hroom
    omega
  obtain ⟨b, hb⟩ := content_lt x w (k := 11 + zeros) (by omega)
  have h8 := prefix_at (B := B) x w htag hg hz hroom
  rw [hw] at h8
  have h8' : At (machine.run (2 * zeros + 3) (startConfig B x w)) qSrc (11 + zeros)
      (tMark x w zeros) := At_time h8 (by omega) (by omega)
  have hsrcval : tMark x w zeros (11 + zeros) = some b := by
    rw [tMark_miss x w (11 + zeros) (by omega),
      two_content x w hz (11 + zeros) (by omega) (by omega), hb]
  -- 5. read the source, write the new terminator, blank the cell it left
  have h9 : At (machine.run (2 * zeros + 4) (startConfig B x w)) (clearOf b) (10 + zeros)
      (tSrc x w zeros) :=
    At_time (stepAt_left h8' hsrcval (row_src b) rfl (if_pos rfl)
      (fun i hi => if_neg hi)) (by omega) (by omega)
  have hterm : tSrc x w zeros (10 + zeros) = some true := by
    rw [show tSrc x w zeros (10 + zeros) = tMark x w zeros (10 + zeros) from if_neg (by omega),
      tMark_miss x w (10 + zeros) (by omega)]
    have h := two_term x w (a := a) (m := m) (zeros := zeros) hz
    rw [hw, show 8 + zeros + 2 = 10 + zeros by omega] at h
    exact h
  have h10 : At (machine.run (2 * zeros + 5) (startConfig B x w)) (carryOf b) (11 + zeros)
      (tClr x w zeros) :=
    At_time (stepAt_right h9 hterm (row_clear b) rfl (hfit (10 + zeros + 1) (by omega))
      (if_pos rfl) (fun i hi => if_neg hi)) (by omega) (by omega)
  -- 6. carry the bit right to the boundary blank
  have hcont : ∀ j, 11 + zeros ≤ j → j < a + m → ∃ c, tClr x w zeros j = some c := by
    intro j hj1 hj2
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hj
    · refine ⟨true, ?_⟩
      rw [show tClr x w zeros (11 + zeros) = tSrc x w zeros (11 + zeros) from if_neg (by omega)]
      exact if_pos rfl
    · obtain ⟨c, hc⟩ := content_lt x w (k := j) hj2
      refine ⟨c, ?_⟩
      rw [tClr_miss x w j (by omega) (by omega) (by omega),
        two_content x w hz j (by omega) (by omega), hc]
  have h11 : At (machine.run (2 * zeros + 5 + (a + m - (11 + zeros))) (startConfig B x w))
      (carryOf b) (a + m) (tClr x w zeros) := by
    refine At_time (walk_right (a + m - (11 + zeros)) h10 (fun j hj1 hj2 => ?_)
      (hfit _ (by omega))) rfl (by omega)
    obtain ⟨c, hc⟩ := hcont j hj1 (by omega)
    rw [hc]
    exact row_carry b c
  have hblank : tClr x w zeros (a + m) = none := by
    rw [tClr_miss x w (a + m) (by omega) (by omega) (by omega),
      two_content x w hz (a + m) (by omega) (by omega)]
    exact content_ge x w le_rfl
  have h12 : At (machine.run (2 * zeros + 6 + (a + m - (11 + zeros))) (startConfig B x w))
      (regOf b) (a + m + 1) (tClr x w zeros) :=
    At_time (stepAt_right h11 hblank (row_carry_blank b) rfl (hfit (a + m + 1) (by omega))
      hblank (fun _ _ => rfl)) (by omega) rfl
  -- 7. walk the register to its first blank and append the bit there
  have hreg : ∀ j, a + m + 1 ≤ j → j ≤ a + m + 3 →
      tClr x w zeros j = some (registerBit x w zeros (j - (a + m + 1))) := by
    intro j h1 h2
    rw [tClr_miss x w j (by omega) (by omega) (by omega)]
    exact two_reg x w hz hN j h1 h2
  have h13 : At (machine.run (2 * zeros + 9 + (a + m - (11 + zeros))) (startConfig B x w))
      (regOf b) (a + m + 4) (tClr x w zeros) := by
    refine At_time (walk_right 3 h12 (fun j hj1 hj2 => ?_) (hfit _ (by omega)))
      (by omega) (by omega)
    rw [hreg j (by omega) (by omega)]
    exact row_reg b _
  have hblank4 : tClr x w zeros (a + m + 4) = none := by
    rw [tClr_miss x w (a + m + 4) (by omega) (by omega) (by omega)]
    exact two_blank4 x w hz hN
  have h14 : At (machine.run (2 * zeros + 10 + (a + m - (11 + zeros))) (startConfig B x w))
      qBackReg (a + m + 3) (tPhys x w zeros b) :=
    At_time (stepAt_left h13 hblank4 (row_reg_blank b) rfl (if_pos rfl)
      (fun i hi => if_neg hi)) (by omega) (by omega)
  -- 8. walk back over the register, the content, and into `qLoop`
  have h15 : At (machine.run (2 * zeros + 13 + (a + m - (11 + zeros))) (startConfig B x w))
      qBackReg (a + m) (tPhys x w zeros b) := by
    refine At_time (walk_left 3 (by omega) h14 (fun j hj1 hj2 => ?_)) (by omega) (by omega)
    rw [tPhys_miss x w b j (by omega), hreg j (by omega) (by omega)]
    exact row_backreg _
  have hblank' : tPhys x w zeros b (a + m) = none := by
    rw [tPhys_miss x w b (a + m) (by omega)]
    exact hblank
  have h16 : At (machine.run (2 * zeros + 14 + (a + m - (11 + zeros))) (startConfig B x w))
      qBackCont (a + m - 1) (tPhys x w zeros b) :=
    At_time (stepAt_left h15 hblank' rfl rfl hblank' (fun _ _ => rfl)) (by omega) rfl
  have h17 : At (machine.run (2 * zeros + 14 + 2 * (a + m - (11 + zeros)))
      (startConfig B x w)) qBackCont (10 + zeros) (tPhys x w zeros b) := by
    refine At_time (walk_left (a + m - (11 + zeros)) (by omega) h16 (fun j hj1 hj2 => ?_))
      (by omega) (by omega)
    obtain ⟨c, hc⟩ := hcont j (by omega) (by omega)
    rw [tPhys_miss x w b j (by omega), hc]
    exact row_backcont c
  have hgap : tPhys x w zeros b (10 + zeros) = none := by
    rw [tPhys_miss x w b (10 + zeros) (by omega)]
    exact if_pos rfl
  have h18 : At (machine.run (roundClock (a + m)) (startConfig B x w)) qLoop (11 + zeros)
      (tPhys x w zeros b) :=
    At_time (stepAt_right h17 hgap rfl rfl (hfit (10 + zeros + 1) (by omega)) hgap
      (fun _ _ => rfl)) (by unfold roundClock; omega) (by omega)
  obtain ⟨hq, hh, ht⟩ := h18
  exact ⟨hq, hh, fun i => (ht i).trans (tPhys_eq x w b hz hP hb i.val)⟩

/-- The virtual branch: the source address is the boundary blank itself, so the
terminator does not move and the appended digit is the virtual zero.  `qVa`/`qVb`
pad it to the physical branch's cost. -/
private theorem virt_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 3 ≤ zeros) (hroom : a + m + 4 < tapeLength (pairLength a m) B)
    (hV : a + m ≤ 11 + zeros) :
    At (machine.run (roundClock (a + m)) (startConfig B x w)) qLoop (a + m - 1)
      (loopNat x w zeros 3) := by
  obtain ⟨hN, hcells⟩ := gamma_cells x w htag hg
  have hw : walk (a + m) zeros 2 = a + m - 9 - zeros := by unfold walk; omega
  have hfit : ∀ k, k ≤ a + m + 4 → k < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    unfold tapeLength pairLength at hroom
    omega
  have h8 := prefix_at (B := B) x w htag hg hz hroom
  rw [hw] at h8
  have h8' : At (machine.run (2 * (a + m) - 19) (startConfig B x w)) qSrc (a + m)
      (tMark x w zeros) := At_time h8 (by omega) (by omega)
  have hbound : tMark x w zeros (a + m) = none := by
    rw [tMark_miss x w (a + m) (by omega), two_content x w hz (a + m) (by omega) (by omega)]
    exact content_ge x w le_rfl
  have hterm : tMark x w zeros (a + m - 1) = some true := by
    rw [tMark_miss x w (a + m - 1) (by omega)]
    have h := two_term x w (a := a) (m := m) (zeros := zeros) hz
    rw [hw, show 8 + zeros + (a + m - 9 - zeros) = a + m - 1 by omega] at h
    exact h
  -- 5. the source is the boundary blank: step back, pad, and enter the register
  have h9 : At (machine.run (2 * (a + m) - 18) (startConfig B x w)) qVa (a + m - 1)
      (tMark x w zeros) :=
    At_time (stepAt_left h8' hbound rfl rfl hbound (fun _ _ => rfl)) (by omega) rfl
  have h10 : At (machine.run (2 * (a + m) - 17) (startConfig B x w)) qVb (a + m)
      (tMark x w zeros) :=
    At_time (stepAt_right h9 hterm rfl rfl (hfit (a + m - 1 + 1) (by omega)) hterm
      (fun _ _ => rfl)) (by omega) (by omega)
  have h11 : At (machine.run (2 * (a + m) - 16) (startConfig B x w)) qRegV (a + m + 1)
      (tMark x w zeros) :=
    At_time (stepAt_right h10 hbound rfl rfl (hfit (a + m + 1) (by omega)) hbound
      (fun _ _ => rfl)) (by omega) rfl
  -- 6. walk the register to its first blank and append the virtual zero
  have hreg : ∀ j, a + m + 1 ≤ j → j ≤ a + m + 3 →
      tMark x w zeros j = some (registerBit x w zeros (j - (a + m + 1))) := by
    intro j h1 h2
    rw [tMark_miss x w j (by omega)]
    exact two_reg x w hz hN j h1 h2
  have h12 : At (machine.run (2 * (a + m) - 13) (startConfig B x w)) qRegV (a + m + 4)
      (tMark x w zeros) := by
    refine At_time (walk_right 3 h11 (fun j hj1 hj2 => ?_) (hfit _ (by omega)))
      (by omega) (by omega)
    rw [hreg j (by omega) (by omega)]
    exact row_regv _
  have hblank4 : tMark x w zeros (a + m + 4) = none := by
    rw [tMark_miss x w (a + m + 4) (by omega)]
    exact two_blank4 x w hz hN
  have h13 : At (machine.run (2 * (a + m) - 12) (startConfig B x w)) qBackRegV (a + m + 3)
      (tVirt x w zeros) :=
    At_time (stepAt_left h12 hblank4 rfl rfl (if_pos rfl) (fun i hi => if_neg hi))
      (by omega) (by omega)
  -- 7. walk back over the register and re-enter `qLoop` on the unmoved terminator
  have h14 : At (machine.run (2 * (a + m) - 9) (startConfig B x w)) qBackRegV (a + m)
      (tVirt x w zeros) := by
    refine At_time (walk_left 3 (by omega) h13 (fun j hj1 hj2 => ?_)) (by omega) (by omega)
    rw [tVirt_miss x w j (by omega), hreg j (by omega) (by omega)]
    exact row_backregv _
  have hbound' : tVirt x w zeros (a + m) = none := by
    rw [tVirt_miss x w (a + m) (by omega)]
    exact hbound
  have h15 : At (machine.run (2 * (a + m) - 8) (startConfig B x w)) qVc (a + m - 1)
      (tVirt x w zeros) :=
    At_time (stepAt_left h14 hbound' rfl rfl hbound' (fun _ _ => rfl)) (by omega) rfl
  have hterm' : tVirt x w zeros (a + m - 1) = some true := by
    rw [tVirt_miss x w (a + m - 1) (by omega)]
    exact hterm
  have h16 : At (machine.run (roundClock (a + m)) (startConfig B x w)) qLoop (a + m - 1)
      (tVirt x w zeros) :=
    At_time (stepAt_stay h15 hterm' rfl rfl hterm' (fun _ _ => rfl))
      (by unfold roundClock; omega) rfl
  obtain ⟨hq, hh, ht⟩ := h16
  exact ⟨hq, hh, fun i => (ht i).trans (tVirt_eq x w hz hN hV i.val)⟩

private theorem malformed_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    At (machine.run s (startConfig B x w)) qReject (a + m) (content x w) := by
  have hlen : 8 ≤ a + m :=
    (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
  obtain ⟨-, hh0, ht0⟩ :=
    FixedGammaTargetPayloadLoopFoundation.malformed_rejects (B := B) x w htag hg
      (FixedGammaTargetPayloadLoopFoundation.deadline (a + m)) (by
        unfold FixedGammaTargetPayloadLoopFoundation.deadline
          FixedGammaTargetPayloadLoopFoundation.malformedExactClock
        omega)
  have hbase : At (machine.run 0 (startConfig B x w)) qLoop (a + m) (content x w) := by
    refine ⟨rfl, hh0, fun i => ?_⟩
    show (FixedGammaTargetPayloadLoopFoundation.machine.run _ _).tape i = _
    rw [ht0]
    exact contentTape_eq x w i
  exact At_absorb (stepAt_stay hbase (content_ge x w le_rfl) rfl rfl (content_ge x w le_rfl)
    (fun _ _ => rfl)) (Or.inr rfl) s (by omega)

/-! ### Public execution theorems -/

/-- **The execution theorem of this slice.**  On a matching tag, a decoded width
with work remaining (`3 ≤ zeros`), and the round's own room premise
`a + m + 4 < tapeLength (pairLength a m) B`, the machine is after exactly
`roundClock (a + m) = 2 * (a + m) - 7` steps back in `qLoop` on the walking
terminator at head `8 + zeros + walk (a + m) zeros 3` with the whole tape equal to
`loopTape B x w zeros 3` — the counter prefix `[8, 10]` marked, the trail blank,
and the register `[a+m+1, a+m+4]` holding its four digits: one round of the loop
invariant, carried from `r = 2` to `r = 3`, in the physical and the virtual source
shape at once.  `qLoop` is **not** absorbing, so this is an exact time and not a
time from which the endpoint persists; there is deliberately no converse and no
first-arrival direction. -/
theorem round_step {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 3 ≤ zeros) (hroom : a + m + 4 < tapeLength (pairLength a m) B) :
    let d := machine.run (roundClock (a + m)) (startConfig B x w)
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros 3 ∧
      d.tape = loopTape B x w zeros 3 := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  have hres : At (machine.run (roundClock (a + m)) (startConfig B x w)) qLoop
      (8 + zeros + walk (a + m) zeros 3) (loopNat x w zeros 3) := by
    rcases Nat.lt_or_ge (11 + zeros) (a + m) with hP | hV
    · exact At_time (phys_at x w htag hg hzeros hroom hP) rfl (by unfold walk; omega)
    · exact At_time (virt_at x w htag hg hzeros hroom hV) rfl (by unfold walk; omega)
  obtain ⟨hq, hh, ht⟩ := hres
  exact ⟨hq, hh, funext fun i => (ht i).trans (loopTape_eq x w zeros 3 i).symm⟩

/-- A failed gamma scan: the retagged foundation rejection rejects again in one
step, at the boundary head `a + m`, on the unchanged content tape.  No room
premise is needed, and this is not a converse — nothing here says that `qReject`
implies a malformed gamma. -/
theorem malformed_rejects {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : malformedExactClock ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hq, hh, ht⟩ := malformed_at (B := B) x w htag hg s hs
  exact ⟨hq, hh, funext fun i => (ht i).trans (contentTape_eq x w i).symm⟩

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadRound
