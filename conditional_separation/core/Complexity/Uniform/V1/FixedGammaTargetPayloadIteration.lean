import Complexity.Uniform.V1.FixedGammaTargetPayloadRound

/-!
# Iterating the gamma payload round (Part A G2p-e)

No new machine.  The landed G2p-d `FixedGammaTargetPayloadRound.machine` — the fixed
22-state, 66-row table — re-enters `qLoop` at the end of a round, so the *same* machine
iterates: this module proves that, and nothing about a new table.  `pnp3/Docs/UniformP_V1.md`
carries the long-form design notes.

Write `N = a + m`.  The loop invariant is the foundation's `loopTape B x w zeros r`: the
counter prefix `[8, 7 + r]` of the gamma zero field marked `some true`, the terminator trail
`[8 + zeros, 8 + zeros + walk N zeros r)` blank, the walking terminator at
`8 + zeros + walk N zeros r`, the target register `[N + 1, N + 1 + r]` holding its `r + 1`
digits, and the incoming content tape everywhere else.  G2p-d proved one hard-coded step of
it, `r = 2 → r = 3`, out of its own `startConfig`.  Two things are new here.

* `round_generic` carries the invariant from `r` to `r + 1` for **every** `r` with
  `1 ≤ r < zeros`, out of an **arbitrary** configuration matching the `r`-instance rather than
  out of `startConfig`.  That is what the hard-coded theorem could not support: an induction.
  (The iteration below only ever instantiates `2 ≤ r`; `r = 1` is inside the statement but is
  produced by nothing here.)  The round's cost is still the length-only
  `roundClock N = 2 * N - 7`, in both source shapes and at every `r`, because the round splits
  into a counter phase costing `2 * walk N zeros r + 2 * (zeros - r) + 3`, a register walk out
  and back costing `2 * (r + 1)`, a content carry out and back costing
  `2 * (N - 9 - zeros - r)` that only the physical shape performs, and six fixed steps besides.
  In the physical shape `walk = r`, so the counter phase is already free of `r` and the carry's
  `-2 * r` cancels the register walk's `+2 * r`; in the virtual shape there is no carry, `walk`
  is the constant `N - 9 - zeros`, and it is the counter phase's `-2 * r` that cancels the
  register walk.  Both shapes take the same six fixed steps; three of the virtual ones pass
  through the `qVa`/`qVb`/`qVc` padding, standing at the positions where the physical shape
  enters `qClear`, `qCarry` and `qBackCont`.
* `rounds_iterate` runs that round `k` times out of the landed G2p-d `startConfig`, and
  `register_complete` is its `k = zeros - 2` instance: after exactly
  `loopClock N zeros = (zeros - 2) * roundClock N` steps the register holds all `zeros + 1`
  digits — the leading `true` of the bootstrap followed by every payload digit of the decoded
  width, each read through the blank padding so a truncated payload contributes virtual
  zeros.  That is the complete target *register content*; it is not a decoded number.

The source of round `r` is the payload cell `9 + zeros + r` when that is physical
(`9 + zeros + r < N`) and the boundary blank `N` otherwise, and it is always found as the
neighbour right of the walking terminator, never computed from a width.  Every branch is
symbol-driven: no width, digit index, target address, proof term, advice, or producer mark
occurs in control — the table is G2p-d's and is unchanged.

Room grows with the register: `room_iff` reads `N + 1 + zeros < tapeLength (pairLength a m) B`
as `zeros ≤ a + B`.  That is the premise the G2p-d round slice recorded as assumed nowhere, and
it is what `rounds_iterate` assumes; it implies the round's `3 ≤ a + B` at `3 ≤ zeros` and the
foundation's `2 ≤ a + B` at `2 ≤ zeros`.  A single round at index `r` assumes only
`N + 2 + r < tapeLength (pairLength a m) B`, that is `r < a + B`, and the round's trace does
reach `N + 2 + r` and write there, the largest such cell over the rounds iterated being
`N + 1 + zeros` at `r = zeros - 1`.  So these premises are sufficient and used, but nothing
here proves them necessary: there is no footprint theorem, and the deferred exhaustion finish
has none either, so none of this is claimed to be the room a *complete* loop needs.

`qLoop` does **not** absorb, so every endpoint below is an *exact* time and may not be
transported past it; there is no phase deadline and no first-arrival/strictness direction.
None of these clocks counts the steps `startConfig` embeds, so none clocks a composed
pipeline.

Deferred, and deliberately not claimed: the exhaustion finish (at `r = zeros` the next round's
counter scan finds the marked cell `7 + zeros` and leaves `qLoop` through `qFin`; that
behaviour, `qDone`, and the restoration of the gamma zero field are outside every theorem
here), the loop's own deadline, the decrement from `n + 1` to `n`, the all-times
clamp/footprint/budget package, a first-arrival direction, and every converse — nothing says
that `qLoop` at `loopClock N zeros`, or a register digit, implies anything about `zeros`.
`zeros = 2` is covered only in the degenerate sense that `loopClock N 2 = 0` makes
`register_complete` a restatement of the retagged foundation endpoint `startConfig`, and
`zeros ≤ 1` is excluded by `2 ≤ zeros`.
Nothing here is connected to `contentHeader?` or to any parsed header value, and no pnp4
bridge exists.  `startConfig` retags an actual prior run, not a composed `UniformTM` execution
from the raw pair input, and `qDone` is never language acceptance.  Clock composition, the
fixed parser, advice freedom, `NP` membership, and `ContentVerifierBridge` are out of scope:
infrastructure, not P-vs-NP mainline progress. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadIteration

open PairEncoding
open FixedGammaTargetPayloadLoopFoundation (walk registerBit loopTape)
open FixedGammaTargetPayloadRound (stateCount machine qLoop qCntL qCntZ qCntMark qCntBack qSrc
  qClear0 qClear1 qCarry0 qCarry1 qReg0 qReg1 qBackReg qBackCont qVa qVb qRegV qBackRegV qVc
  roundClock startConfig)

/-- Exact, length-and-width-only cost of the `zeros - 2` rounds this module iterates out of
the landed G2p-d start configuration.  It counts those rounds alone: neither the steps
`startConfig` embeds nor the deferred exhaustion finish, and it is not a time from which any
endpoint persists, since `qLoop` does not absorb. -/
def loopClock (N zeros : Nat) : Nat := (zeros - 2) * roundClock N

/-! ### Clock and room pins -/

/-- Closed forms of this module's clock, and the two widths at which it degenerates. -/
theorem loopClock_pins (N zeros : Nat) :
    loopClock N zeros = (zeros - 2) * roundClock N ∧ roundClock N = 2 * N - 7 ∧
      loopClock N 2 = 0 ∧ loopClock N 3 = 2 * N - 7 ∧
      loopClock N 4 = 2 * (2 * N - 7) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> unfold loopClock roundClock <;> omega

/-- The room the *whole* iteration assumes is exactly `zeros ≤ a + B`; it implies the single
round's `3 ≤ a + B` at `3 ≤ zeros` and the foundation's `2 ≤ a + B` at `2 ≤ zeros`, and the
room a single round at index `r` assumes is `r < a + B`.  Sufficiency is what the execution
theorems below use; necessity is not proved, and room is never inferred from a header. -/
theorem room_iff (a m B zeros r : Nat) :
    (a + m + 1 + zeros < tapeLength (pairLength a m) B ↔ zeros ≤ a + B) ∧
      (a + m + 2 + r < tapeLength (pairLength a m) B ↔ r < a + B) ∧
      (2 ≤ zeros → a + m + 1 + zeros < tapeLength (pairLength a m) B →
        a + m + 3 < tapeLength (pairLength a m) B) ∧
      (3 ≤ zeros → a + m + 1 + zeros < tapeLength (pairLength a m) B →
        a + m + 4 < tapeLength (pairLength a m) B) ∧
      (r + 1 ≤ zeros → a + m + 1 + zeros < tapeLength (pairLength a m) B →
        a + m + 2 + r < tapeLength (pairLength a m) B) := by
  unfold tapeLength pairLength
  omega

/-- The completed register's digits, spelled out: digit `0` is the bootstrap's leading
`true`, and digit `i + 1` is the payload cell `9 + zeros + i` read through the blank padding,
so `i < zeros` covers exactly the payload block `[9 + zeros, 9 + 2 * zeros)` of the decoded
width and a truncated payload contributes virtual zeros.  "Exactly" is the fourth conjunct:
the source addresses of the digits `1 … zeros` are precisely the cells of that block, neither
short of it nor past it.  The statement is hypothesis-free, so `zeros` is an arbitrary `Nat`
here; it is *the decoded width* only where the execution theorems below supply
`gammaZeros? (Fin.append x w) = some zeros`.  This is the register's *content*; nothing here
decodes it into a number and no `contentHeader?` value occurs. -/
theorem register_digits {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    registerBit x w zeros 0 = true ∧
      (∀ i, i < zeros → registerBit x w zeros (i + 1) =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + i)).getD false) ∧
      (∀ i, i < zeros → 9 + zeros ≤ 9 + zeros + i ∧ 9 + zeros + i < 9 + 2 * zeros) ∧
      (∀ k, (9 + zeros ≤ k ∧ k < 9 + 2 * zeros) ↔ ∃ i, i < zeros ∧ k = 9 + zeros + i) :=
  ⟨(FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).1,
    fun i _ => (FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).2.2.2 i,
    fun _ h => ⟨by omega, by omega⟩,
    fun k => ⟨fun h => ⟨k - (9 + zeros), by omega, by omega⟩, fun ⟨i, hi, hk⟩ => by omega⟩⟩

/-! ### Address-level execution kernel

The same kernel every phase of this pipeline uses: a configuration is described by its
control, its numeric head, and every tape cell read through its Nat address, and one
`machine.step` row is consumed at a time.  Nothing here is specific to this slice; the round
module's own copy is `private`, so it is restated rather than imported. -/

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

/-! ### Content cells, the gamma field, and the invariant tape -/

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

/-- Nat-addressed form of the foundation's `loopTape`, at every `r`. -/
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

/-- The terminator advance, closed at both source shapes: it never passes the boundary, and
whether it moves this round is decided by `9 + zeros + r` against `a + m` alone. -/
private theorem walk_bounds (a m zeros r : Nat) (hN : 9 + zeros ≤ a + m) :
    walk (a + m) zeros r ≤ r ∧ 9 + zeros + walk (a + m) zeros r ≤ a + m ∧
      (9 + zeros + r < a + m →
        walk (a + m) zeros r = r ∧ walk (a + m) zeros (r + 1) = r + 1) ∧
      (a + m ≤ 9 + zeros + r →
        walk (a + m) zeros r = a + m - 9 - zeros ∧
          walk (a + m) zeros (r + 1) = a + m - 9 - zeros) := by
  unfold walk
  omega

/-! ### Cell values of the incoming `r`-instance: every read of a round is one of these. -/

section RTape
variable {a m zeros r : Nat} (x : Bitstring a) (w : Bitstring m)

private theorem r_mark (hr : 1 ≤ r) : loopNat x w zeros r (7 + r) = some true := by
  unfold loopNat
  rw [if_pos ⟨by omega, by omega⟩]

private theorem r_zero (_hrz : r < zeros) (hN : 9 + zeros ≤ a + m)
    (hcells : ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false) (j : Nat)
    (h1 : 8 + r ≤ j) (h2 : j ≤ 7 + zeros) : loopNat x w zeros r j = some false := by
  have hw := walk_bounds a m zeros r hN
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hcells j (by omega) (by omega)

private theorem r_trail (hrz : r < zeros) (j : Nat) (h1 : 8 + zeros ≤ j)
    (h2 : j < 8 + zeros + walk (a + m) zeros r) : loopNat x w zeros r j = none := by
  unfold loopNat
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

private theorem r_term (hrz : r < zeros) :
    loopNat x w zeros r (8 + zeros + walk (a + m) zeros r) = some true := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

private theorem r_content (hrz : r < zeros) (hN : 9 + zeros ≤ a + m) (j : Nat)
    (h1 : 9 + zeros + walk (a + m) zeros r ≤ j) (h2 : j ≤ a + m) :
    loopNat x w zeros r j = content x w j := by
  have hw := walk_bounds a m zeros r hN
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem r_reg (hrz : r < zeros) (hN : 9 + zeros ≤ a + m) (j : Nat)
    (h1 : a + m + 1 ≤ j) (h2 : j ≤ a + m + 1 + r) :
    loopNat x w zeros r j = some (registerBit x w zeros (j - (a + m + 1))) := by
  have hw := walk_bounds a m zeros r hN
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]

private theorem r_next_blank (hrz : r < zeros) (hN : 9 + zeros ≤ a + m) :
    loopNat x w zeros r (a + m + 2 + r) = none := by
  have hw := walk_bounds a m zeros r hN
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact content_ge x w (by omega)

end RTape

/-! ### The four intermediate tapes of a round at index `r` -/

/-- After the counter mark at cell `8 + r` is written. -/
private def tMark {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros r k : Nat) :
    Option Bool := if k = 8 + r then some true else loopNat x w zeros r k

/-- After the new walking terminator is written over the physical source. -/
private def tSrc {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros r k : Nat) :
    Option Bool :=
  if k = 9 + zeros + walk (a + m) zeros r then some true else tMark x w zeros r k

/-- After the cell the terminator left is blanked. -/
private def tClr {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros r k : Nat) :
    Option Bool :=
  if k = 8 + zeros + walk (a + m) zeros r then none else tSrc x w zeros r k

/-- The physical branch's endpoint tape: the appended digit at `a + m + 2 + r`. -/
private def tPhys {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros r : Nat) (b : Bool)
    (k : Nat) : Option Bool := if k = a + m + 2 + r then some b else tClr x w zeros r k

/-- The virtual branch's endpoint tape: the appended virtual zero at `a + m + 2 + r`. -/
private def tVirt {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros r k : Nat) :
    Option Bool := if k = a + m + 2 + r then some false else tMark x w zeros r k

section Stages
variable {a m zeros r : Nat} (x : Bitstring a) (w : Bitstring m)

private theorem tMark_miss (j : Nat) (h : j ≠ 8 + r) :
    tMark x w zeros r j = loopNat x w zeros r j := if_neg h

private theorem tClr_miss (j : Nat) (h : j ≠ 8 + r)
    (h1 : j ≠ 8 + zeros + walk (a + m) zeros r)
    (h2 : j ≠ 9 + zeros + walk (a + m) zeros r) :
    tClr x w zeros r j = loopNat x w zeros r j := by
  unfold tClr tSrc
  rw [if_neg h1, if_neg h2, tMark_miss x w j h]

private theorem tPhys_miss (b : Bool) (j : Nat) (h : j ≠ a + m + 2 + r) :
    tPhys x w zeros r b j = tClr x w zeros r j := if_neg h

private theorem tVirt_miss (j : Nat) (h : j ≠ a + m + 2 + r) :
    tVirt x w zeros r j = tMark x w zeros r j := if_neg h

end Stages

/-! ### Identifying the endpoint tapes with the `r + 1` instance -/

private theorem loopNat_succ_phys {a m zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hrz : r < zeros) (hN : 9 + zeros ≤ a + m) (hP : 9 + zeros + r < a + m) {k : Nat}
    (h1 : k ≠ 8 + r) (h2 : k ≠ 8 + zeros + r) (h3 : k ≠ 9 + zeros + r)
    (h4 : k ≠ a + m + 2 + r) :
    loopNat x w zeros (r + 1) k = loopNat x w zeros r k := by
  obtain ⟨-, -, hphys, -⟩ := walk_bounds a m zeros r hN
  obtain ⟨hwr, hwr1⟩ := hphys hP
  unfold loopNat
  rw [hwr, hwr1]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem loopNat_succ_virt {a m zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hrz : r < zeros) (hN : 9 + zeros ≤ a + m) (hV : a + m ≤ 9 + zeros + r) {k : Nat}
    (h1 : k ≠ 8 + r) (h4 : k ≠ a + m + 2 + r) :
    loopNat x w zeros (r + 1) k = loopNat x w zeros r k := by
  obtain ⟨-, -, -, hvirt⟩ := walk_bounds a m zeros r hN
  obtain ⟨hwr, hwr1⟩ := hvirt hV
  unfold loopNat
  rw [hwr, hwr1]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem tPhys_eq {a m zeros r : Nat} (x : Bitstring a) (w : Bitstring m) (b : Bool)
    (hrz : r < zeros) (hN : 9 + zeros ≤ a + m) (hP : 9 + zeros + r < a + m)
    (hb : content x w (9 + zeros + r) = some b) (k : Nat) :
    tPhys x w zeros r b k = loopNat x w zeros (r + 1) k := by
  obtain ⟨-, -, hphys, -⟩ := walk_bounds a m zeros r hN
  obtain ⟨hwr, hwr1⟩ := hphys hP
  have hval : registerBit x w zeros (r + 1) = b := by
    have hb' : FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + r) =
        some b := hb
    simp [(FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).2.2.2 r, hb']
  have hreg : loopNat x w zeros (r + 1) (a + m + 2 + r) = some b := by
    unfold loopNat
    rw [hwr1, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (show a + m + 1 ≤ a + m + 2 + r ∧ a + m + 2 + r ≤ a + m + 1 + (r + 1) by omega),
      show a + m + 2 + r - (a + m + 1) = r + 1 by omega, hval]
  have htr : loopNat x w zeros (r + 1) (8 + zeros + r) = none := by
    unfold loopNat
    rw [hwr1, if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  have hte : loopNat x w zeros (r + 1) (9 + zeros + r) = some true := by
    unfold loopNat
    rw [hwr1, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have hmk : loopNat x w zeros (r + 1) (8 + r) = some true := by
    unfold loopNat
    rw [if_pos ⟨by omega, by omega⟩]
  by_cases h4 : k = a + m + 2 + r
  · subst h4
    rw [show tPhys x w zeros r b (a + m + 2 + r) = some b from if_pos rfl, hreg]
  · rw [tPhys_miss x w b k h4]
    by_cases h2 : k = 8 + zeros + r
    · subst h2
      rw [show tClr x w zeros r (8 + zeros + r) = none from if_pos (by rw [hwr]), htr]
    · rw [show tClr x w zeros r k = tSrc x w zeros r k from if_neg (by rw [hwr]; omega)]
      by_cases h3 : k = 9 + zeros + r
      · subst h3
        rw [show tSrc x w zeros r (9 + zeros + r) = some true from if_pos (by rw [hwr]), hte]
      · rw [show tSrc x w zeros r k = tMark x w zeros r k from if_neg (by rw [hwr]; omega)]
        by_cases h1 : k = 8 + r
        · subst h1
          rw [show tMark x w zeros r (8 + r) = some true from if_pos rfl, hmk]
        · rw [tMark_miss x w k h1]
          exact (loopNat_succ_phys x w hrz hN hP h1 h2 h3 h4).symm

private theorem tVirt_eq {a m zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hrz : r < zeros) (hN : 9 + zeros ≤ a + m) (hV : a + m ≤ 9 + zeros + r) (k : Nat) :
    tVirt x w zeros r k = loopNat x w zeros (r + 1) k := by
  obtain ⟨-, -, -, hvirt⟩ := walk_bounds a m zeros r hN
  obtain ⟨hwr, hwr1⟩ := hvirt hV
  have hval : registerBit x w zeros (r + 1) = false := by
    have hb' : FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + r) = none :=
      content_ge x w (by omega)
    simp [(FixedGammaTargetPayloadLoopFoundation.registerBit_pins x w zeros).2.2.2 r, hb']
  have hreg : loopNat x w zeros (r + 1) (a + m + 2 + r) = some false := by
    unfold loopNat
    rw [hwr1, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (show a + m + 1 ≤ a + m + 2 + r ∧ a + m + 2 + r ≤ a + m + 1 + (r + 1) by omega),
      show a + m + 2 + r - (a + m + 1) = r + 1 by omega, hval]
  have hmk : loopNat x w zeros (r + 1) (8 + r) = some true := by
    unfold loopNat
    rw [if_pos ⟨by omega, by omega⟩]
  by_cases h4 : k = a + m + 2 + r
  · subst h4
    rw [show tVirt x w zeros r (a + m + 2 + r) = some false from if_pos rfl, hreg]
  · rw [tVirt_miss x w k h4]
    by_cases h1 : k = 8 + r
    · subst h1
      rw [show tMark x w zeros r (8 + r) = some true from if_pos rfl, hmk]
    · rw [tMark_miss x w k h1]
      exact (loopNat_succ_virt x w hrz hN hV h1 h4).symm

/-! ### The execution of one round at an arbitrary index `r` -/

/-- The counter phase shared by both branches, out of an arbitrary `r`-instance: mark the
first unconsumed gamma zero, cell `8 + r`, and land on the cell right of the walking
terminator — the next source.  It costs `2 * walk + 2 * (zeros - r) + 3`, scanning left over
the blank trail and the unconsumed zeros and right back over both.  Its `-2 * r` is what the
register walk below cancels in the virtual branch; in the physical branch `walk = r` makes
this phase `r`-free on its own and the content carry cancels the register walk instead. -/
private theorem prefix_at {a m B zeros r : Nat} {c : Config stateCount (pairLength a m) B}
    (x : Bitstring a) (w : Bitstring m) (hr : 1 ≤ r) (hrz : r < zeros)
    (hN : 9 + zeros ≤ a + m)
    (hcells : ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false)
    (hroom : a + m + 2 + r < tapeLength (pairLength a m) B)
    (hc : At c qLoop (8 + zeros + walk (a + m) zeros r) (loopNat x w zeros r)) :
    At (machine.run (2 * walk (a + m) zeros r + 2 * (zeros - r) + 3) c) qSrc
      (9 + zeros + walk (a + m) zeros r) (tMark x w zeros r) := by
  obtain ⟨hwle, hwN, -, -⟩ := walk_bounds a m zeros r hN
  have hfit : ∀ k, k ≤ a + m + 2 + r → k < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    unfold tapeLength pairLength at hroom
    omega
  have hterm : tMark x w zeros r (8 + zeros + walk (a + m) zeros r) = some true := by
    rw [tMark_miss x w (8 + zeros + walk (a + m) zeros r) (by omega)]
    exact r_term x w hrz
  -- 1. off the terminator, left over the blank trail to the gamma zero field
  have h0 : At (machine.run 0 c) qLoop (8 + zeros + walk (a + m) zeros r)
      (loopNat x w zeros r) := hc
  have h1 : At (machine.run 1 c) qCntL (7 + zeros + walk (a + m) zeros r)
      (loopNat x w zeros r) :=
    At_time (stepAt_left h0 (r_term x w hrz) rfl rfl (r_term x w hrz) (fun _ _ => rfl))
      rfl (by omega)
  have h2 : At (machine.run (1 + walk (a + m) zeros r) c) qCntL (7 + zeros)
      (loopNat x w zeros r) := by
    refine At_time (walk_left (walk (a + m) zeros r) (by omega) h1 (fun j hj1 hj2 => ?_))
      rfl (by omega)
    rw [r_trail x w hrz j (by omega) (by omega)]
    rfl
  -- 2. left over the unconsumed zeros to the last counter mark
  have h3 : At (machine.run (2 + walk (a + m) zeros r) c) qCntZ (6 + zeros)
      (loopNat x w zeros r) :=
    At_time (stepAt_left h2 (r_zero x w hrz hN hcells (7 + zeros) (by omega) (by omega))
      rfl rfl (r_zero x w hrz hN hcells (7 + zeros) (by omega) (by omega))
      (fun _ _ => rfl)) (by omega) (by omega)
  have h4 : At (machine.run (walk (a + m) zeros r + (zeros - r) + 1) c) qCntZ (7 + r)
      (loopNat x w zeros r) := by
    refine At_time (walk_left (zeros - r - 1) (by omega) h3 (fun j hj1 hj2 => ?_)) (by omega)
      (by omega)
    rw [r_zero x w hrz hN hcells j (by omega) (by omega)]
    rfl
  -- 3. mark the first unconsumed zero, cell `8 + r`
  have h5 : At (machine.run (walk (a + m) zeros r + (zeros - r) + 2) c) qCntMark (8 + r)
      (loopNat x w zeros r) :=
    At_time (stepAt_right h4 (r_mark x w hr) rfl rfl (hfit (7 + r + 1) (by omega))
      (r_mark x w hr) (fun _ _ => rfl)) (by omega) (by omega)
  have h6 : At (machine.run (walk (a + m) zeros r + (zeros - r) + 3) c) qCntBack (9 + r)
      (tMark x w zeros r) :=
    At_time (stepAt_right h5 (r_zero x w hrz hN hcells (8 + r) (by omega) (by omega)) rfl rfl
      (hfit (8 + r + 1) (by omega)) (if_pos rfl) (fun i hi => tMark_miss x w i hi))
      (by omega) (by omega)
  -- 4. right over the rest of the field and the trail, back onto the terminator
  have h7 : At (machine.run (2 * walk (a + m) zeros r + 2 * (zeros - r) + 2) c) qCntBack
      (8 + zeros + walk (a + m) zeros r) (tMark x w zeros r) := by
    refine At_time (walk_right (8 + zeros + walk (a + m) zeros r - (9 + r)) h6
      (fun j hj1 hj2 => ?_) (hfit _ (by omega))) (by omega) (by omega)
    rw [tMark_miss x w j (by omega)]
    rcases Nat.lt_or_ge j (8 + zeros) with hj | hj
    · rw [r_zero x w hrz hN hcells j (by omega) (by omega)]
      rfl
    · rw [r_trail x w hrz j (by omega) (by omega)]
      rfl
  exact At_time (stepAt_right h7 hterm rfl rfl
    (hfit (8 + zeros + walk (a + m) zeros r + 1) (by omega)) hterm (fun _ _ => rfl))
    (by omega) (by omega)

/-- The physical branch: the source cell `9 + zeros + r` is a content cell, so the walking
terminator advances onto it and the cell it left is blanked. -/
private theorem phys_at {a m B zeros r : Nat} {c : Config stateCount (pairLength a m) B}
    (x : Bitstring a) (w : Bitstring m) (hr : 1 ≤ r) (hrz : r < zeros)
    (hN : 9 + zeros ≤ a + m)
    (hcells : ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false)
    (hroom : a + m + 2 + r < tapeLength (pairLength a m) B) (hP : 9 + zeros + r < a + m)
    (hc : At c qLoop (8 + zeros + walk (a + m) zeros r) (loopNat x w zeros r)) :
    At (machine.run (roundClock (a + m)) c) qLoop (9 + zeros + r)
      (loopNat x w zeros (r + 1)) := by
  obtain ⟨-, -, hphys, -⟩ := walk_bounds a m zeros r hN
  obtain ⟨hwr, -⟩ := hphys hP
  have hfit : ∀ k, k ≤ a + m + 2 + r → k < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    unfold tapeLength pairLength at hroom
    omega
  obtain ⟨b, hb⟩ := content_lt x w (k := 9 + zeros + r) hP
  have h8 := prefix_at x w hr hrz hN hcells hroom hc
  rw [hwr] at h8
  have h8' : At (machine.run (2 * zeros + 3) c) qSrc (9 + zeros + r)
      (tMark x w zeros r) := At_time h8 (by omega) rfl
  have hsrcval : tMark x w zeros r (9 + zeros + r) = some b := by
    rw [tMark_miss x w (9 + zeros + r) (by omega),
      r_content x w hrz hN (9 + zeros + r) (by omega) (by omega), hb]
  -- 5. read the source, write the new terminator, blank the cell it left
  have h9 : At (machine.run (2 * zeros + 4) c) (clearOf b) (8 + zeros + r)
      (tSrc x w zeros r) :=
    At_time (stepAt_left h8' hsrcval (row_src b) rfl (if_pos (by rw [hwr]))
      (fun i hi => if_neg (by rw [hwr]; omega))) (by omega) (by omega)
  have hterm : tSrc x w zeros r (8 + zeros + r) = some true := by
    rw [show tSrc x w zeros r (8 + zeros + r) = tMark x w zeros r (8 + zeros + r) from
        if_neg (by rw [hwr]; omega),
      tMark_miss x w (8 + zeros + r) (by omega)]
    have h := r_term x w (a := a) (m := m) (zeros := zeros) (r := r) hrz
    rwa [hwr] at h
  have h10 : At (machine.run (2 * zeros + 5) c) (carryOf b) (9 + zeros + r)
      (tClr x w zeros r) :=
    At_time (stepAt_right h9 hterm (row_clear b) rfl (hfit (8 + zeros + r + 1) (by omega))
      (if_pos (by rw [hwr])) (fun i hi => if_neg (by rw [hwr]; omega))) (by omega) (by omega)
  -- 6. carry the bit right to the boundary blank
  have hcont : ∀ j, 9 + zeros + r ≤ j → j < a + m → ∃ d, tClr x w zeros r j = some d := by
    intro j hj1 hj2
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hj
    · refine ⟨true, ?_⟩
      rw [show tClr x w zeros r (9 + zeros + r) = tSrc x w zeros r (9 + zeros + r) from
        if_neg (by rw [hwr]; omega)]
      exact if_pos (by rw [hwr])
    · obtain ⟨d, hd⟩ := content_lt x w (k := j) hj2
      refine ⟨d, ?_⟩
      rw [tClr_miss x w j (by omega) (by rw [hwr]; omega) (by rw [hwr]; omega),
        r_content x w hrz hN j (by omega) (by omega), hd]
  have h11 : At (machine.run (2 * zeros + 5 + (a + m - (9 + zeros + r))) c) (carryOf b)
      (a + m) (tClr x w zeros r) := by
    refine At_time (walk_right (a + m - (9 + zeros + r)) h10 (fun j hj1 hj2 => ?_)
      (hfit _ (by omega))) rfl (by omega)
    obtain ⟨d, hd⟩ := hcont j hj1 (by omega)
    rw [hd]
    exact row_carry b d
  have hblank : tClr x w zeros r (a + m) = none := by
    rw [tClr_miss x w (a + m) (by omega) (by rw [hwr]; omega) (by rw [hwr]; omega),
      r_content x w hrz hN (a + m) (by omega) (by omega)]
    exact content_ge x w le_rfl
  have h12 : At (machine.run (2 * zeros + 6 + (a + m - (9 + zeros + r))) c) (regOf b)
      (a + m + 1) (tClr x w zeros r) :=
    At_time (stepAt_right h11 hblank (row_carry_blank b) rfl (hfit (a + m + 1) (by omega))
      hblank (fun _ _ => rfl)) (by omega) rfl
  -- 7. walk the register to its first blank and append the bit there
  have hreg : ∀ j, a + m + 1 ≤ j → j ≤ a + m + 1 + r →
      tClr x w zeros r j = some (registerBit x w zeros (j - (a + m + 1))) := by
    intro j h1 h2
    rw [tClr_miss x w j (by omega) (by rw [hwr]; omega) (by rw [hwr]; omega)]
    exact r_reg x w hrz hN j h1 h2
  have h13 : At (machine.run (2 * zeros + 7 + r + (a + m - (9 + zeros + r))) c) (regOf b)
      (a + m + 2 + r) (tClr x w zeros r) := by
    refine At_time (walk_right (r + 1) h12 (fun j hj1 hj2 => ?_) (hfit _ (by omega)))
      (by omega) (by omega)
    rw [hreg j (by omega) (by omega)]
    exact row_reg b _
  have hblank4 : tClr x w zeros r (a + m + 2 + r) = none := by
    rw [tClr_miss x w (a + m + 2 + r) (by omega) (by rw [hwr]; omega) (by rw [hwr]; omega)]
    exact r_next_blank x w hrz hN
  have h14 : At (machine.run (2 * zeros + 8 + r + (a + m - (9 + zeros + r))) c) qBackReg
      (a + m + 1 + r) (tPhys x w zeros r b) :=
    At_time (stepAt_left h13 hblank4 (row_reg_blank b) rfl (if_pos rfl)
      (fun i hi => if_neg hi)) (by omega) (by omega)
  -- 8. walk back over the register, the content, and into `qLoop`
  have h15 : At (machine.run (2 * zeros + 9 + 2 * r + (a + m - (9 + zeros + r))) c) qBackReg
      (a + m) (tPhys x w zeros r b) := by
    refine At_time (walk_left (r + 1) (by omega) h14 (fun j hj1 hj2 => ?_)) (by omega)
      (by omega)
    rw [tPhys_miss x w b j (by omega), hreg j (by omega) (by omega)]
    exact row_backreg _
  have hblank' : tPhys x w zeros r b (a + m) = none := by
    rw [tPhys_miss x w b (a + m) (by omega)]
    exact hblank
  have h16 : At (machine.run (2 * zeros + 10 + 2 * r + (a + m - (9 + zeros + r))) c)
      qBackCont (a + m - 1) (tPhys x w zeros r b) :=
    At_time (stepAt_left h15 hblank' rfl rfl hblank' (fun _ _ => rfl)) (by omega) rfl
  have h17 : At (machine.run (2 * zeros + 10 + 2 * r + 2 * (a + m - (9 + zeros + r))) c)
      qBackCont (8 + zeros + r) (tPhys x w zeros r b) := by
    refine At_time (walk_left (a + m - (9 + zeros + r)) (by omega) h16 (fun j hj1 hj2 => ?_))
      (by omega) (by omega)
    obtain ⟨d, hd⟩ := hcont j (by omega) (by omega)
    rw [tPhys_miss x w b j (by omega), hd]
    exact row_backcont d
  have hgap : tPhys x w zeros r b (8 + zeros + r) = none := by
    rw [tPhys_miss x w b (8 + zeros + r) (by omega)]
    exact if_pos (by rw [hwr])
  have h18 : At (machine.run (roundClock (a + m)) c) qLoop (9 + zeros + r)
      (tPhys x w zeros r b) :=
    At_time (stepAt_right h17 hgap rfl rfl (hfit (8 + zeros + r + 1) (by omega)) hgap
      (fun _ _ => rfl)) (by unfold roundClock; omega) (by omega)
  obtain ⟨hq, hh, ht⟩ := h18
  exact ⟨hq, hh, fun i => (ht i).trans (tPhys_eq x w b hrz hN hP hb i.val)⟩

/-- The virtual branch: the source address is the boundary blank itself, so the terminator
does not move and the appended digit is the virtual zero.  `qVa`/`qVb`/`qVc` pad it to the
physical branch's cost, at every `r`. -/
private theorem virt_at {a m B zeros r : Nat} {c : Config stateCount (pairLength a m) B}
    (x : Bitstring a) (w : Bitstring m) (hr : 1 ≤ r) (hrz : r < zeros)
    (hN : 9 + zeros ≤ a + m)
    (hcells : ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false)
    (hroom : a + m + 2 + r < tapeLength (pairLength a m) B) (hV : a + m ≤ 9 + zeros + r)
    (hc : At c qLoop (8 + zeros + walk (a + m) zeros r) (loopNat x w zeros r)) :
    At (machine.run (roundClock (a + m)) c) qLoop (a + m - 1)
      (loopNat x w zeros (r + 1)) := by
  obtain ⟨-, -, -, hvirt⟩ := walk_bounds a m zeros r hN
  obtain ⟨hwr, -⟩ := hvirt hV
  have hfit : ∀ k, k ≤ a + m + 2 + r → k < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    unfold tapeLength pairLength at hroom
    omega
  have h8 := prefix_at x w hr hrz hN hcells hroom hc
  rw [hwr] at h8
  have h8' : At (machine.run (2 * (a + m) - 15 - 2 * r) c) qSrc (a + m)
      (tMark x w zeros r) := At_time h8 (by omega) (by omega)
  have hbound : tMark x w zeros r (a + m) = none := by
    rw [tMark_miss x w (a + m) (by omega),
      r_content x w hrz hN (a + m) (by rw [hwr]; omega) (by omega)]
    exact content_ge x w le_rfl
  have hterm : tMark x w zeros r (a + m - 1) = some true := by
    rw [tMark_miss x w (a + m - 1) (by omega)]
    have h := r_term x w (a := a) (m := m) (zeros := zeros) (r := r) hrz
    rw [hwr, show 8 + zeros + (a + m - 9 - zeros) = a + m - 1 by omega] at h
    exact h
  -- 5. the source is the boundary blank: step back, pad, and enter the register
  have h9 : At (machine.run (2 * (a + m) - 14 - 2 * r) c) qVa (a + m - 1)
      (tMark x w zeros r) :=
    At_time (stepAt_left h8' hbound rfl rfl hbound (fun _ _ => rfl)) (by omega) rfl
  have h10 : At (machine.run (2 * (a + m) - 13 - 2 * r) c) qVb (a + m)
      (tMark x w zeros r) :=
    At_time (stepAt_right h9 hterm rfl rfl (hfit (a + m - 1 + 1) (by omega)) hterm
      (fun _ _ => rfl)) (by omega) (by omega)
  have h11 : At (machine.run (2 * (a + m) - 12 - 2 * r) c) qRegV (a + m + 1)
      (tMark x w zeros r) :=
    At_time (stepAt_right h10 hbound rfl rfl (hfit (a + m + 1) (by omega)) hbound
      (fun _ _ => rfl)) (by omega) rfl
  -- 6. walk the register to its first blank and append the virtual zero
  have hreg : ∀ j, a + m + 1 ≤ j → j ≤ a + m + 1 + r →
      tMark x w zeros r j = some (registerBit x w zeros (j - (a + m + 1))) := by
    intro j h1 h2
    rw [tMark_miss x w j (by omega)]
    exact r_reg x w hrz hN j h1 h2
  have h12 : At (machine.run (2 * (a + m) - 11 - r) c) qRegV (a + m + 2 + r)
      (tMark x w zeros r) := by
    refine At_time (walk_right (r + 1) h11 (fun j hj1 hj2 => ?_) (hfit _ (by omega)))
      (by omega) (by omega)
    rw [hreg j (by omega) (by omega)]
    exact row_regv _
  have hblank4 : tMark x w zeros r (a + m + 2 + r) = none := by
    rw [tMark_miss x w (a + m + 2 + r) (by omega)]
    exact r_next_blank x w hrz hN
  have h13 : At (machine.run (2 * (a + m) - 10 - r) c) qBackRegV (a + m + 1 + r)
      (tVirt x w zeros r) :=
    At_time (stepAt_left h12 hblank4 rfl rfl (if_pos rfl) (fun i hi => if_neg hi))
      (by omega) (by omega)
  -- 7. walk back over the register and re-enter `qLoop` on the unmoved terminator
  have h14 : At (machine.run (2 * (a + m) - 9) c) qBackRegV (a + m) (tVirt x w zeros r) := by
    refine At_time (walk_left (r + 1) (by omega) h13 (fun j hj1 hj2 => ?_)) (by omega)
      (by omega)
    rw [tVirt_miss x w j (by omega), hreg j (by omega) (by omega)]
    exact row_backregv _
  have hbound' : tVirt x w zeros r (a + m) = none := by
    rw [tVirt_miss x w (a + m) (by omega)]
    exact hbound
  have h15 : At (machine.run (2 * (a + m) - 8) c) qVc (a + m - 1) (tVirt x w zeros r) :=
    At_time (stepAt_left h14 hbound' rfl rfl hbound' (fun _ _ => rfl)) (by omega) rfl
  have hterm' : tVirt x w zeros r (a + m - 1) = some true := by
    rw [tVirt_miss x w (a + m - 1) (by omega)]
    exact hterm
  have h16 : At (machine.run (roundClock (a + m)) c) qLoop (a + m - 1)
      (tVirt x w zeros r) :=
    At_time (stepAt_stay h15 hterm' rfl rfl hterm' (fun _ _ => rfl))
      (by unfold roundClock; omega) rfl
  obtain ⟨hq, hh, ht⟩ := h16
  exact ⟨hq, hh, fun i => (ht i).trans (tVirt_eq x w hrz hN hV i.val)⟩

/-- Both source shapes at once: one round out of an arbitrary `r`-instance. -/
private theorem round_at {a m B zeros r : Nat} {c : Config stateCount (pairLength a m) B}
    (x : Bitstring a) (w : Bitstring m) (hr : 1 ≤ r) (hrz : r < zeros)
    (hN : 9 + zeros ≤ a + m)
    (hcells : ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false)
    (hroom : a + m + 2 + r < tapeLength (pairLength a m) B)
    (hc : At c qLoop (8 + zeros + walk (a + m) zeros r) (loopNat x w zeros r)) :
    At (machine.run (roundClock (a + m)) c) qLoop
      (8 + zeros + walk (a + m) zeros (r + 1)) (loopNat x w zeros (r + 1)) := by
  obtain ⟨-, -, hphys, hvirt⟩ := walk_bounds a m zeros r hN
  rcases Nat.lt_or_ge (9 + zeros + r) (a + m) with hP | hV
  · exact At_time (phys_at x w hr hrz hN hcells hroom hP hc) rfl
      (by rw [(hphys hP).2]; omega)
  · exact At_time (virt_at x w hr hrz hN hcells hroom hV hc) rfl
      (by rw [(hvirt hV).2]; omega)

/-- The retagged G2p-d foundation endpoint, in this module's address form: the `r = 2`
instance of the invariant, at a decoded `2 ≤ zeros`. -/
private theorem start_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    At (startConfig B x w) qLoop (8 + zeros + walk (a + m) zeros 2)
      (loopNat x w zeros 2) := by
  obtain ⟨-, hh, ht⟩ :=
    FixedGammaTargetPayloadLoopFoundation.markers_at_deadline (B := B) x w htag hg hz hroom
  refine ⟨rfl, hh, fun i => ?_⟩
  change (FixedGammaTargetPayloadLoopFoundation.machine.run _ _).tape i = _
  rw [ht]
  exact loopTape_eq x w zeros 2 i

/-- `k` rounds out of the retagged G2p-d foundation endpoint. -/
private theorem iterate_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    ∀ k : Nat, 2 + k ≤ zeros →
      At (machine.run (k * roundClock (a + m)) (startConfig B x w)) qLoop
        (8 + zeros + walk (a + m) zeros (2 + k)) (loopNat x w zeros (2 + k)) := by
  obtain ⟨hN, hcells⟩ := gamma_cells x w htag hg
  have hbase : a + m + 3 < tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength
    unfold tapeLength pairLength at hroom
    omega
  intro k
  induction k with
  | zero => intro _; exact At_time (t := 0) (start_at x w htag hg hz hbase) (by omega) rfl
  | succ k ih =>
      intro hk
      have hstep := round_at (r := 2 + k) x w (by omega) (by omega) hN hcells
        (by unfold tapeLength pairLength
            unfold tapeLength pairLength at hroom
            omega)
        (ih (by omega))
      rw [← machine.run_add] at hstep
      exact At_time hstep (by ring) rfl

/-! ### Public execution theorems -/

/-- **The reusable round of this slice.**  On a matching tag, a decoded width, an index `r`
with `1 ≤ r` and work remaining (`r < zeros`), the index's own room
`a + m + 2 + r < tapeLength (pairLength a m) B`, and an **arbitrary** configuration `c`
matching the `r`-instance of the loop invariant `loopTape B x w zeros r`, the machine is after
exactly `roundClock (a + m) = 2 * (a + m) - 7` steps back in `qLoop` on the walking terminator
at head `8 + zeros + walk (a + m) zeros (r + 1)` with the whole tape equal to
`loopTape B x w zeros (r + 1)`: one round of the invariant, from `r` to `r + 1`, in the
physical and the virtual source shape at once.  Unlike the landed `round_step` this quantifies
over `r` and over the incoming configuration, which is exactly what supports the induction
below.  `qLoop` is **not** absorbing, so this is an exact time and not a time from which the
endpoint persists; there is deliberately no converse and no first-arrival direction. -/
theorem round_generic {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hr : 1 ≤ r) (hrz : r < zeros)
    (hroom : a + m + 2 + r < tapeLength (pairLength a m) B)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = 8 + zeros + walk (a + m) zeros r)
    (ht : c.tape = loopTape B x w zeros r) :
    let d := machine.run (roundClock (a + m)) c
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros (r + 1) ∧
      d.tape = loopTape B x w zeros (r + 1) := by
  obtain ⟨hN, hcells⟩ := gamma_cells x w htag hg
  have hc : At c qLoop (8 + zeros + walk (a + m) zeros r) (loopNat x w zeros r) :=
    ⟨hq, hh, fun i => by rw [ht]; exact loopTape_eq x w zeros r i⟩
  obtain ⟨hq', hh', ht'⟩ := round_at x w hr hrz hN hcells hroom hc
  exact ⟨hq', hh', funext fun i => (ht' i).trans (loopTape_eq x w zeros (r + 1) i).symm⟩

/-- **The iteration.**  On a matching tag, a decoded `2 ≤ zeros` and the room every round
assumes, `a + m + 1 + zeros < tapeLength (pairLength a m) B` (equivalently `zeros ≤ a + B`),
running the *same* machine for exactly `k * roundClock (a + m)` steps out of the landed G2p-d
`startConfig` reaches the `r = 2 + k` instance of the loop invariant, for every `k` with
`2 + k ≤ zeros`.  `k = 0` is the retagged foundation endpoint itself; each further `k` is one
more payload digit appended to the target register.  The bound `2 + k ≤ zeros` is the work-remaining
premise of every round performed, and the rounds beyond it — the exhaustion finish — are not
covered here.  (`2 ≤ zeros` is kept as an explicit premise although `2 + k ≤ zeros` already
implies it.)  `qLoop` does not absorb, so these are exact times; there is no converse. -/
theorem rounds_iterate {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B)
    (k : Nat) (hk : 2 + k ≤ zeros) :
    let d := machine.run (k * roundClock (a + m)) (startConfig B x w)
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros (2 + k) ∧
      d.tape = loopTape B x w zeros (2 + k) := by
  obtain ⟨hq, hh, ht⟩ := iterate_at x w htag hg hzeros hroom k hk
  exact ⟨hq, hh, funext fun i => (ht i).trans (loopTape_eq x w zeros (2 + k) i).symm⟩

/-- Register cells of the invariant tape, read through their addresses.  `r ≤ zeros` is what
keeps the register clear of the counter prefix `[8, 7 + r]`. -/
private theorem register_cell {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hN : 9 + zeros ≤ a + m) (hrz : r ≤ zeros) (j : Nat) (hj : j ≤ r)
    (i : Fin (tapeLength (pairLength a m) B)) (hi : i.val = a + m + 1 + j) :
    loopTape B x w zeros r i = some (registerBit x w zeros j) := by
  have hw := walk_bounds a m zeros r hN
  rw [loopTape_eq, hi]
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (show a + m + 1 ≤ a + m + 1 + j ∧ a + m + 1 + j ≤ a + m + 1 + r by omega),
    show a + m + 1 + j - (a + m + 1) = j by omega]

/-- **The complete target register.**  At `k = zeros - 2` the iteration has copied every
remaining payload digit into the register: after exactly
`loopClock (a + m) zeros = (zeros - 2) * roundClock
(a + m)` steps out of the landed G2p-d `startConfig`, the register `[a+m+1, a+m+1+zeros]`
holds all `zeros + 1` digits `registerBit x w zeros j` — by `register_digits` the bootstrap's
leading `true` followed by every payload digit of the decoded width, a truncated payload
contributing virtual zeros.  The room premise allocates every one of those cells, which the
fourth conjunct states, so the cell-by-cell reading is not vacuous.  This is the register's
*content* at an exact time, not a decoded number, not a halting run, and not language
acceptance: the machine sits in the non-absorbing `qLoop` and the exhaustion finish that would
leave it is deferred.  At `zeros = 2` the clock is `0`, so this is literally a restatement of
the retagged foundation endpoint `startConfig`. -/
theorem register_complete {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    let d := machine.run (loopClock (a + m) zeros) (startConfig B x w)
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros zeros ∧
      d.tape = loopTape B x w zeros zeros ∧
      (∀ j : Nat, j ≤ zeros → a + m + 1 + j < tapeLength (pairLength a m) B) ∧
      ∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j → d.tape i = some (registerBit x w zeros j) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  obtain ⟨hq, hh, ht⟩ :=
    rounds_iterate x w htag hg hzeros hroom (zeros - 2) (by omega)
  rw [show 2 + (zeros - 2) = zeros by omega] at hh ht
  refine ⟨hq, hh, ht, fun j hj => by omega, fun j hj i hi => ?_⟩
  have hcell : (machine.run ((zeros - 2) * roundClock (a + m)) (startConfig B x w)).tape i =
      some (registerBit x w zeros j) := by
    rw [ht]
    exact register_cell x w hN le_rfl j hj i hi
  exact hcell

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadIteration
