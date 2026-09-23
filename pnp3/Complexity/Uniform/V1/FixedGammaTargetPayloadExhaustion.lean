import Complexity.Uniform.V1.FixedGammaTargetPayloadIteration

/-!
# The gamma payload exhaustion finish (Part A G2p-f)

No new machine.  The landed G2p-d `FixedGammaTargetPayloadRound.machine` — the fixed
22-state, 66-row table — already carries the stopping rule in its `qCntL`/`qFin` rows;
this module proves what those rows do, and nothing about a new table.
`pnp3/Docs/UniformP_V1.md` carries the long-form design notes.

Write `N = a + m`.  G2p-e left the machine in the `r = zeros` instance of the loop
invariant `loopTape B x w zeros zeros`: the whole gamma zero field `[8, 7 + zeros]` marked
`some true` (one mark per consumed source, so `r = zeros` *is* exhaustion), the terminator
trail `[8 + zeros, 8 + zeros + termWalk N zeros)` blank, the walking terminator at
`8 + zeros + termWalk N zeros`, and the completed target register `[N + 1, N + 1 + zeros]`
holding its `zeros + 1` digits.  Out of that configuration the machine does exactly three
things, and this slice proves all three.

* The stopping rule fires.  `qLoop` leaves the terminator into `qCntL`, `qCntL` scans left
  over the blank trail, and the first non-blank it meets is cell `7 + zeros`.  At every
  index `r < zeros` that cell was an *unconsumed* gamma zero, `some false`, which is the
  branch the rounds took; at `r = zeros` it is a consumed mark, `some true`, and the
  `qCntL` row for `some true` — the row the round slices leave unexecuted over their own
  bounded segments, by direct inspection of the table trace inside their proofs and not by
  any theorem either of them exports — sends the machine into `qFin`.  The rule reads one
  tape cell and nothing else: no width, digit index, address, counter value, proof term,
  advice, or producer mark occurs in control.
* The gamma zero field is restored.  `qFin` walks back left writing `some false` over every
  mark, so cells `[8, 7 + zeros]` end holding exactly what the incoming content tape holds
  there, and the sweep stops of its own accord on the tag cell `7`, which a matching tag
  already holds as `some false`.  That restoration is the semantic point of the finish:
  the field the loop used as a counter is handed back unchanged.  Nothing else is restored,
  and the endpoint tape is **not** `contentTape`: the consumed payload cells stay blank, the
  walking terminator stays where it walked to, and the register stays.  `finishTape` is that
  endpoint, and `finishTape_pins` states both halves — what was restored and what was not.
* The machine halts.  `qFin` on `some false` enters `qDone`, which is absorbing, so the
  endpoint here is a *deadline* and not only an exact time — unlike the round endpoints of
  this loop, which sit in the non-absorbing `qLoop`.  `exhaust_strict` transports it to
  every later time, and in the same breath proves minimality: `qDone` is not reached at any
  strictly earlier time.

`exhaustClock N zeros = termWalk N zeros + zeros + 2` is the exact cost: one step off the
terminator, `termWalk N zeros` blank-trail steps, the step that fires the rule, `zeros - 1`
further unmarking steps, and the halt.  It is neither length-only nor shape-independent: it
depends on the decoded width, and through `termWalk N zeros = walk N zeros zeros` on whether
the payload is physically present — `2 * zeros + 2` when it is, `N - 7` when it is truncated.
That is the one clock of this loop that is not padded flat.  A round had to be, because
`rounds_iterate` adds up a sequence of round costs and an `r`-dependent summand would have
forced the induction to carry a sum; the finish is performed once, so nothing has to add it
up and the `qVa`/`qVb`/`qVc` padding has no counterpart here.  `totalClock N zeros` adds the G2p-e
`loopClock N zeros`; it counts those rounds and this finish, and counts **no** step that
`startConfig` embeds, so it clocks no composed pipeline.

`qDone` is an internal control tag of this phase.  It is `machine.accept` of a machine that
is started here from a phase-local retag of an actual prior run rather than from
`initialConfig` on a raw pair input, so reaching it is neither halting of a composed
machine nor language acceptance, and this module states no `accepts`, no `AcceptsAt`, and no
language membership.

Deferred, and deliberately not claimed: the decrement of the register from `n + 1` digits to
`n`, any reading of the register as a *number* (`registerBit` gives content, not a value, and
on a truncated payload its digits past the content are virtual `false` — nothing says those
are the payload's value or that the register decodes to the intended number), the completion
of the register itself (that is G2p-e's `register_complete`; this slice only preserves it),
every connection to `contentHeader?` or a parsed header value, any pnp4 bridge, the
footprint/budget half of the all-times package (the clamp below is proved, a footprint
theorem is not, so none of the room premises is shown necessary), a converse — nothing says
that `qDone` at `totalClock N zeros`, or any endpoint cell, implies anything about `zeros` —
first arrival measured from `startConfig` rather than from the `r = zeros` configuration
(the G2p-e rounds carry no strictness theorem, so `qDone`-freeness over the round segment is
available only for the literal probe instances), the degenerate widths — `zeros = 0` is
excluded from `exhaust_schedule`, `exhaust_generic` and `exhaust_strict` by their `1 ≤ zeros`
premise, which the tape-shape theorem `finishTape_pins` does not carry, while `zeros = 1`
satisfies those three but is produced by nothing here, `payload_exhausted` needing
`2 ≤ zeros` — and a malformed-gamma branch.  Clock composition, the fixed parser, advice
freedom, `NP` membership, and `ContentVerifierBridge` are out of scope: infrastructure, not
P-vs-NP mainline progress. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion

open PairEncoding
open FixedGammaTargetPayloadLoopFoundation (walk registerBit loopTape)
open FixedGammaTargetPayloadIteration (loopClock)
open FixedGammaTargetPayloadRound (stateCount machine qLoop qCntL qFin qDone qReject
  roundClock startConfig)

/-- Terminator advance once every source has been consumed: the `r = zeros` instance of the
foundation's `walk`, so one cell per *physical* source and no cell per virtual one. -/
def termWalk (N zeros : Nat) : Nat := walk N zeros zeros

/-- Exact cost of the finish out of the `r = zeros` invariant: one step off the walking
terminator, `termWalk N zeros` steps over the blank trail, the step in which the stopping
rule fires, `zeros - 1` further unmarking steps, and the halt.  Unlike `roundClock` this is
**not** length-only: it depends on the decoded width and on the source shape. -/
def exhaustClock (N zeros : Nat) : Nat := termWalk N zeros + zeros + 2

/-- The G2p-e rounds plus this finish, out of the landed G2p-d `startConfig`.  It counts
those steps only: none of the steps `startConfig` embeds is included, so this clocks no
composed pipeline. -/
def totalClock (N zeros : Nat) : Nat := loopClock N zeros + exhaustClock N zeros

/-- The endpoint tape of the finish: the `r = zeros` invariant with the gamma zero counter
field `[8, 7 + zeros]` given back to the incoming content tape.  The terminator trail stays
blank, the walking terminator stays where it walked to, and the completed register
`[N + 1, N + 1 + zeros]` stays; so this is **not** `contentTape`. -/
def finishTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if 8 + zeros ≤ i.val ∧ i.val < 8 + zeros + termWalk (a + m) zeros then none
  else if i.val = 8 + zeros + termWalk (a + m) zeros then some true
  else if a + m + 1 ≤ i.val ∧ i.val ≤ a + m + 1 + zeros then
    some (registerBit x w zeros (i.val - (a + m + 1)))
  else FixedPairContentMarkerErase.contentTape B x w i

/-! ### Machine reuse, clocks, and the endpoint tape -/

/-- The machine executed below is the landed G2p-d round machine, unchanged, together with
the five rows this phase actually runs: leaving the terminator, scanning the blank trail,
the stopping rule, the unmarking sweep, and the halt.  The `qDone` row is absorbing, which
is what makes this phase endpoint a deadline rather than an exact time only. -/
theorem machine_reused :
    machine = FixedGammaTargetPayloadRound.machine ∧ machine.stateCount = 22 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 66 ∧
      machine.start = qLoop ∧ machine.accept = qDone ∧ machine.reject = qReject ∧
      machine.step qLoop (some true) = (qCntL, some true, .left) ∧
      machine.step qCntL none = (qCntL, none, .left) ∧
      machine.step qCntL (some true) = (qFin, some false, .left) ∧
      machine.step qFin (some true) = (qFin, some false, .left) ∧
      machine.step qFin (some false) = (qDone, some false, .stay) ∧
      (∀ s, machine.step qDone s = (qDone, s, .stay)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun s => ?_⟩
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- Closed forms of this slice's clocks and of the terminator advance, and the two source
shapes the finish cost splits into: `2 * zeros + 2` when the payload is physically present,
and `N - 7` when it is truncated.  Under `9 + zeros ≤ N` — the tag, the gamma zero field and
the gamma terminator cell all fitting inside the content — the finish never costs more than
one round.  That guard is a hypothesis of the last conjunct and not prose scaffolding: at
`N = 0`, `zeros = 100` the finish costs `102` while `roundClock 0` truncates to `0`. -/
theorem clock_pins (N zeros : Nat) :
    termWalk N zeros = walk N zeros zeros ∧
      exhaustClock N zeros = termWalk N zeros + zeros + 2 ∧
      totalClock N zeros = loopClock N zeros + exhaustClock N zeros ∧
      totalClock N zeros = (zeros - 2) * roundClock N + exhaustClock N zeros ∧
      (9 + 2 * zeros ≤ N → exhaustClock N zeros = 2 * zeros + 2) ∧
      (9 + zeros ≤ N → N ≤ 9 + 2 * zeros → exhaustClock N zeros = N - 7) ∧
      (9 + zeros ≤ N → exhaustClock N zeros ≤ roundClock N) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · unfold exhaustClock termWalk walk; omega
  · unfold exhaustClock termWalk walk; omega
  · unfold exhaustClock termWalk walk roundClock; omega

/-! ### Address-level execution kernel

The same kernel every phase of this pipeline uses: a configuration is described by its
control, its numeric head, and every tape cell read through its Nat address, and one
`machine.step` row is consumed at a time.  Nothing here is specific to this slice; the
round and iteration modules' own copies are `private`, so it is restated rather than
imported. -/

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

/-! ### Content cells, the gamma field, and the invariant tape -/

private theorem contentTape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) :
    FixedPairContentMarkerErase.contentTape B x w i = content x w i.val := by
  unfold content FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
  split_ifs <;> rfl

/-- Tag cell `7` and the gamma zeros: the whole field `[7, 8 + zeros)` the finish sweeps is
`some false` in the incoming content, which is both what the sweep restores and what stops
it on `7`. -/
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

/-- Nat-addressed form of the foundation's `loopTape` at `r = zeros`. -/
private def loopNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool :=
  if 8 ≤ k ∧ k ≤ 7 + zeros then some true
  else if 8 + zeros ≤ k ∧ k < 8 + zeros + termWalk (a + m) zeros then none
  else if k = 8 + zeros + termWalk (a + m) zeros then some true
  else if a + m + 1 ≤ k ∧ k ≤ a + m + 1 + zeros then
    some (registerBit x w zeros (k - (a + m + 1)))
  else content x w k

private theorem loopTape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) (i : Fin (tapeLength (pairLength a m) B)) :
    loopTape B x w zeros zeros i = loopNat x w zeros i.val := by
  unfold loopTape loopNat termWalk
  split_ifs <;> first | exact contentTape_eq x w i | rfl

private theorem loopNat_term {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    loopNat x w zeros (8 + zeros + termWalk (a + m) zeros) = some true := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

private theorem loopNat_trail {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros k : Nat} (h1 : 8 + zeros ≤ k) (h2 : k < 8 + zeros + termWalk (a + m) zeros) :
    loopNat x w zeros k = none := by
  unfold loopNat
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

private theorem loopNat_mark {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros k : Nat} (h1 : 8 ≤ k) (h2 : k ≤ 7 + zeros) :
    loopNat x w zeros k = some true := by
  unfold loopNat
  rw [if_pos ⟨h1, h2⟩]

/-- Below the gamma field the invariant tape is literal content; `9 + zeros ≤ N` keeps the
register clear of cell `7`. -/
private theorem loopNat_low {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros k : Nat} (hN : 9 + zeros ≤ a + m) (hk : k < 8) :
    loopNat x w zeros k = content x w k := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Nat-addressed form of `finishTape`. -/
private def finalNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool :=
  if 8 + zeros ≤ k ∧ k < 8 + zeros + termWalk (a + m) zeros then none
  else if k = 8 + zeros + termWalk (a + m) zeros then some true
  else if a + m + 1 ≤ k ∧ k ≤ a + m + 1 + zeros then
    some (registerBit x w zeros (k - (a + m + 1)))
  else content x w k

private theorem finishTape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) (i : Fin (tapeLength (pairLength a m) B)) :
    finishTape B x w zeros i = finalNat x w zeros i.val := by
  unfold finishTape finalNat
  split_ifs <;> first | exact contentTape_eq x w i | rfl

/-! ### The finish phase

One induction on the step index carries the whole phase: the control, the head and the tape
at time `s` are closed forms of `s`, so every intermediate time is available and minimality
costs nothing extra.  `finishNat x w zeros s` is the invariant tape with the gamma zero
cells the sweep has already passed given back to the content tape. -/

private def finishState (N zeros s : Nat) : Fin stateCount :=
  if s = 0 then qLoop
  else if s ≤ termWalk N zeros + 1 then qCntL
  else if s ≤ termWalk N zeros + zeros + 1 then qFin
  else qDone

private def finishHead (N zeros s : Nat) : Nat :=
  if s ≤ termWalk N zeros + zeros + 1 then 8 + zeros + termWalk N zeros - s else 7

private def finishNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros s k : Nat) :
    Option Bool :=
  if 8 ≤ k ∧ k < 8 + zeros ∧ 8 + zeros + termWalk (a + m) zeros - k + 1 ≤ s then
    content x w k
  else loopNat x w zeros k

/-- Up to the halt the control is never `qDone`. -/
private theorem finishState_ne_done {N zeros s : Nat}
    (hs : s ≤ termWalk N zeros + zeros + 1) : finishState N zeros s ≠ qDone := by
  unfold finishState
  by_cases h1 : s = 0
  · rw [if_pos h1]; decide
  · rw [if_neg h1]
    by_cases h2 : s ≤ termWalk N zeros + 1
    · rw [if_pos h2]; decide
    · rw [if_neg h2, if_pos hs]; decide

/-- **The finish.**  The stopping rule fires on the first non-blank cell left of the
terminator, the gamma zero field is restored on the way back, and the machine halts in the
absorbing `qDone` on the tag cell `7`. -/
private theorem finish_at {a m B zeros : Nat} {x : Bitstring a} {w : Bitstring m}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 0 < zeros) {c : Config stateCount (pairLength a m) B}
    (hc : At c qLoop (8 + zeros + termWalk (a + m) zeros) (loopNat x w zeros))
    (s : Nat) (hs : s ≤ exhaustClock (a + m) zeros) :
    At (machine.run s c) (finishState (a + m) zeros s) (finishHead (a + m) zeros s)
      (finishNat x w zeros s) := by
  obtain ⟨hN, hfalse⟩ := gamma_cells x w htag hg
  have hwle : 9 + zeros + termWalk (a + m) zeros ≤ a + m := by
    unfold termWalk walk; omega
  have hec : exhaustClock (a + m) zeros = termWalk (a + m) zeros + zeros + 2 := rfl
  rw [hec] at hs
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := hc
      refine ⟨hq.trans ?_, hh.trans ?_, fun i => (ht i).trans ?_⟩
      · simp (disch := omega) only [finishState, if_pos, if_true]
      · simp (disch := omega) only [finishHead, if_pos]
        omega
      · unfold finishNat
        rw [if_neg (by omega)]
  | succ s ih =>
      have ih := ih (by omega)
      have hkeep : ∀ j : Nat, j ≠ 8 + zeros + termWalk (a + m) zeros - s →
          finishNat x w zeros (s + 1) j = finishNat x w zeros s j := by
        intro j hj
        unfold finishNat
        by_cases hc8 : 8 ≤ j ∧ j < 8 + zeros ∧
            8 + zeros + termWalk (a + m) zeros - j + 1 ≤ s
        · rw [if_pos ⟨hc8.1, hc8.2.1, by omega⟩, if_pos hc8]
        · rw [if_neg (by omega), if_neg hc8]
      rcases (show s = 0 ∨ (1 ≤ s ∧ s ≤ termWalk (a + m) zeros) ∨
          s = termWalk (a + m) zeros + 1 ∨
          (termWalk (a + m) zeros + 2 ≤ s ∧ s ≤ termWalk (a + m) zeros + zeros) ∨
          s = termWalk (a + m) zeros + zeros + 1 by omega) with h | h | h | h | h
      · -- Leave the walking terminator.
        subst h
        simp (disch := omega) only [finishState, finishHead, if_pos, if_neg, if_true] at ih ⊢
        have hrd : finishNat x w zeros 0 (8 + zeros + termWalk (a + m) zeros - 0)
            = some true := by
          rw [show 8 + zeros + termWalk (a + m) zeros - 0
            = 8 + zeros + termWalk (a + m) zeros by omega]
          unfold finishNat
          rw [if_neg (by omega)]
          exact loopNat_term x w zeros
        refine stepAt_left ih hrd rfl (by omega) ?_ (fun j hj => hkeep j (by omega))
        rw [show 8 + zeros + termWalk (a + m) zeros - 0
          = 8 + zeros + termWalk (a + m) zeros by omega]
        unfold finishNat
        rw [if_neg (by omega)]
        exact loopNat_term x w zeros
      · -- Scan left over the blank trail of consumed sources.
        simp (disch := omega) only [finishState, finishHead, if_pos, if_neg] at ih ⊢
        have hrd : finishNat x w zeros s (8 + zeros + termWalk (a + m) zeros - s) = none := by
          unfold finishNat
          rw [if_neg (by omega)]
          exact loopNat_trail x w (by omega) (by omega)
        refine stepAt_left ih hrd rfl (by omega) ?_ (fun j hj => hkeep j (by omega))
        unfold finishNat
        rw [if_neg (by omega)]
        exact loopNat_trail x w (by omega) (by omega)
      · -- The stopping rule: the first non-blank is a consumed counter mark, not a zero.
        subst h
        simp (disch := omega) only [finishState, finishHead, if_pos, if_neg] at ih ⊢
        have hrd : finishNat x w zeros (termWalk (a + m) zeros + 1)
            (8 + zeros + termWalk (a + m) zeros - (termWalk (a + m) zeros + 1))
            = some true := by
          unfold finishNat
          rw [if_neg (by omega)]
          exact loopNat_mark x w (by omega) (by omega)
        refine stepAt_left ih hrd rfl (by omega) ?_ (fun j hj => hkeep j (by omega))
        unfold finishNat
        rw [if_pos ⟨by omega, by omega, by omega⟩]
        exact hfalse _ (by omega) (by omega)
      · -- Restore the gamma zero field on the way back.
        simp (disch := omega) only [finishState, finishHead, if_pos, if_neg] at ih ⊢
        have hrd : finishNat x w zeros s (8 + zeros + termWalk (a + m) zeros - s)
            = some true := by
          unfold finishNat
          rw [if_neg (by omega)]
          exact loopNat_mark x w (by omega) (by omega)
        refine stepAt_left ih hrd rfl (by omega) ?_ (fun j hj => hkeep j (by omega))
        unfold finishNat
        rw [if_pos ⟨by omega, by omega, by omega⟩]
        exact hfalse _ (by omega) (by omega)
      · -- Halt on the tag cell `7`, which a matching tag already holds as `some false`.
        subst h
        simp (disch := omega) only [finishState, finishHead, if_pos, if_neg] at ih ⊢
        have hhd : 8 + zeros + termWalk (a + m) zeros -
            (termWalk (a + m) zeros + zeros + 1) = 7 := by omega
        rw [hhd] at ih
        have hrd : finishNat x w zeros (termWalk (a + m) zeros + zeros + 1) 7
            = some false := by
          unfold finishNat
          rw [if_neg (by omega), loopNat_low x w hN (by omega)]
          exact hfalse 7 le_rfl (by omega)
        refine stepAt_stay ih hrd rfl rfl ?_ (fun j hj => hkeep j (by omega))
        unfold finishNat
        rw [if_neg (by omega), loopNat_low x w hN (by omega)]
        exact hfalse 7 le_rfl (by omega)

/-- At the halt every gamma zero cell has been passed, so the time-indexed tape is the
endpoint tape. -/
private theorem finishNat_end {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hN : 9 + zeros ≤ a + m) (k : Nat) :
    finishNat x w zeros (exhaustClock (a + m) zeros) k = finalNat x w zeros k := by
  have hec : exhaustClock (a + m) zeros = termWalk (a + m) zeros + zeros + 2 := rfl
  unfold finishNat finalNat
  rw [hec]
  by_cases hc : 8 ≤ k ∧ k < 8 + zeros
  · rw [if_pos ⟨hc.1, hc.2, by omega⟩, if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  · rw [if_neg (by omega)]
    unfold loopNat
    split_ifs <;> first | rfl | omega

private theorem finishState_end (N zeros : Nat) :
    finishState N zeros (exhaustClock N zeros) = qDone := by
  unfold finishState exhaustClock
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem finishHead_end (N zeros : Nat) : finishHead N zeros (exhaustClock N zeros) = 7 := by
  unfold finishHead exhaustClock
  rw [if_neg (by omega)]

/-- Off the gamma zero field the endpoint tape is the incoming invariant tape, cell for
cell: the finish rewrites the counter and nothing else. -/
private theorem loopNat_eq_finalNat {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros k : Nat} (h : k < 8 ∨ 8 + zeros ≤ k) :
    loopNat x w zeros k = finalNat x w zeros k := by
  unfold loopNat finalNat
  rw [if_neg (by omega)]

private theorem finalNat_gamma {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros k : Nat} (hN : 9 + zeros ≤ a + m) (h2 : k < 8 + zeros) :
    finalNat x w zeros k = content x w k := by
  unfold finalNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem finalNat_trail {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros k : Nat} (h1 : 8 + zeros ≤ k) (h2 : k < 8 + zeros + termWalk (a + m) zeros) :
    finalNat x w zeros k = none := by
  unfold finalNat
  rw [if_pos ⟨h1, h2⟩]

private theorem finalNat_term {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    finalNat x w zeros (8 + zeros + termWalk (a + m) zeros) = some true := by
  unfold finalNat
  rw [if_neg (by omega), if_pos rfl]

private theorem finalNat_register {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros j : Nat} (hN : 9 + zeros ≤ a + m) (hj : j ≤ zeros) :
    finalNat x w zeros (a + m + 1 + j) = some (registerBit x w zeros j) := by
  have hw : 9 + zeros + termWalk (a + m) zeros ≤ a + m := by unfold termWalk walk; omega
  unfold finalNat
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show a + m + 1 + j - (a + m + 1) = j by omega]

/-! ### Public execution theorems -/

/-- **What the finish restores, and what it does not.**  On the gamma zero field
`[7, 8 + zeros)` — the counter the loop consumed, together with the tag cell `7` the sweep
stops on — the endpoint tape is back to the incoming content tape, and there it reads
`some false`.  Everywhere else it is the incoming `r = zeros` invariant tape, unchanged:
the consumed sources stay blank, the walking terminator stays at
`8 + zeros + termWalk (a + m) zeros`, and the completed register `[a+m+1, a+m+1+zeros]`
survives holding its `zeros + 1` digits.  So this endpoint is **not** `contentTape`, and
nothing here claims it is.  The register conjunct is a statement about cells that are
allocated only when the room premise of `payload_exhausted` holds; on its own it is
vacuous for indices past the tape. -/
theorem finishTape_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (∀ i : Fin (tapeLength (pairLength a m) B), 7 ≤ i.val → i.val < 8 + zeros →
        finishTape B x w zeros i = FixedPairContentMarkerErase.contentTape B x w i ∧
          finishTape B x w zeros i = some false) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val < 8 ∨ 8 + zeros ≤ i.val →
        finishTape B x w zeros i = loopTape B x w zeros zeros i) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), 8 + zeros ≤ i.val →
        i.val < 8 + zeros + termWalk (a + m) zeros → finishTape B x w zeros i = none) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = 8 + zeros + termWalk (a + m) zeros →
        finishTape B x w zeros i = some true) ∧
      (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j → finishTape B x w zeros i = some (registerBit x w zeros j)) := by
  obtain ⟨hN, hfalse⟩ := gamma_cells x w htag hg
  refine ⟨fun i h1 h2 => ⟨?_, ?_⟩, fun i h => ?_, fun i h1 h2 => ?_, fun i h => ?_,
    fun j hj i hi => ?_⟩
  · rw [finishTape_eq, finalNat_gamma x w hN h2, contentTape_eq]
  · rw [finishTape_eq, finalNat_gamma x w hN h2]
    exact hfalse i.val h1 h2
  · rw [finishTape_eq, loopTape_eq, loopNat_eq_finalNat x w h]
  · rw [finishTape_eq]
    exact finalNat_trail x w h1 h2
  · rw [finishTape_eq, h]
    exact finalNat_term x w zeros
  · rw [finishTape_eq, hi]
    exact finalNat_register x w hN hj

/-- **The control schedule of the finish.**  Out of an arbitrary configuration matching the
`r = zeros` instance of the loop invariant, the head walks monotonically left from the
walking terminator to the tag cell `7`, and the control is `qLoop` for one step, `qCntL`
while the blank trail is scanned, and `qFin` from the step in which the stopping rule fires
until the halt.  `qCntZ`, `qCntMark`, `qSrc` and every register/carry state of the round are
never entered, so no source is consumed and no digit is appended: together with
`exhaust_generic` these conjuncts name the control at *every* time up to and including the
halt, so there is no time left at which another state could occur.  The `t = 0` conjunct is
the incoming hypothesis `hq` restated at `machine.run 0 c`. -/
theorem exhaust_schedule {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 1 ≤ zeros) (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = 8 + zeros + termWalk (a + m) zeros)
    (ht : c.tape = loopTape B x w zeros zeros) :
    (∀ t, t ≤ termWalk (a + m) zeros + zeros + 1 →
        (machine.run t c).head.val = 8 + zeros + termWalk (a + m) zeros - t) ∧
      (machine.run 0 c).state = qLoop ∧
      (∀ t, 1 ≤ t → t ≤ termWalk (a + m) zeros + 1 → (machine.run t c).state = qCntL) ∧
      (∀ t, termWalk (a + m) zeros + 2 ≤ t → t ≤ termWalk (a + m) zeros + zeros + 1 →
        (machine.run t c).state = qFin) := by
  have hc : At c qLoop (8 + zeros + termWalk (a + m) zeros) (loopNat x w zeros) :=
    ⟨hq, hh, fun i => by rw [ht]; exact loopTape_eq x w zeros i⟩
  refine ⟨fun t htle => ?_, hq, fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
  · have h := (finish_at htag hg hz hc t (by unfold exhaustClock; omega)).2.1
    rw [h]
    unfold finishHead
    rw [if_pos htle]
  · have h := (finish_at htag hg hz hc t (by unfold exhaustClock; omega)).1
    rw [h]
    unfold finishState
    rw [if_neg (by omega), if_pos h2]
  · have h := (finish_at htag hg hz hc t (by unfold exhaustClock; omega)).1
    rw [h]
    unfold finishState
    rw [if_neg (by omega), if_neg (by omega), if_pos h2]

/-- **The exhaustion finish, out of an arbitrary `r = zeros` configuration.**  On a matching
tag, a decoded width `1 ≤ zeros`, and a configuration whose three projections are the
`r = zeros` instance of the loop invariant — control `qLoop`, head on the walking terminator
`8 + zeros + termWalk (a + m) zeros`, tape `loopTape B x w zeros zeros` — the machine is
after exactly `exhaustClock (a + m) zeros = termWalk (a + m) zeros + zeros + 2` steps in
`qDone` on the tag cell `7`, with the whole tape equal to `finishTape B x w zeros`.  There
is **no room premise**: the finish only ever moves left from a head the hypothesis already
places inside the tape, so it touches no cell the incoming configuration does not have.
`qDone` is an internal control tag of this phase; this is neither halting of a composed
machine nor language acceptance, and no converse is claimed. -/
theorem exhaust_generic {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 1 ≤ zeros) (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = 8 + zeros + termWalk (a + m) zeros)
    (ht : c.tape = loopTape B x w zeros zeros) :
    let d := machine.run (exhaustClock (a + m) zeros) c
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = finishTape B x w zeros := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  have hc : At c qLoop (8 + zeros + termWalk (a + m) zeros) (loopNat x w zeros) :=
    ⟨hq, hh, fun i => by rw [ht]; exact loopTape_eq x w zeros i⟩
  obtain ⟨hq', hh', ht'⟩ := finish_at htag hg hz hc (exhaustClock (a + m) zeros) le_rfl
  exact ⟨hq'.trans (finishState_end (a + m) zeros), hh'.trans (finishHead_end (a + m) zeros),
    funext fun i =>
      (ht' i).trans ((finishNat_end x w hN i.val).trans (finishTape_eq x w zeros i).symm)⟩

/-- **The finish endpoint is a deadline, and `exhaustClock` is its first arrival.**  Because
`qDone` absorbs — which `qLoop`, where both round endpoints of this loop sit, does not — the
endpoint of `exhaust_generic` holds at *every* later time and may be transported forward.
Minimality is the other direction: at every
strictly earlier time the control is one of `qLoop`, `qCntL`, `qFin`, so `exhaustClock` is
the *first* time `qDone` is entered out of this configuration.  Minimality is measured from
the `r = zeros` configuration, not from `startConfig`: the G2p-e rounds carry no strictness
theorem, so nothing here says `qDone` is unreached during them. -/
theorem exhaust_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 1 ≤ zeros) (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = 8 + zeros + termWalk (a + m) zeros)
    (ht : c.tape = loopTape B x w zeros zeros) :
    (∀ t, t < exhaustClock (a + m) zeros → (machine.run t c).state ≠ qDone) ∧
      (∀ t, exhaustClock (a + m) zeros ≤ t →
        machine.run t c = machine.run (exhaustClock (a + m) zeros) c) ∧
      (∀ t, exhaustClock (a + m) zeros ≤ t →
        (machine.run t c).state = qDone ∧ (machine.run t c).head.val = 7 ∧
          (machine.run t c).tape = finishTape B x w zeros) := by
  have hc : At c qLoop (8 + zeros + termWalk (a + m) zeros) (loopNat x w zeros) :=
    ⟨hq, hh, fun i => by rw [ht]; exact loopTape_eq x w zeros i⟩
  obtain ⟨hdq, hdh, hdt⟩ := exhaust_generic x w htag hg hz c hq hh ht
  have hclamp : ∀ t, exhaustClock (a + m) zeros ≤ t →
      machine.run t c = machine.run (exhaustClock (a + m) zeros) c := by
    intro t hge
    rw [show t = exhaustClock (a + m) zeros + (t - exhaustClock (a + m) zeros) by omega,
      machine.run_add]
    exact machine.run_accept _ hdq _
  refine ⟨fun t htlt => ?_, hclamp, fun t hge => ?_⟩
  · rw [(finish_at htag hg hz hc t (by omega)).1]
    exact finishState_ne_done (by unfold exhaustClock at htlt; omega)
  · rw [hclamp t hge]
    exact ⟨hdq, hdh, hdt⟩

/-- **The concrete exact run: the gamma payload loop runs out of sources and stops.**  On a
matching tag, a decoded `2 ≤ zeros`, and the G2p-e iteration room
`a + m + 1 + zeros < tapeLength (pairLength a m) B` (equivalently `zeros ≤ a + B`), the
landed G2p-d round machine run out of the landed G2p-d `startConfig` for exactly
`totalClock (a + m) zeros = loopClock (a + m) zeros + exhaustClock (a + m) zeros` steps is
in `qDone` on the tag cell `7`, its tape is `finishTape B x w zeros`, the gamma zero field
`[7, 8 + zeros)` has been handed back to the incoming content tape, and the endpoint
persists at every later time.  The register conjunct is **preservation, not completion**:
that `[a+m+1, a+m+1+zeros]` holds the `zeros + 1` digits `registerBit x w zeros j` is
G2p-e's `register_complete`, and all this slice adds is that the finish carries it through
unchanged.  Nothing here decodes those digits, and where the payload is truncated the digits
past it are `registerBit`'s virtual `false`; no theorem says a virtual `false` is the
payload's value or that the register decodes to any intended number.  The room premise is inherited from the iteration —
the finish itself needs none — and it is sufficient, not shown necessary.  `totalClock`
counts those rounds and this finish only: not one step that `startConfig` embeds, so it
clocks no composed pipeline.  `qDone` is an internal control tag: this is neither halting of
a composed machine nor language acceptance, and nothing here decodes the register into a
number or mentions `contentHeader?`. -/
theorem payload_exhausted {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    let d := machine.run (totalClock (a + m) zeros) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = finishTape B x w zeros ∧
      (∀ j : Nat, j ≤ zeros → a + m + 1 + j < tapeLength (pairLength a m) B) ∧
      (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j → d.tape i = some (registerBit x w zeros j)) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), 7 ≤ i.val → i.val < 8 + zeros →
        d.tape i = FixedPairContentMarkerErase.contentTape B x w i ∧
          d.tape i = some false) ∧
      (∀ t, totalClock (a + m) zeros ≤ t → machine.run t (startConfig B x w) = d) := by
  obtain ⟨hq, hh, ht, -, -⟩ :=
    FixedGammaTargetPayloadIteration.register_complete x w htag hg hzeros hroom
  have hsplit : machine.run (totalClock (a + m) zeros) (startConfig B x w)
      = machine.run (exhaustClock (a + m) zeros)
        (machine.run (loopClock (a + m) zeros) (startConfig B x w)) :=
    machine.run_add _ _ _
  obtain ⟨hdq, hdh, hdt⟩ :=
    exhaust_generic x w htag hg (by omega)
      (machine.run (loopClock (a + m) zeros) (startConfig B x w)) hq hh ht
  obtain ⟨-, hclamp, -⟩ :=
    exhaust_strict x w htag hg (by omega)
      (machine.run (loopClock (a + m) zeros) (startConfig B x w)) hq hh ht
  obtain ⟨hpin1, -, -, -, hpin5⟩ := finishTape_pins (B := B) x w htag hg
  refine ⟨hsplit ▸ hdq, hsplit ▸ hdh, hsplit ▸ hdt, fun j hj => by omega,
    fun j hj i hi => ?_, fun i h1 h2 => ?_, fun t hge => ?_⟩
  · rw [hsplit, hdt]
    exact hpin5 j hj i hi
  · rw [hsplit, hdt]
    exact hpin1 i h1 h2
  · rw [hsplit, show t = loopClock (a + m) zeros + (t - loopClock (a + m) zeros) by
      unfold totalClock at hge; omega, machine.run_add]
    exact hclamp _ (by unfold totalClock at hge; omega)

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion
