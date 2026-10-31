import Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownBridge

/-!
# The countdown drains on the parsed target (Part A G2v)

The pnp3 G2u slice `FixedGammaTargetUnaryCountdownIteration` landed the whole drain — entry,
`v` rounds, exhaustion — out of the landed phase-local `startConfig`, and explicitly deferred
exactly one thing to pnp4: a *value*.  Its `register_drained` is stated for a `v` that is
universally quantified — "a `v` whose digit `zeros - j` is G2q's decremented register digit `j` at
every `j ≤ zeros` and which has no digit above `zeros`" — and no theorem of that module produces
such a `v`; its own surface probes supply the literals `24` and `3` **by hand**.  This module is
that missing value and nothing else, exactly as G2t was for G2s-a's single round: on a decoded
content header the G2r bridge already proves both digit facts for the decoded target `n`, so
`v := n` is the instantiation, and the phase's whole countdown is then a countdown of the *actual
parsed target*.  **No new machine, no new state and no new table row**: every step below is G2s-a's
fixed 11-state, 33-row table, run for longer.  Write `N = a + m` and `d = borrow x w zeros`.

```text
entry   register cell  N+1+j      holds  n.testBit (zeros - j)    j ≤ zeros
exit    register cell  N+1+j      holds  some false               j ≤ zeros
exit    lane cells     [N+3+zeros, N+3+zeros+n)   hold  some true
exit    lane cells     N+3+zeros+n  and beyond    are blank
```

Four theorems, all one-way, all out of a decoded header or a successful dependent parse.

* `countdown_width_eq_gammaZeros` identifies the **physical** gamma width that
  `FixedContentGammaTerminator.gammaZeros?` reads off the word with the **canonical** width
  `gammaZeros n = bitLength (n + 1) - 1` that the pnp4 layout convention computes from the decoded
  target.  The proof is arithmetic on the adjacent-power bounds `2 ^ zeros ≤ n + 1 < 2 ^ (zeros+1)`
  that G2p-g exports and on the same bounds for `bitLength (n + 1)`, which pin the exponent
  uniquely.  Nothing is extracted from a proof and no decoder is executed: both widths are already
  *functions* of data, and this theorem says the two functions agree on a decoded header.
* `countdown_drain_cap_iff_machine_room` states the cap and the room, and the exact direction of
  their relationship.  The lane cap `n ≤ F` is explicit; `gammaZeros n + 2 + F ≤ a + B` is G2u's
  `lane_room` premise once the width is recovered, which is the same condition as the physical form
  `zeros + 2 + F ≤ a + B` and as the tape form `a+m+3+zeros+F < tapeLength (pairLength a m) B`.
  Cap and room together **imply** G2t's first-round room `2 * (n + 1) < 2 ^ (a + B)`.  The converse
  is **not** stated and is false in general: G2t's room allocates the *first* tally cell only, and
  `probe_countdown_drain_room_strictly_stronger` exhibits a literal split where G2t's room holds
  while this one fails at every `F` the cap admits.
* `countdown_drained_header_value` carries the header through to the actual G2u run.  The landed
  `FixedGammaTargetUnaryCountdown.startConfig` — a retag of an actual G2q run at G2q's own
  length-only `deadline (a + m)` — *enters* `qLoop` on the separator blank `N + 2 + zeros` after
  exactly `d + 2` steps with the register holding the decoded target `n`, and after exactly
  `fullClock zeros d n` steps is in the absorbing `qDone` on that same cell with every register cell
  `some false`, exactly `n` marks in `[N+3+zeros, N+3+zeros+n)` and blanks beyond.  The whole-tape
  equality `loopTape B x w zeros 0 n` pins every index; the cell conjuncts read the same endpoint
  back at the addresses the next phase will care about.
* `countdown_drained_parsed_target` replaces the header by a successful dependent parse
  `contentInput? codec (Fin.append x w) = some pr` for an **arbitrary** codec, with no monotonicity
  and no injectivity premise.  It exports `pr.2.n = pr.1` — the target the parsed `PrefixInput`
  carries, which is what `ContentAccepts` reads, is the outer Sigma index and the target the
  *decoder* returns — and then the same endpoint at that actual parsed target.

## Every hypothesis, in full

* `countdown_width_eq_gammaZeros`: **two**, the decoded header and the decoded width `hg`, which is
  what ties the statement's otherwise free `zeros` to that header.  No tag, no budget, no cap and no
  machine.
* `countdown_drain_cap_iff_machine_room`: the same **two**.  `B` and `F` are universally quantified
  and free, which is exactly why a decoded header implies neither the cap nor the room.
* `countdown_drained_header_value`: **five** — the matching tag, the decoded header, `3 ≤ n`, the
  cap `n ≤ F`, and the room `gammaZeros n + 2 + F ≤ a + B`.  `3 ≤ n` reaches `2 ≤ zeros`, the width
  premise G2u inherits from G2q and thence from `payload_exhausted`; G2u needs no positivity, so
  unlike G2t's use of it nothing here needs `1 ≤ n`.  The tag is what `register_drained` asks for,
  and it uses it twice over: to identify the incoming G2q endpoint, and to know that the cells at
  and past the boundary blank are blank on the incoming finish tape.  The configuration is **not** a
  hypothesis and is not arbitrary: it is the landed `startConfig B x w`, so the incoming tape is the
  one the earlier phases actually produce from `Fin.append x w`.
* `countdown_drained_parsed_target`: **five** — the matching tag, the successful parse,
  `3 ≤ pr.2.n`, the cap at `pr.2.n` and the room at `pr.2.n`.  The tag is carried, not derived from
  the parse; the header is a *conclusion*, obtained through `contentInput?_target_eq_contentHeader`,
  which is also what gives `pr.2.n = pr.1`.

## The numbers, and which of them is on the tape

This slice introduces no new value: it adds a second *name* for the gamma width and then proves the
two names equal.  `zeros = gammaZeros n` is that gamma
width, `n + 1` the encoded gamma integer, `consumed = 2 * zeros + 1` and the window length
`treeMCSPPrefixM codec pr.1` stay length conventions, and `n` is what the entry register holds and
what the lane counts out.  The endpoint register holds **zero** — the drain clears it — and no
conclusion here puts a convention length in a register cell.  The `n` cells of the lane are
**marks**: the tally is exactly as long as the decoded target, which this module states as a cell
predicate, not as a claim that the machine has re-encoded `n` in unary anywhere.

## What is not claimed

The **fence**.  `F` is a parameter of every statement below, nothing instantiates it here, and no
cell of the tape is a cutoff: `loopTape` is blank at `N + 3 + zeros + F`, an installed `some false`
there is not a `loopTape`, and nothing here is evidence that any of these theorems survives one.
The room is a joint condition on the parsed target and the budget, carried and never derived —
`B` is a free budget — and it is **sufficient and used, never shown necessary**: no footprint or
budget theorem exists on the pnp3 side, and G2u's own `check_below_room_drain_probe` exhibits a
budget where the condition fails while the canonical unfenced drain still completes.  A target too
large for the budget still runs `qRunEnd` off the end of the tape and sticks there, which is a
timeout and therefore neither verdict; nothing here excludes that.

**First arrival.**  `qDone` absorbs, so the all-times conjunct is persistence and nothing more: no
theorem here says `qDone` is entered for the *first* time at `fullClock zeros d n`, and none is
proved.  **Every converse**: nothing derives a valid header, a width, `2 ≤ zeros`, the cap, the
room, the borrow length or a parsed target from `qDone`, from the endpoint tape, or from a mark
found in the lane; in particular no endpoint-to-parse direction is stated.

Everything G2t and G2r already disclaimed still holds.  No machine here executes `contentHeader?`,
`contentInput?`, the strict parser or any decoder: `n` and `pr` occur only in the *statements*, and
every row of the fixed table is a function of the current state and the one symbol under the head —
no width, digit index, register address, mark count, clock, counter, advice, producer mark or proof
term occurs in any row.
Nothing is computed from a proof; no `Nat.find`, choice, or decidability instance supplies a runtime
value, and `gammaZeros` is an ordinary arithmetic function of a number, not an extraction from the
existential above.  No **malformed-gamma branch**: G2q characterises no non-`qDone` endpoint to
route, and no theorem of G2s-a or G2u characterises when its `qReject` is reached.  No **degenerate
width**: `zeros ≤ 1` is out of reach of the machine theorems, since `3 ≤ n` forces the `2 ≤ zeros`
that G2u needs, while the two parser-side theorems carry no width premise and cover it.  The gamma
**leading-digit convention is not restored and must not be read back in** — G2q destroyed it, each
round destroyed it further, and the endpoint register is all `some false`.  `fullClock` counts the
steps of this phase alone — not one of the steps `startConfig` embeds, and no clock of any earlier
phase — so nothing here composes a pipeline clock or states a raw-input deadline.  `qDone` is an
internal control tag of a phase whose `startConfig` retags an *actual* prior run rather than
`initialConfig` on a raw pair input: reaching it is phase-local acceptance, neither halting of a
composed machine nor language acceptance.  This module states no `accepts`, no `AcceptsAt`, no
`ContentAccepts` and no language membership; the fixed parser, the checks, advice freedom, `NP`
membership, `ContentVerifierBridge` and P-vs-NP mainline progress are out of scope.

**Progress classification (AGENTS.md): Infrastructure.**
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-! ### The canonical width equals the physical one -/

/-- **The physical gamma width is the canonical one.**  `FixedContentGammaTerminator.gammaZeros?`
counts the leading zeros the *word* physically carries; `gammaZeros n = bitLength (n + 1) - 1` is
the width the pnp4 layout convention computes from a *number*.  On a decoded header they agree, and
the two adjacent-power bounds hold at that common value.

The proof is exponent uniqueness and nothing else: G2p-g exports `2 ^ zeros ≤ n + 1 < 2 ^ (zeros+1)`
for the physical width, `bitLength` satisfies the same two bounds at `gammaZeros n`, and no natural
lies in two such windows.  Both widths are functions of data that already exist, so this is an
equation between two computed quantities — nothing is extracted from a proof, and no decoder is
executed.  No tag, no budget and no machine occurs. -/
theorem countdown_width_eq_gammaZeros {a m n consumed zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed))
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    zeros = gammaZeros n ∧ 2 ^ gammaZeros n ≤ n + 1 ∧ n + 1 < 2 ^ (gammaZeros n + 1) := by
  obtain ⟨zeros', hg', -, hlo, hhi, -, -, -⟩ := decremented_register_digits x w hheader
  rw [show zeros' = zeros from Option.some.inj (hg'.symm.trans hg)] at hlo hhi
  have hpos : 0 < bitLength (n + 1) := bitLength_pos_of_pos (Nat.succ_pos n)
  have hglo : 2 ^ gammaZeros n ≤ n + 1 := by
    unfold gammaZeros
    exact two_pow_bitLength_pred_le (a := n + 1) (Nat.succ_pos n)
  have hghi : n + 1 < 2 ^ (gammaZeros n + 1) := by
    rw [show gammaZeros n + 1 = bitLength (n + 1) by unfold gammaZeros; omega]
    exact nat_lt_two_pow_bitLength (n + 1)
  refine ⟨?_, hglo, hghi⟩
  rcases Nat.lt_trichotomy zeros (gammaZeros n) with h | h | h
  · have hp : (2 : Nat) ^ (zeros + 1) ≤ 2 ^ gammaZeros n :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · exact h
  · have hp : (2 : Nat) ^ (gammaZeros n + 1) ≤ 2 ^ zeros :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ### The lane cap and the room it needs -/

/-- **The cap, the room, and the one direction that holds.**  G2u's drain lays one mark per round,
so it allocates the whole lane `[N+3+zeros, N+3+zeros+F)` rather than its first cell: its premises
are an explicit cap `v ≤ F` on how many marks may be laid and the budget condition
`zeros + 2 + F ≤ a + B`.  On a decoded header the cap reads `n ≤ F`, the budget condition may be
written at the canonical width `gammaZeros n` — the first conjunct is what makes the two forms one
condition — and it is the same condition as the tape form
`a+m+3+zeros+F < tapeLength (pairLength a m) B`.

The last conjunct is the **only** relationship claimed between this room and G2t's: cap and room
together imply `2 * (n + 1) < 2 ^ (a + B)`, the first-round room.  The converse is not stated, and
is false in general — G2t's room reserves the first tally cell and says nothing about the twelfth;
`probe_countdown_drain_room_strictly_stronger` exhibits a literal split where G2t's room holds and
this one fails at every `F` the cap admits.

`B` and `F` are universally quantified and free, which is exactly why a decoded header implies
none of this: the cap is a joint condition on the parsed target and the lane budget, the room a
joint condition on both and the tape budget, and both are carried by the machine theorems below and
never derived.  Both are sufficient only — no footprint theorem on the pnp3 side shows either
necessary, and G2u's `check_below_room_drain_probe` exhibits a budget where the room fails while
the canonical unfenced drain still completes. -/
theorem countdown_drain_cap_iff_machine_room {a m B n consumed zeros F : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed))
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    zeros = gammaZeros n ∧
      ((n ≤ F ∧ gammaZeros n + 2 + F ≤ a + B) ↔ (n ≤ F ∧ zeros + 2 + F ≤ a + B)) ∧
      (zeros + 2 + F ≤ a + B ↔
        a + m + 3 + zeros + F < tapeLength (PairEncoding.pairLength a m) B) ∧
      (n ≤ F ∧ gammaZeros n + 2 + F ≤ a + B → 2 * (n + 1) < 2 ^ (a + B)) := by
  have hzg : zeros = gammaZeros n := (countdown_width_eq_gammaZeros x w hheader hg).1
  refine ⟨hzg, by rw [hzg], (FixedGammaTargetUnaryCountdown.room_iff a m B zeros F).1.symm,
    fun h => ?_⟩
  exact (countdown_room_iff_target_bound (B := B) x w hheader hg).1.2 (by omega)

/-! ### The machine side: the whole countdown drains on the parsed target -/

/-- **The whole countdown, on the decoded header's target.**  On a matching tag, a decoded header
with `3 ≤ n`, the lane cap `n ≤ F` and the room `gammaZeros n + 2 + F ≤ a + B`, the landed G2u
drain runs out of the landed `startConfig`: the machine *enters* `qLoop` on the separator blank
`a + m + 2 + zeros` after exactly `d + 2` steps with tape `loopTape B x w zeros n 0`, whose register
`[a+m+1, a+m+1+zeros]` holds the decoded target `n` cell by cell, and after exactly
`fullClock zeros d n` steps is in the **absorbing** `qDone` on that same cell with tape
`loopTape B x w zeros 0 n`: every register cell `some false`, exactly `n` marks filling
`[a+m+3+zeros, a+m+3+zeros+n)`, and every cell from `a+m+3+zeros+n` on blank.  The endpoint
persists at every later time.

`3 ≤ n` reaches `2 ≤ zeros`, the width premise G2u inherits; G2u's drain needs no positivity, so
unlike G2t nothing here uses `1 ≤ n`.  The cap and the room are carried, not derived, and are
sufficient only (`countdown_drain_cap_iff_machine_room`); together they imply G2t's first-round
room, which is exported here as a conjunct, and nothing claims the reverse.  `F` stays a parameter:
no cutoff is laid at `a+m+3+zeros+F`, and the tape is the unchanged canonical `loopTape`, blank
there.  The persistence conjunct is persistence and **not** first arrival — `qDone` absorbs, and no
conjunct says it is entered for the first time at this clock.  Nothing decodes the register on the
tape, no machine executes `contentHeader?`, the marks are marks rather than a value in unary, the
gamma leading-digit convention stays destroyed, `fullClock` counts this phase's steps alone, and
`qDone` is an internal control tag rather than halting or language acceptance. -/
theorem countdown_drained_header_value {a m B n consumed F : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) (hn : 3 ≤ n)
    (hcap : n ≤ F) (hroom : gammaZeros n + 2 + F ≤ a + B) :
    ∃ zeros, zeros = gammaZeros n ∧ 2 ≤ zeros ∧ consumed = 2 * zeros + 1 ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
      2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      2 * (n + 1) < 2 ^ (a + B) ∧
      a + m + 3 + zeros + F < tapeLength (PairEncoding.pairLength a m) B ∧
      let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
      let c0 := FixedGammaTargetUnaryCountdown.machine.run (d + 2)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      let e := FixedGammaTargetUnaryCountdown.machine.run
        (FixedGammaTargetUnaryCountdownIteration.fullClock zeros d n)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      d ≤ zeros ∧ c0.state = FixedGammaTargetUnaryCountdown.qLoop ∧
        c0.head.val = a + m + 2 + zeros ∧
        c0.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros n 0 ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → c0.tape i = some (n.testBit (zeros - j))) ∧
        e.state = FixedGammaTargetUnaryCountdown.qDone ∧
        e.head.val = a + m + 2 + zeros ∧
        e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros 0 n ∧
        (∀ t, FixedGammaTargetUnaryCountdownIteration.fullClock zeros d n ≤ t →
          FixedGammaTargetUnaryCountdown.machine.run t
            (FixedGammaTargetUnaryCountdown.startConfig B x w) = e) ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → e.tape i = some false) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 3 + zeros ≤ i.val →
          i.val < a + m + 3 + zeros + n → e.tape i = some true) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          a + m + 3 + zeros + n ≤ i.val → e.tape i = none) := by
  obtain ⟨zeros, hg, hconsumed, hlo, hhi, hd, hdec, hdechigh⟩ :=
    decremented_register_digits x w hheader
  have hz : 2 ≤ zeros := by
    by_contra hc
    have hpow : (2 : Nat) ^ (zeros + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
    omega
  have hbound := countdown_drain_cap_iff_machine_room (B := B) (F := F) x w hheader hg
  have hmroom : zeros + 2 + F ≤ a + B := (hbound.2.1.1 ⟨hcap, hroom⟩).2
  obtain ⟨hc1, hc2, hc3, he1, he2, he3, hpers, hreg, hmark, hlane⟩ :=
    FixedGammaTargetUnaryCountdownIteration.register_drained (B := B) (v := n) (F := F) x w htag
      hg hz hcap hmroom (fun j hj => (hdec j hj).symm) hdechigh
  have hp0 := (FixedGammaTargetUnaryCountdown.loopTape_pins (B := B) (zeros := zeros) (v := n)
    (r := 0) x w).1
  exact ⟨zeros, hbound.1, hz, hconsumed, hg, hlo, hhi, hbound.2.2.2 ⟨hcap, hroom⟩,
    hbound.2.2.1.1 hmroom, hd, hc1, hc2, hc3, fun j hj i hi => by rw [hc3]; exact hp0 j hj i hi,
    he1, he2, he3, hpers, hreg, hmark, hlane⟩

/-- **The whole countdown, on the *actual parsed target*.**  Replacing the header by a successful
dependent parse `contentInput? codec (Fin.append x w) = some pr`, for an arbitrary codec and with
no monotonicity or injectivity premise: the target carried by the parsed `PrefixInput` — the
`pr.2.n` that `ContentAccepts` feeds to the search relation — is the outer Sigma index `pr.1` and
the target a decoded `contentHeader?` *returns*, the entry register holds `pr.2.n`, and after
exactly `fullClock zeros d pr.2.n` steps the register is all `some false` with exactly `pr.2.n`
marks in the lane and blanks beyond, an endpoint that persists.

The parse is the hypothesis, not a claim about execution: no machine here runs `contentInput?`, the
strict parser, or the decoder, and the window length convention `treeMCSPPrefixM codec pr.1` occurs
only in the type of `pr`.  The implication runs one way only — from parser success plus the explicit
cap and room to the endpoint — and no endpoint-to-parse converse is stated.  The lane is still
uncapped in the machine: `F` is a parameter, no cutoff cell is laid, and a target too large for the
budget would run off the end of the tape, which is a timeout and neither verdict.  Nothing here is a
`ContentAccepts` statement, a language membership, or P-vs-NP mainline progress. -/
theorem countdown_drained_parsed_target {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {a m B F : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec (Fin.append x w) = some pr) (hn : 3 ≤ pr.2.n)
    (hcap : pr.2.n ≤ F) (hroom : gammaZeros pr.2.n + 2 + F ≤ a + B) :
    ∃ zeros, zeros = gammaZeros pr.2.n ∧ 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
      contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
      2 ^ zeros ≤ pr.2.n + 1 ∧ pr.2.n + 1 < 2 ^ (zeros + 1) ∧
      2 * (pr.2.n + 1) < 2 ^ (a + B) ∧
      a + m + 3 + zeros + F < tapeLength (PairEncoding.pairLength a m) B ∧
      let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
      let c0 := FixedGammaTargetUnaryCountdown.machine.run (d + 2)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      let e := FixedGammaTargetUnaryCountdown.machine.run
        (FixedGammaTargetUnaryCountdownIteration.fullClock zeros d pr.2.n)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      d ≤ zeros ∧ c0.state = FixedGammaTargetUnaryCountdown.qLoop ∧
        c0.head.val = a + m + 2 + zeros ∧
        c0.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros pr.2.n 0 ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → c0.tape i = some (pr.2.n.testBit (zeros - j))) ∧
        e.state = FixedGammaTargetUnaryCountdown.qDone ∧
        e.head.val = a + m + 2 + zeros ∧
        e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros 0 pr.2.n ∧
        (∀ t, FixedGammaTargetUnaryCountdownIteration.fullClock zeros d pr.2.n ≤ t →
          FixedGammaTargetUnaryCountdown.machine.run t
            (FixedGammaTargetUnaryCountdown.startConfig B x w) = e) ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → e.tape i = some false) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 3 + zeros ≤ i.val →
          i.val < a + m + 3 + zeros + pr.2.n → e.tape i = some true) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          a + m + 3 + zeros + pr.2.n ≤ i.val → e.tape i = none) := by
  obtain ⟨consumed, hheader, hidx⟩ :=
    contentInput?_target_eq_contentHeader codec (Fin.append x w) hpr
  rw [← hidx] at hheader
  obtain ⟨zeros, hzg, hz, hconsumed, hg, hlo, hhi, hgroom, htroom, hd, hc1, hc2, hc3, hcreg,
    he1, he2, he3, hpers, hreg, hmark, hlane⟩ :=
    countdown_drained_header_value (B := B) (F := F) x w htag hheader hn hcap hroom
  exact ⟨zeros, hzg, hz, hidx, by rw [hheader, hconsumed], hg, hlo, hhi, hgroom, htroom, hd,
    hc1, hc2, hc3, hcreg, he1, he2, he3, hpers, hreg, hmark, hlane⟩

end Pnp4.Frontier.ContractExpansion
