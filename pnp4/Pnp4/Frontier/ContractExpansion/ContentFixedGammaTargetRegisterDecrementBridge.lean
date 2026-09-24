import Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetPayloadExhaustionBridge

/-!
# The decremented target register is the parsed target's digits (Part A G2r)

Two landed slices each deferred exactly one half of this composition, and this module is that
composition and nothing else.

* The pnp4 G2p-g bridge `exhaustion_register_digits` identifies the register the G2p-e/G2p-f
  loop completes: on a decoded content header `contentHeader? (Fin.append x w) =
  some (n, consumed)` every register digit `registerBit x w zeros j`, `j ≤ zeros` — the content
  of the cell `a+m+1+j`, as that bridge's own endpoint theorem reads it off the tape — is the
  binary digit `zeros - j` of the **encoded gamma integer** `n + 1`, virtual tail included, and
  `n + 1` has no bit above `zeros`.  Those are the two facts about a value that the decrement
  needs, and G2p-g does not decrement.
* The pnp3 G2q slice `FixedGammaTargetRegisterDecrement` subtracts one from that register with
  a fixed 7-state table.  Its `decBit_sub_one` is arithmetic about `Nat`: for an **arbitrary**
  `v` whose bit `zeros - j` is register digit `j` at every `j ≤ zeros` and which has no bit
  above `zeros`, the endpoint digits are the bits of `v - 1`.  No theorem there supplies such a
  `v`, and no theorem there mentions `contentHeader?`, `contentInput?` or a parsed target.

Instantiating that `v` at `n + 1` is the whole content of this module: `v - 1` is then the
decoded target `n` itself.  Write `N = a + m` and `d = borrow x w zeros`.

```text
register cell  a+m+1+j   holds   n.testBit (zeros - j)      for every  j ≤ zeros
```

* `decremented_register_digits` is the parser-side half, with **no machine run in its
  statement**: `decBit` is G2q's endpoint-*content* function and `borrow` is a quantity read
  off the digits, both pure functions of the input word and the width, and no `Config`, clock,
  tag or budget occurs.  A decoded header fixes the physical gamma width `zeros`, `consumed =
  2 * zeros + 1`, the bounds `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)` on the encoded integer, the
  displayed equation at every `j ≤ zeros`, and the completeness fact that `n` has *no* bit above
  `zeros`, so those `zeros + 1` cells carry **all** of the decoded target's digits and none is
  stored elsewhere.  The one remaining conjunct, the bound `d ≤ zeros` that keeps the borrow
  inside the register, needs no header: it is G2q's `borrow_pins`, true of every word and every
  width, and is exported here only because the equation is stated at that `d`.
* `decremented_register_determines_target`: those digits do not merely belong to `n`, they pin
  it, uniquely among the values with no bit above `zeros`.  Still no machine — the statement is
  about `decBit`, not about a cell of any `Config`.
* `decrement_room_iff_target_bound` makes G2q's **stronger** room premise legible in target
  terms.  `qRegEnd` finds the register's right end by the blank past it, so this phase needs
  one cell more than G2p-f did, and on a decoded header the three forms `n + 1 < 2 ^ (a + B)`,
  `zeros + 1 ≤ a + B` and `a + m + 2 + zeros < tapeLength (pairLength a m) B` are the same
  condition.  It is stronger than the G2p-g room `n + 1 < 2 ^ (a + B + 1)`: the third conjunct
  is that it implies it, and the fourth is that at the boundary width `zeros = a + B` it fails.
  That G2p-g's room can still hold at that boundary is *not* a conjunct — no theorem here says
  so; `probe_decrement_room_strictly_stronger` exhibits it on a literal word, which is what
  makes the strengthening strict rather than a restatement.  Like G2p-g's, it is a joint
  condition on the parsed target and the budget that a header alone does not imply, and it is
  carried, never derived.
* `decremented_register_header_value` carries the header through to the actual G2q endpoint:
  matching tag, decoded header, `3 ≤ n`, and that room.  The concrete run of
  `FixedGammaTargetRegisterDecrement.machine` out of the landed
  `FixedGammaTargetRegisterDecrement.startConfig` for exactly
  `decClock (a+m) zeros d` steps is in `qDone` on the stopping cell `a+m+1+zeros-d` with the
  whole tape `decTape B x w zeros d`; every register cell `a+m+1+j`, `j ≤ zeros`, holds
  `some (n.testBit (zeros - j))`; `n` has no bit above `zeros`; those endpoint cells pin `n`;
  every cell outside the register is the incoming G2p-f endpoint cell of
  `finishTape B x w zeros`; and the endpoint persists at every later time.  One conjunct looks
  backwards rather than forwards: the incoming `finishTape` register cells hold
  `some ((n + 1).testBit (zeros - j))`, so the phase's before and after are `n + 1` and `n` in
  a single statement.
* `decremented_register_parsed_target` replaces the header by a successful **dependent parse**
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec.  It exports
  `pr.2.n = pr.1` — the target the parsed `PrefixInput` carries, which is what `ContentAccepts`
  reads, is the outer Sigma index and the target the *decoder* returns — and then states the
  register, pinning conjunct included, in terms of `pr.2.n`.  This is the actual parsed target,
  not a convention length and not an outer placeholder.

## Every hypothesis, in full

Nothing is implicit, nothing is discharged by a search or a default instance, and no theorem
below assumes a tape, a symbol or a register content.

* `decremented_register_digits`: **one** hypothesis, the decoded header.  No tag, no budget, no
  width and no machine.
* `decremented_register_determines_target`: **four** — the decoded header; the decoded width
  `hg`, which is what ties the statement's otherwise free `zeros` to that header; the decremented
  digits of `v`; and that `v` has no bit above `zeros`.  The last is not redundant: the register
  carries only the indices `0 … zeros`, so without it `v` could differ from `n` above them.
* `decrement_room_iff_target_bound`: **two**, the decoded header and the decoded width.  `B` is
  universally quantified and free, which is exactly why the room is not derivable.
* `decremented_register_header_value`: **four** — the matching tag, the decoded header, `3 ≤ n`,
  and the room `n + 1 < 2 ^ (a + B)`.  `3 ≤ n` is used only to reach `2 ≤ zeros`, the width
  premise `register_decremented` inherits from `payload_exhausted`; the room is translated into
  that theorem's tape form and carried, never derived; the tag is what `finishTape_pins` and
  `register_decremented` both ask for.  The configuration is **not** a hypothesis and is not
  arbitrary: it is the landed `FixedGammaTargetRegisterDecrement.startConfig B x w`, which
  retags an actual G2p-d run at G2q's length-only `priorDeadline (a + m)`, so the incoming tape
  is the one the earlier phases produce from `Fin.append x w` — a source-and-content tape this
  module neither posits nor reconstructs.
* `decremented_register_parsed_target`: **four** — the matching tag, the successful parse,
  `3 ≤ pr.2.n`, and the room at `pr.2.n`.  The tag is carried, not derived from the parse.  The
  header is *not* a hypothesis here: it is a conclusion, obtained from the parse through
  `contentInput?_target_eq_contentHeader`, which is also what gives `pr.2.n = pr.1`.

## Three numbers, and which one is now on the tape

G2p-g had to keep `pr.2.n`, the encoded integer `n + 1`, and the header's cell count
`consumed = 2 * zeros + 1` apart, and the same distinction governs here.  What changes is only
which of them the register holds: after this phase the cells hold the digits of the **decoded
target** `n` — the number `ContentAccepts` would feed to the search relation — where before the
phase they held the digits of `n + 1`, the integer the gamma convention physically writes.
`consumed` and the window length `treeMCSPPrefixM codec pr.1` remain length conventions; no
conclusion here is about a register cell holding either.

## What is not claimed

The gamma **leading-digit convention is not restored, and must not be read back in**.  The
convention encodes `n` as the bits of `n + 1` precisely so that the leading digit is a `true`
the decoder can find; subtracting one destroys that.  When the incoming register is exactly
`2 ^ zeros` the borrow runs its whole length and clears digit `0`, so the decremented register's
top cell holds `some false`, and the theorems above say so rather than excluding it — the
`probe_decrement_cleared_top_digit` probe exhibits that case on a literal word.  Nothing here
re-establishes the invariant, and the register is *not* claimed to be a re-encodable gamma
payload.  For the same reason the virtual-tail conjunct of G2p-g has **no** analogue here: a
truncated payload's register cell is `some false` before the phase and the borrow may flip it to
`some true`, so that conjunct is not preserved, and the only statement made about such a cell is
the general one, that it holds `n`'s digit.

No machine here executes `contentHeader?`, `contentInput?`, or any parser: `n` and `pr` occur
only in the *statements*, and the control of G2q's fixed table reads one tape symbol and nothing
else — no width, digit index, address, advice, producer mark or proof term.  Nothing is computed
from a proof; no `Nat.find`, choice, or decidability instance supplies a runtime value.  The
machine is never shown to *recover* `n`: the register is a tape object whose cells this bridge
identifies with digits, and the pinning conjunct is arithmetic about those digits, not a decoding
step the control performs.

There is deliberately no converse: nothing derives a valid header, a width, `2 ≤ zeros`, room,
or the borrow length from `qDone`, from the endpoint tape, or from a digit found at a register
cell.  Nothing here states a footprint or budget theorem — so the room premise is sufficient and
used, never shown necessary — covers a malformed gamma, or measures first arrival.  The two
machine theorems give the endpoint at exactly `decClock (a+m) zeros d` together with its
persistence at every later time, and no conjunct of theirs says that `qDone` is not entered
earlier: minimality is G2q's `decrement_strict`, which is stated for an arbitrary configuration
of the G2p-f endpoint shape and is neither instantiated nor restated here.  Those two theorems
also do not cover the degenerate widths `zeros ≤ 1`, which `register_decremented` inherits from
`payload_exhausted` and excludes; the three parser-side theorems carry no width premise and do
cover them.  Given a decoded header `3 ≤ n` is exactly
`2 ≤ zeros`, in the same sense as in G2p-g: both directions are derivable from the exported
bounds and neither is stated as an equivalence theorem — only the direction used here,
`3 ≤ n → 2 ≤ zeros`, is proved.  `decClock` counts the steps of the G2q phase alone: not one of
the steps its `startConfig` embeds, so no clock here composes a pipeline, and the length-only
`priorDeadline` that identifies the incoming configuration is G2q's, restated nowhere here.
`qDone` is an internal control tag of a phase whose `startConfig` retags an *actual* prior run:
reaching it is neither halting of a composed machine nor language acceptance.  This module
states no `accepts`, no `AcceptsAt` and no language membership; clock composition, the fixed
parser, the checks, advice freedom, `NP` membership, `ContentVerifierBridge` and P-vs-NP
mainline progress are out of scope.

**Progress classification (AGENTS.md): Infrastructure.**
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-! ### The parser side: the decremented digits, completeness, and uniqueness -/

/-- **The decremented register equation.**  On a decoded content header the *decremented*
register digit `j` is the binary digit `zeros - j` of the decoded target `n` itself, for every
`j ≤ zeros`.  The completeness conjunct makes "all of them" precise: `n` has no bit above
`zeros`, so those `zeros + 1` cells carry *all* of `n`'s digits and none is stored elsewhere.
The bound `d ≤ zeros`, which keeps the borrow inside the register, is header-free — it is G2q's
`borrow_pins` for every word and width, exported here because the equation is stated at that
`d`.  This is
`decBit_sub_one` instantiated at `v = n + 1` — the value G2q could not supply, since no pnp3
theorem mentions a header — where `v - 1` is `n`.  The statement mentions no machine, no tag,
no clock and no budget; `decBit` and `borrow` are pure functions of the word and the width.

The top digit is *not* claimed to be `true`: at `n + 1 = 2 ^ zeros` the borrow clears it, and
this equation then reads `n.testBit zeros = false`.  The gamma leading-digit convention is not
restored here or anywhere in this module. -/
theorem decremented_register_digits {a m n consumed : Nat} (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) :
    ∃ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
      consumed = 2 * zeros + 1 ∧ 2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      FixedGammaTargetRegisterDecrement.borrow x w zeros ≤ zeros ∧
      (∀ j, j ≤ zeros →
        FixedGammaTargetRegisterDecrement.decBit x w zeros
            (FixedGammaTargetRegisterDecrement.borrow x w zeros) j =
          n.testBit (zeros - j)) ∧
      (∀ b, zeros < b → n.testBit b = false) := by
  obtain ⟨zeros, hg, hconsumed, hlo, hhi, hbits, hhigh, -⟩ :=
    exhaustion_register_digits x w hheader
  obtain ⟨hdec, hdechigh⟩ :=
    FixedGammaTargetRegisterDecrement.decBit_sub_one x w zeros (n + 1)
      (fun j hj => (hbits j hj).symm) hhigh
  rw [show n + 1 - 1 = n from rfl] at hdec hdechigh
  exact ⟨zeros, hg, hconsumed, hlo, hhi, (FixedGammaTargetRegisterDecrement.borrow_pins x w
    zeros).1, fun j hj => (hdec j hj).symm, hdechigh⟩

/-- **The decremented register pins the decoded target.**  Any `v` whose bit `zeros - j` is the
decremented digit `j` for every `j ≤ zeros`, and which has no bit above `zeros`, equals `n`.
Both premises are needed: the register carries only the `zeros + 1` digits at indices
`0 … zeros`, so without the second premise `v` could differ from `n` above them.  This is
arithmetic about the digits, not a decoding step performed by any machine. -/
theorem decremented_register_determines_target {a m n consumed zeros v : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed))
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hbits : ∀ j, j ≤ zeros →
      v.testBit (zeros - j) = FixedGammaTargetRegisterDecrement.decBit x w zeros
        (FixedGammaTargetRegisterDecrement.borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    v = n := by
  obtain ⟨zeros', hg', -, -, -, -, hdig, hzero⟩ := decremented_register_digits x w hheader
  rw [show zeros' = zeros from Option.some.inj (hg'.symm.trans hg)] at hdig hzero
  refine Nat.eq_of_testBit_eq fun b => ?_
  rcases Nat.lt_or_ge zeros b with hb | hb
  · rw [hhigh b hb, hzero b hb]
  · have h1 := hbits (zeros - b) (by omega)
    have h2 := hdig (zeros - b) (by omega)
    rw [show zeros - (zeros - b) = b by omega] at h1 h2
    rw [h1, h2]

/-- **The stronger room premise, in header terms.**  G2q allocates one cell more than G2p-f,
because `qRegEnd` finds the register's right end by the blank past it and by nothing else.  On a
decoded header the bound `n + 1 < 2 ^ (a + B)` on the encoded gamma integer, the width bound
`zeros + 1 ≤ a + B`, and the tape form `a + m + 2 + zeros < tapeLength (pairLength a m) B` that
`register_decremented` carries are one and the same condition.  The third conjunct is the
comparison with G2p-g: this room implies that slice's `n + 1 < 2 ^ (a + B + 1)`.  The fourth is
the separation: at the boundary width `zeros = a + B` this room fails, while G2p-g's can still
hold, so the strengthening is real and not a restatement.  A decoded header does not imply
either: `B` is a free budget.  So the machine theorems below carry this premise explicitly, and
it is sufficient, not shown necessary — no footprint theorem exists on the pnp3 side. -/
theorem decrement_room_iff_target_bound {a m B n consumed zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed))
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (n + 1 < 2 ^ (a + B) ↔ zeros + 1 ≤ a + B) ∧
      (zeros + 1 ≤ a + B ↔
        a + m + 2 + zeros < tapeLength (PairEncoding.pairLength a m) B) ∧
      (n + 1 < 2 ^ (a + B) → n + 1 < 2 ^ (a + B + 1)) ∧
      (zeros = a + B → ¬ n + 1 < 2 ^ (a + B)) := by
  obtain ⟨zeros', hg', -, hlo, hhi, -, -, -⟩ := exhaustion_register_digits x w hheader
  rw [show zeros' = zeros from Option.some.inj (hg'.symm.trans hg)] at hlo hhi
  refine ⟨⟨fun h => ?_, fun h => ?_⟩,
    (FixedGammaTargetRegisterDecrement.room_iff a m B zeros).1.symm, fun h => ?_, fun h hc => ?_⟩
  · by_contra hcon
    have hpow : (2 : Nat) ^ (a + B) ≤ 2 ^ zeros := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hpow : (2 : Nat) ^ (zeros + 1) ≤ 2 ^ (a + B) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hpow : (2 : Nat) ^ (a + B) ≤ 2 ^ (a + B + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · subst h
    omega

/-! ### The machine side: the decrement endpoint reads the parsed target -/

/-- **The decremented register holds the digits of the decoded header's target.**  On a matching
tag, a decoded header with `3 ≤ n`, and the room `n + 1 < 2 ^ (a + B)`, the landed G2q machine
run out of the landed `startConfig` for exactly `decClock (a+m) zeros d` steps, at the borrow
length `d = borrow x w zeros`, is in `qDone` on the stopping cell `a+m+1+zeros-d` with tape
`decTape B x w zeros d`, and *every* register cell `a+m+1+j`, `j ≤ zeros`, holds the digit
`n.testBit (zeros - j)` of the decoded target.  `n` has no bit above `zeros`, so those cells
carry all of it, and they moreover *pin* it: any `v` read off them with no bit above `zeros` is
`n`.  Every cell outside the register is the incoming G2p-f endpoint cell, and because `qDone`
absorbs the endpoint persists at every later time.  The `finishTape` conjunct records the
incoming register for comparison: it held the digits of `n + 1`, the encoded gamma integer, so
this one statement carries both sides of the subtraction.

Given a decoded header `3 ≤ n` is exactly `2 ≤ zeros`, the premise `register_decremented`
inherits from `payload_exhausted` — both directions follow from the exported bounds, only the
direction used here is proved.  The room premise is carried, not derived, and is sufficient only
(`decrement_room_iff_target_bound`); it is G2q's one-extra-cell premise, strictly stronger than
G2p-g's.  The endpoint register need not begin with a `true`: at `n + 1 = 2 ^ zeros` the borrow
clears the top cell, and no conjunct here excludes that or restores the gamma leading-digit
convention.  Nothing decodes the register on the tape — the pinning conjunct is arithmetic about
the digits, not a step the control performs — and no machine executes `contentHeader?`.  `qDone`
is an internal control tag: this is neither halting of a composed machine nor language
acceptance, `decClock` counts this phase's steps alone, and no converse is claimed. -/
theorem decremented_register_header_value {a m B n consumed : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) (hn : 3 ≤ n)
    (hroom : n + 1 < 2 ^ (a + B)) :
    ∃ zeros, 2 ≤ zeros ∧ consumed = 2 * zeros + 1 ∧
      2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      a + m + 2 + zeros < tapeLength (PairEncoding.pairLength a m) B ∧
      (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
        i.val = a + m + 1 + j →
        FixedGammaTargetPayloadExhaustion.finishTape B x w zeros i =
          some ((n + 1).testBit (zeros - j))) ∧
      let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
      let e := FixedGammaTargetRegisterDecrement.machine.run
        (FixedGammaTargetRegisterDecrement.decClock (a + m) zeros d)
        (FixedGammaTargetRegisterDecrement.startConfig B x w)
      d ≤ zeros ∧ e.state = FixedGammaTargetRegisterDecrement.qDone ∧
        e.head.val = a + m + 1 + zeros - d ∧
        e.tape = FixedGammaTargetRegisterDecrement.decTape B x w zeros d ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → e.tape i = some (n.testBit (zeros - j))) ∧
        (∀ b : Nat, zeros < b → n.testBit b = false) ∧
        (∀ v : Nat,
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → e.tape i = some (v.testBit (zeros - j))) →
          (∀ b : Nat, zeros < b → v.testBit b = false) → v = n) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val < a + m + 1 ∨ a + m + 1 + zeros < i.val →
          e.tape i = FixedGammaTargetPayloadExhaustion.finishTape B x w zeros i) ∧
        (∀ t, FixedGammaTargetRegisterDecrement.decClock (a + m) zeros d ≤ t →
          FixedGammaTargetRegisterDecrement.machine.run t
            (FixedGammaTargetRegisterDecrement.startConfig B x w) = e) := by
  obtain ⟨zeros, hg, hconsumed, hlo, hhi, hbits, -, -⟩ :=
    exhaustion_register_digits x w hheader
  obtain ⟨zeros', hg', -, -, -, hd, hdec, hdechigh⟩ := decremented_register_digits x w hheader
  rw [show zeros' = zeros from Option.some.inj (hg'.symm.trans hg)] at hd hdec hdechigh
  have hz : 2 ≤ zeros := by
    by_contra hc
    have hpow : (2 : Nat) ^ (zeros + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
    omega
  have hbound := decrement_room_iff_target_bound (B := B) x w hheader hg
  have hroom' : a + m + 2 + zeros < tapeLength (PairEncoding.pairLength a m) B :=
    hbound.2.1.1 (hbound.1.1 hroom)
  obtain ⟨-, -, -, -, hfin⟩ :=
    FixedGammaTargetPayloadExhaustion.finishTape_pins (B := B) x w htag hg
  obtain ⟨hq, hh, ht, hreg, hout, hclamp⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented x w htag hg hz hroom'
  refine ⟨zeros, hz, hconsumed, hlo, hhi, hroom', fun j hj i hi => ?_, hd, hq, hh, ht,
    fun j hj i hi => ?_, hdechigh,
    fun v hv hvhigh => decremented_register_determines_target x w hheader hg
      (fun j hj => ?_) hvhigh,
    hout, hclamp⟩
  · rw [hfin j hj i hi, hbits j hj]
  · rw [hreg j hj i hi, hdec j hj]
  · have hlt : a + m + 1 + j < tapeLength (PairEncoding.pairLength a m) B := by omega
    exact Option.some.inj
      ((hv j hj ⟨a + m + 1 + j, hlt⟩ rfl).symm.trans (hreg j hj ⟨a + m + 1 + j, hlt⟩ rfl))

/-- **The decremented register holds the digits of the *actual parsed target*.**  Replacing the
header by a successful dependent parse `contentInput? codec (Fin.append x w) = some pr`, for an
arbitrary codec: the target carried by the parsed `PrefixInput` — the `pr.2.n` that
`ContentAccepts` feeds to the search relation — is the outer Sigma index `pr.1` and the target a
decoded `contentHeader?` *returns*, and every register cell of the G2q endpoint holds the
matching digit of `pr.2.n`, with `pr.2.n` having no bit above `zeros`.  Those cells pin
`pr.2.n`: any `v` whose digits they are and which has no bit above `zeros` is `pr.2.n`.  The
incoming `finishTape` conjunct still reads `pr.2.n + 1`, the encoded gamma integer, so the
phase's before and after are visible in one statement.

The parse is the hypothesis, not a claim about execution: no machine here runs `contentInput?`,
the strict parser, or the decoder, and the window length convention `treeMCSPPrefixM codec pr.1`
occurs only in the type of `pr`.  Nothing here is a `ContentAccepts` statement, a language
membership, or P-vs-NP mainline progress, and the gamma leading-digit convention stays
destroyed. -/
theorem decremented_register_parsed_target {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec (Fin.append x w) = some pr) (hn : 3 ≤ pr.2.n)
    (hroom : pr.2.n + 1 < 2 ^ (a + B)) :
    ∃ zeros, 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
      contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
      2 ^ zeros ≤ pr.2.n + 1 ∧ pr.2.n + 1 < 2 ^ (zeros + 1) ∧
      a + m + 2 + zeros < tapeLength (PairEncoding.pairLength a m) B ∧
      (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
        i.val = a + m + 1 + j →
        FixedGammaTargetPayloadExhaustion.finishTape B x w zeros i =
          some ((pr.2.n + 1).testBit (zeros - j))) ∧
      let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
      let e := FixedGammaTargetRegisterDecrement.machine.run
        (FixedGammaTargetRegisterDecrement.decClock (a + m) zeros d)
        (FixedGammaTargetRegisterDecrement.startConfig B x w)
      d ≤ zeros ∧ e.state = FixedGammaTargetRegisterDecrement.qDone ∧
        e.head.val = a + m + 1 + zeros - d ∧
        e.tape = FixedGammaTargetRegisterDecrement.decTape B x w zeros d ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → e.tape i = some (pr.2.n.testBit (zeros - j))) ∧
        (∀ b : Nat, zeros < b → pr.2.n.testBit b = false) ∧
        (∀ v : Nat,
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → e.tape i = some (v.testBit (zeros - j))) →
          (∀ b : Nat, zeros < b → v.testBit b = false) → v = pr.2.n) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val < a + m + 1 ∨ a + m + 1 + zeros < i.val →
          e.tape i = FixedGammaTargetPayloadExhaustion.finishTape B x w zeros i) ∧
        (∀ t, FixedGammaTargetRegisterDecrement.decClock (a + m) zeros d ≤ t →
          FixedGammaTargetRegisterDecrement.machine.run t
            (FixedGammaTargetRegisterDecrement.startConfig B x w) = e) := by
  obtain ⟨consumed, hheader, hidx⟩ :=
    contentInput?_target_eq_contentHeader codec (Fin.append x w) hpr
  rw [← hidx] at hheader
  obtain ⟨zeros, hz, hconsumed, hlo, hhi, hroom', hfin, hd, hq, hh, ht, hreg, hhigh, hpin,
    hout, hclamp⟩ := decremented_register_header_value (B := B) x w htag hheader hn hroom
  exact ⟨zeros, hz, hidx, by rw [hheader, hconsumed], hlo, hhi, hroom', hfin, hd, hq, hh, ht,
    hreg, hhigh, hpin, hout, hclamp⟩

end Pnp4.Frontier.ContractExpansion
