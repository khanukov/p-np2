import Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetRegisterDecrementBridge

/-!
# The countdown's first round runs on the parsed target (Part A G2t)

The pnp3 G2s-a slice `FixedGammaTargetUnaryCountdown` landed a new fixed 11-state table and
explicitly deferred exactly one thing to pnp4: a *value*.  Its `first_round` is stated for a `v`
that is universally quantified — "a positive `v` whose digit `zeros - j` is G2q's decremented
register digit `j` at every `j ≤ zeros` and which has no digit above `zeros`" — and no theorem of
that module produces such a `v`; its own surface probes supply the literals `24` and `23`
**by hand**.  This module is that missing value and nothing else: on a
decoded content header the G2r bridge already proves both digit facts for the decoded target `n`,
so `v := n` is the instantiation, and the phase's first round is then a round on the *actual
parsed target*.  Write `N = a + m` and `d = borrow x w zeros`.

```text
entry   register cell  N+1+j  holds   n.testBit (zeros - j)         j ≤ zeros
exit    register cell  N+1+j  holds   (n-1).testBit (zeros - j)     j ≤ zeros
exit    lane cell      N+3+zeros  holds  some true                  one mark
```

Three theorems, all one-way, all out of a decoded header or a successful dependent parse.

* `countdown_room_iff_target_bound` makes G2s-a's room premise legible in target terms.  The
  countdown allocates the **first tally cell**, one more than G2q's register end, so on a decoded
  header the three forms `2 * (n + 1) < 2 ^ (a + B)`, `zeros + 2 ≤ a + B` and
  `a + m + 3 + zeros < tapeLength (pairLength a m) B` are the same condition.  The doubling is
  exact, not a convenience: the gamma bounds `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)` make
  `2 * (n + 1)` straddle `2 ^ (zeros + 1)` and `2 ^ (zeros + 2)` precisely, so the equivalence has
  no slack at either end.  Two further conjuncts place this room against G2q's: it implies it, and
  at the boundary width `zeros + 1 = a + B` G2q's room holds while this one fails.  Unlike the
  corresponding G2r separation, that second half needs no literal probe — `n + 1 < 2 ^ (zeros + 1)`
  is a header conjunct, so at that width `n + 1 < 2 ^ (a + B)` is immediate.  `B` is a free budget,
  so a header implies none of this; the room is carried, never derived, and is sufficient only.
* `first_countdown_header_value` carries the header through to the actual G2s-a run.  The landed
  `FixedGammaTargetUnaryCountdown.startConfig` — a retag of an actual G2q run at G2q's length-only
  `deadline (a + m)` — *enters* `qLoop` on the separator blank `N + 2 + zeros` after exactly
  `d + 2` steps with the register holding the decoded target `n`, and after exactly
  `firstClock zeros d = 2 * zeros + d + 9` steps is back in `qLoop` there with the register holding
  `n - 1` and **one mark** in the tally lane.  Six cell conjuncts read that endpoint tape at every
  index — the `zeros + 1` register cells, the boundary blank `N`, the separator blank
  `N + 2 + zeros`, the single mark at `N + 3 + zeros`, blanks past it, and the untouched content
  below `N` — so the statement pins the whole tape, not a sample of it.
* `first_countdown_parsed_target` replaces the header by a successful dependent parse
  `contentInput? codec (Fin.append x w) = some pr` for an **arbitrary** codec, with no monotonicity
  and no injectivity premise.  It exports `pr.2.n = pr.1` — the target the parsed `PrefixInput`
  carries, which is what `ContentAccepts` reads, is the outer Sigma index and the target the
  *decoder* returns — and then the same concrete endpoint at that actual parsed target.

## Every hypothesis, in full

* `countdown_room_iff_target_bound`: **two**, the decoded header and the decoded width `hg`, which
  is what ties the statement's otherwise free `zeros` to that header.  No tag, no budget premise —
  `B` is universally quantified — and no machine.
* `first_countdown_header_value`: **four** — the matching tag, the decoded header, `3 ≤ n`, and the
  room `2 * (n + 1) < 2 ^ (a + B)`.  `3 ≤ n` does two jobs: it reaches `2 ≤ zeros`, the width
  premise G2s-a inherits from G2q and thence from `payload_exhausted`, and it discharges G2s-a's
  `1 ≤ v` at `v := n`, without which the borrow would walk off the register instead of subtracting.
  The tag is what `first_round` asks for, and it uses it twice over: to identify the incoming G2q
  endpoint, and to know that the cells at and past the boundary blank are blank on the incoming
  finish tape.  The configuration is **not** a hypothesis and is not
  arbitrary: it is the landed `startConfig B x w`, so the incoming tape is the one the earlier
  phases actually produce from `Fin.append x w`.
* `first_countdown_parsed_target`: **four** — the matching tag, the successful parse, `3 ≤ pr.2.n`,
  and the room at `pr.2.n`.  The tag is carried, not derived from the parse; the header is a
  *conclusion*, obtained through `contentInput?_target_eq_contentHeader`, which is also what gives
  `pr.2.n = pr.1`.

## Four numbers, and which of them is on the tape

G2p-g had to keep the decoded target, the encoded gamma integer `n + 1` and the header's cell count
`consumed = 2 * zeros + 1` apart; G2r moved the register from the second to the first.  This slice
adds a fourth, `n - 1`, and the endpoint register holds *that*.  `zeros` is the physical gamma
width, `consumed` and the window length `treeMCSPPrefixM codec pr.1` stay length conventions, and
no conclusion here puts either in a register cell.  The `r` marks in the lane are **marks**: after
this round there is exactly one, and calling a tally "the target in unary" would be a claim about a
decoded value that no theorem here makes.

## What is not claimed

The **iteration**.  This is one round, and one only.  Nothing here runs the countdown to zero,
composes rounds, or states any clock beyond `firstClock zeros d`, which counts the steps of this
phase alone — not one of the steps `startConfig` embeds.  The endpoint is in `qLoop`, which is
**not** terminal, so unlike G2r's `qDone` these endpoints hold at their exact time and say nothing
about any other time: there is deliberately no persistence conjunct, no deadline, and no clamp.

The **fence**.  The room premise allocates the *first* lane cell and no more.  It is not a bound on
the countdown: a target too large for the budget would run the lane off the end of the tape, which
is a timeout and therefore neither verdict, and nothing here excludes that or claims the target
fits.  Capping the lane needs an executed `some false` at a length-derived offset, laid by a phase
that does not exist; until it does, no theorem here or in pnp3 may be iterated.

Everything G2r already disclaimed still holds.  No machine here executes `contentHeader?`,
`contentInput?`, the strict parser or any decoder: `n` and `pr` occur only in the *statements*, and
every branch of the fixed table is decided by the one symbol under the head — no width, digit
index, register address, mark count, clock, counter, advice, producer mark or proof term occurs in
any row.  Nothing is computed from a proof; no `Nat.find`, choice, or decidability instance
supplies a runtime value.  The machine is never shown to *recover* `n` or `n - 1`: the register is
a tape object whose cells this bridge identifies with digits, and the pinning conjunct is
arithmetic about those digits, not a decoding step the control performs.

There is no **converse**: nothing derives a valid header, a width, `2 ≤ zeros`, room, the borrow
length or a parsed target from `qLoop`, from the endpoint tape, or from a digit found at a register
cell.  No **footprint or budget theorem** exists on the pnp3 side, so every room premise is
sufficient and used, never shown necessary.  No **malformed-gamma branch**: G2q characterises no
non-`qDone` endpoint to route, and no theorem of G2s-a characterises when its `qReject` is reached,
so there is nothing here to case on.  No **first arrival**: the endpoints are given at exactly
`d + 2` and `firstClock zeros d`, and no conjunct says `qLoop` is not entered at some other time.
No **degenerate width**: `zeros ≤ 1` is out of reach of the machine theorems, since `3 ≤ n` forces
the `2 ≤ zeros` that G2s-a needs, while the room theorem carries no width premise and covers it.
The gamma
**leading-digit convention is not restored and must not be read back in** — G2q destroyed it and
each round destroys it further, so the endpoint register's top cell may be `some false` and no
conjunct here excludes that or claims the register is a re-encodable gamma payload.  `qLoop` is an
internal control tag of a phase whose `startConfig` retags an *actual* prior run rather than
`initialConfig` on a raw pair input: reaching it is neither halting of a composed machine nor
language acceptance.  This module states no `accepts`, no `AcceptsAt`, no `ContentAccepts` and no
language membership; clock composition, the fixed parser, the checks, advice freedom, `NP`
membership, `ContentVerifierBridge` and P-vs-NP mainline progress are out of scope.

**Progress classification (AGENTS.md): Infrastructure.**
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-! ### The room the tally lane needs, in target terms -/

/-- **The countdown room, in three equivalent forms.**  G2s-a's `qRunEnd` writes the first mark on
the first blank past the separator, so this phase allocates cell `a + m + 3 + zeros`, one more than
G2q's register end.  On a decoded header that tape condition, the width form `zeros + 2 ≤ a + B`,
and the target form `2 * (n + 1) < 2 ^ (a + B)` are the same condition.  The doubling is exact: the
gamma bounds give `2 ^ (zeros + 1) ≤ 2 * (n + 1) < 2 ^ (zeros + 2)`, so neither direction has slack.

The last two conjuncts place this room against G2q's.  It implies `n + 1 < 2 ^ (a + B)`, which is
the premise the G2r bridge carries; and at the boundary width `zeros + 1 = a + B` G2q's room holds
while this one fails, so the strengthening is real and not a restatement.  Both halves of that
separation are *proved* here — the upper gamma bound is a header conjunct — where the G2r analogue
had to exhibit the second half on a literal word.

`B` is universally quantified and free, which is exactly why a decoded header implies none of this:
the room is a joint condition on the parsed target and the budget, carried by the machine theorems
below and never derived, and sufficient only — no footprint theorem on the pnp3 side shows any of
it necessary. -/
theorem countdown_room_iff_target_bound {a m B n consumed zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed))
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (2 * (n + 1) < 2 ^ (a + B) ↔ zeros + 2 ≤ a + B) ∧
      (zeros + 2 ≤ a + B ↔
        a + m + 3 + zeros < tapeLength (PairEncoding.pairLength a m) B) ∧
      (2 * (n + 1) < 2 ^ (a + B) → n + 1 < 2 ^ (a + B)) ∧
      (zeros + 1 = a + B → n + 1 < 2 ^ (a + B) ∧ ¬ 2 * (n + 1) < 2 ^ (a + B)) := by
  obtain ⟨zeros', hg', -, hlo, hhi, -, -, -⟩ := exhaustion_register_digits x w hheader
  rw [show zeros' = zeros from Option.some.inj (hg'.symm.trans hg)] at hlo hhi
  have hsucc : (2 : Nat) ^ (zeros + 1) = 2 ^ zeros * 2 := Nat.pow_succ 2 zeros
  refine ⟨⟨fun h => ?_, fun h => ?_⟩,
    (FixedGammaTargetUnaryCountdown.room_iff a m B zeros 0).1.symm, fun h => by omega,
    fun h => ⟨h ▸ hhi, ?_⟩⟩
  · by_contra hcon
    have hpow : (2 : Nat) ^ (a + B) ≤ 2 ^ (zeros + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hpow : (2 : Nat) ^ (zeros + 2) ≤ 2 ^ (a + B) := Nat.pow_le_pow_right (by omega) h
    have hsucc2 : (2 : Nat) ^ (zeros + 2) = 2 ^ (zeros + 1) * 2 := Nat.pow_succ 2 (zeros + 1)
    omega
  · rw [← h]
    omega

/-! ### The machine side: the first countdown round runs on the parsed target -/

/-- **The first countdown round, on the decoded header's target.**  On a matching tag, a decoded
header with `3 ≤ n`, and the room `2 * (n + 1) < 2 ^ (a + B)`, the landed G2s-a `startConfig`
*enters* `qLoop` on the separator blank `a + m + 2 + zeros` after exactly `d + 2` steps, writing
nothing, with the register `[a+m+1, a+m+1+zeros]` holding the decoded target `n`; and after exactly
`firstClock zeros d = 2 * zeros + d + 9` steps it is back in `qLoop` there with the register holding
`n - 1`, one mark at `a + m + 3 + zeros`, and `n - 1` still free of digits above `zeros`.  Those
endpoint register cells moreover *pin* `n - 1`: any `v` read off them with no bit above `zeros` is
`n - 1`.  The entry and exit register conjuncts put the round's before and after — `n` and `n - 1` —
in one statement, and the six cell conjuncts cover every index of the endpoint tape.

`3 ≤ n` reaches `2 ≤ zeros`, the width premise G2s-a inherits, and discharges G2s-a's `1 ≤ v` at
`v := n`.  The room is carried, not derived, and is sufficient only
(`countdown_room_iff_target_bound`); it allocates the *first* lane cell and is **not** a bound on
the whole countdown.  This is one round: nothing here iterates, composes a clock, or reaches the
exhaustion.  `qLoop` is not terminal, so both endpoints hold at exactly their stated time and say
nothing about any other time — there is no persistence conjunct, no deadline, and no first-arrival
claim.  Nothing decodes the register on the tape, no machine executes `contentHeader?`, the marks
are marks rather than a value in unary, the gamma leading-digit convention stays destroyed, and
`qLoop` is an internal control tag rather than halting or language acceptance. -/
theorem first_countdown_header_value {a m B n consumed : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) (hn : 3 ≤ n)
    (hroom : 2 * (n + 1) < 2 ^ (a + B)) :
    ∃ zeros, 2 ≤ zeros ∧ consumed = 2 * zeros + 1 ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
      2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      a + m + 3 + zeros < tapeLength (PairEncoding.pairLength a m) B ∧
      let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
      let c0 := FixedGammaTargetUnaryCountdown.machine.run (d + 2)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      let e := FixedGammaTargetUnaryCountdown.machine.run
        (FixedGammaTargetUnaryCountdown.firstClock zeros d)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      d ≤ zeros ∧ c0.state = FixedGammaTargetUnaryCountdown.qLoop ∧
        c0.head.val = a + m + 2 + zeros ∧
        c0.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros n 0 ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → c0.tape i = some (n.testBit (zeros - j))) ∧
        e.state = FixedGammaTargetUnaryCountdown.qLoop ∧
        e.head.val = a + m + 2 + zeros ∧
        e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros (n - 1) 1 ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → e.tape i = some ((n - 1).testBit (zeros - j))) ∧
        (∀ b : Nat, zeros < b → (n - 1).testBit b = false) ∧
        (∀ v : Nat,
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → e.tape i = some (v.testBit (zeros - j))) →
          (∀ b : Nat, zeros < b → v.testBit b = false) → v = n - 1) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 3 + zeros → e.tape i = some true) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          a + m + 3 + zeros + 1 ≤ i.val → e.tape i = none) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 2 + zeros → e.tape i = none) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m → e.tape i = none) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), i.val < a + m →
          e.tape i = FixedGammaTargetPayloadExhaustion.finishTape B x w zeros i) := by
  obtain ⟨zeros, hg, hconsumed, hlo, hhi, hd, hdec, hdechigh⟩ :=
    decremented_register_digits x w hheader
  have hz : 2 ≤ zeros := by
    by_contra hc
    have hpow : (2 : Nat) ^ (zeros + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
    omega
  have hbound := countdown_room_iff_target_bound (B := B) x w hheader hg
  have hroomT : a + m + 3 + zeros < tapeLength (PairEncoding.pairLength a m) B :=
    hbound.2.1.1 (hbound.1.1 hroom)
  obtain ⟨hc1, hc2, hc3, he1, he2, he3, hehigh⟩ :=
    FixedGammaTargetUnaryCountdown.first_round (B := B) (v := n) x w htag hg hz hroomT
      (fun j hj => (hdec j hj).symm) hdechigh (by omega)
  have hp0 := (FixedGammaTargetUnaryCountdown.loopTape_pins (B := B) (zeros := zeros) (v := n)
    (r := 0) x w).1
  have hp1 := FixedGammaTargetUnaryCountdown.loopTape_pins (B := B) (zeros := zeros) (v := n - 1)
    (r := 1) x w
  refine ⟨zeros, hz, hconsumed, hg, hlo, hhi, hroomT, hd, hc1, hc2, hc3, fun j hj i hi => ?_,
    he1, he2, he3, fun j hj i hi => ?_, hehigh, fun v hv hvhigh => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hc3]
    exact hp0 j hj i hi
  · rw [he3]
    exact hp1.1 j hj i hi
  · refine Nat.eq_of_testBit_eq fun b => ?_
    rcases Nat.lt_or_ge zeros b with hb | hb
    · rw [hvhigh b hb, hehigh b hb]
    · have hlt : a + m + 1 + (zeros - b) < tapeLength (PairEncoding.pairLength a m) B := by omega
      have h1 := hv (zeros - b) (by omega) ⟨a + m + 1 + (zeros - b), hlt⟩ rfl
      have h2 := hp1.1 (zeros - b) (by omega) ⟨a + m + 1 + (zeros - b), hlt⟩ rfl
      rw [he3] at h1
      rw [show zeros - (zeros - b) = b by omega] at h1 h2
      exact Option.some.inj (h1.symm.trans h2)
  · rw [he3]
    exact hp1.2.2.2.1 i (by omega) (by omega)
  · rw [he3]
    exact hp1.2.2.2.2.1 i hi
  · rw [he3]
    exact hp1.2.2.1 i hi
  · rw [he3]
    exact hp1.2.1 i hi
  · rw [he3]
    exact hp1.2.2.2.2.2 i hi

/-- **The first countdown round, on the *actual parsed target*.**  Replacing the header by a
successful dependent parse `contentInput? codec (Fin.append x w) = some pr`, for an arbitrary codec
and with no monotonicity or injectivity premise: the target carried by the parsed `PrefixInput` —
the `pr.2.n` that `ContentAccepts` feeds to the search relation — is the outer Sigma index `pr.1`
and the target a decoded `contentHeader?` *returns*, the entry register holds `pr.2.n`, and after
exactly `firstClock zeros d` steps the endpoint register holds `pr.2.n - 1` with one mark in the
lane.  Those endpoint cells pin `pr.2.n - 1` among the values with no bit above `zeros`.

The parse is the hypothesis, not a claim about execution: no machine here runs `contentInput?`, the
strict parser, or the decoder, and the window length convention `treeMCSPPrefixM codec pr.1` occurs
only in the type of `pr`.  This is still one round out of an uncapped lane — nothing iterates,
nothing bounds the countdown, and the room allocates the first tally cell only.  Nothing here is a
`ContentAccepts` statement, a language membership, or P-vs-NP mainline progress. -/
theorem first_countdown_parsed_target {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec (Fin.append x w) = some pr) (hn : 3 ≤ pr.2.n)
    (hroom : 2 * (pr.2.n + 1) < 2 ^ (a + B)) :
    ∃ zeros, 2 ≤ zeros ∧ pr.2.n = pr.1 ∧
      contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1) ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
      2 ^ zeros ≤ pr.2.n + 1 ∧ pr.2.n + 1 < 2 ^ (zeros + 1) ∧
      a + m + 3 + zeros < tapeLength (PairEncoding.pairLength a m) B ∧
      let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
      let c0 := FixedGammaTargetUnaryCountdown.machine.run (d + 2)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      let e := FixedGammaTargetUnaryCountdown.machine.run
        (FixedGammaTargetUnaryCountdown.firstClock zeros d)
        (FixedGammaTargetUnaryCountdown.startConfig B x w)
      d ≤ zeros ∧ c0.state = FixedGammaTargetUnaryCountdown.qLoop ∧
        c0.head.val = a + m + 2 + zeros ∧
        c0.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros pr.2.n 0 ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → c0.tape i = some (pr.2.n.testBit (zeros - j))) ∧
        e.state = FixedGammaTargetUnaryCountdown.qLoop ∧
        e.head.val = a + m + 2 + zeros ∧
        e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w zeros (pr.2.n - 1) 1 ∧
        (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 1 + j → e.tape i = some ((pr.2.n - 1).testBit (zeros - j))) ∧
        (∀ b : Nat, zeros < b → (pr.2.n - 1).testBit b = false) ∧
        (∀ v : Nat,
          (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
            i.val = a + m + 1 + j → e.tape i = some (v.testBit (zeros - j))) →
          (∀ b : Nat, zeros < b → v.testBit b = false) → v = pr.2.n - 1) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 3 + zeros → e.tape i = some true) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          a + m + 3 + zeros + 1 ≤ i.val → e.tape i = none) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m + 2 + zeros → e.tape i = none) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B),
          i.val = a + m → e.tape i = none) ∧
        (∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), i.val < a + m →
          e.tape i = FixedGammaTargetPayloadExhaustion.finishTape B x w zeros i) := by
  obtain ⟨consumed, hheader, hidx⟩ :=
    contentInput?_target_eq_contentHeader codec (Fin.append x w) hpr
  rw [← hidx] at hheader
  obtain ⟨zeros, hz, hconsumed, hg, hlo, hhi, hroomT, hd, hc1, hc2, hc3, hcreg, he1, he2, he3,
    hereg, hehigh, hpin, hmark, hlane, hsep, hbnd, hlow⟩ :=
    first_countdown_header_value (B := B) x w htag hheader hn hroom
  exact ⟨zeros, hz, hidx, by rw [hheader, hconsumed], hg, hlo, hhi, hroomT, hd, hc1, hc2, hc3,
    hcreg, he1, he2, he3, hereg, hehigh, hpin, hmark, hlane, hsep, hbnd, hlow⟩

end Pnp4.Frontier.ContractExpansion
