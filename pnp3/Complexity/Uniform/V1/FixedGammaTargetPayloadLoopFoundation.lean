import Complexity.Uniform.V1.FixedGammaTargetSecondPayload

/-!
# Loop markers for the remaining gamma payload digits (Part A G2p-d foundation)

One fixed 14-state, 42-row machine whose start configuration retags the *actual*
endpoint of the G2p-c second-payload run and which installs on the tape the two
markers a self-stopping payload loop needs.  It is the finite preamble of that
loop, not the loop: the round, its iteration, and the exhaustion finish are
deferred, and this machine halts as soon as the markers are in place.

Write `N = a + m`.  The target register grows from scratch cell `N + 1`, most
significant digit first: G2p-a wrote the leading `true` of `n + 1` there, G2p-b
the first gamma payload digit at `N + 2`, G2p-c the second at `N + 3`.  The
payload cells of a width-`zeros` header are `[9 + zeros, 9 + 2 * zeros)`, digit
`k` at `9 + zeros + k`, so at a decoded `2 ≤ zeros` exactly *two* payload digits
have been consumed when this phase starts — a constant of the phase ABI, not data
read off the tape — while `zeros = 1` has consumed one and `zeros = 0` none.
Digits `2, …, zeros - 1` remain, and there are some exactly when `3 ≤ zeros`.

## The two markers

A loop over the remaining digits must know when to stop and where its next source
is, and it may carry neither in its control.  Both go on the tape:

* a **counter** inside the gamma zero field.  A consumed zero is rewritten
  `some true`, **left to right**, so the marked prefix `[8, 7 + r]` records that
  `r` digits have been consumed.  Scanning left from the terminator over the blank
  trail, the first non-blank cell is then an unconsumed zero (`some false`)
  exactly while work is left and the last consumed marker (`some true`) exactly
  when the payload is exhausted — a stopping rule that reads only the tape.
  Marking right to left would not do: tag cell `7` is also `some false`, so the
  scan could not tell the last gamma zero from the tag;
* a **walking terminator**: the `some true` at `8 + zeros` moves one cell right
  per *physical* source consumed and the vacated cell is blanked, so the cell
  right of the terminator is always the next source and the trail behind it is
  blank.

At a decoded `2 ≤ zeros` this machine installs the `r = 2` instance: it marks the
gamma zeros at cells `8` and `9`, walks to the input terminator, and advances the
terminator over the two payload cells `9 + zeros` and `10 + zeros` that G2p-b and
G2p-c consumed.  Which advance moves the terminator is decided by the tape alone,
in the same three shapes G2p-c's source address has: with `10 + zeros < N` both
sources are physical and the terminator walks to `10 + zeros`, leaving `8 + zeros`
and `9 + zeros` blank; with `10 + zeros = N` only the first is physical, so it
stops at `9 + zeros` and only `8 + zeros` is blanked; with `9 + zeros = N` neither
is, the terminator does not move and nothing is blanked.  `walk N zeros r =
min r (N - 9 - zeros)` is that count and the endpoint head
`8 + zeros + walk N zeros 2` covers all three at once.  A virtual source costs the
same three steps as a physical one (`qSrcA`/`qBackA`/`qOnTerm` against
`qSrcA`/`qClearA`/`qOnTerm`), which is why `exactClock` is width-only.

Advancing the terminator is **destructive**, but only as far as it moves: the
first shape overwrites `9 + zeros` and `10 + zeros` with `some true` and blanks
the first again, the second overwrites only `9 + zeros` as the new terminator, and
the third overwrites neither; the *input terminator* `8 + zeros` is blanked
exactly when `9 + zeros < N`.  Nothing reads those cells again — their values are
in the register — so the endpoint is not `contentTape`: `loopTape_layout` pins it.

## Room and clocks

Room is inherited, not needed here: the head never moves past `N`, a cell every budget
allocates, so no `.right` move of this phase can clamp.  The premise
`a + m + 3 < tapeLength (pairLength a m) B` — equivalently `2 ≤ a + B` (`room_iff`),
the exact G2p-c premise — is carried because it is the hypothesis of the G2p-c endpoint
theorem this module hands off from, so it is what makes the incoming tape known, and
because it allocates the three register cells `loopTape` mentions.  The room a full
loop will need, `N + 1 + zeros < tapeLength (pairLength a m) B`, is assumed nowhere.
`exactClock zeros = zeros + 7` is length-independent and is the first terminal
time of a width `2 ≤ zeros`: `markers_installed` gives the endpoint from it on
(`qDone` is absorbing) and `markers_strict` excludes both terminals before it.  A
malformed gamma has no decoded width and is in `qReject` from `malformedExactClock = 1`
on, with no strictness proved; the public deadline is the length-only `deadline N = N`.
No clock here counts `startConfig`'s embedded steps, so none clocks the composed pipeline.

## What is deferred

The round (counter test, source read, carry, register write), its iteration, the
exhaustion finish that restores the gamma zero field, the complete target
register, the intended loop's own deadline, the all-times clamp/footprint/budget
package, and the decrement from `n + 1` to `n` are **not** here.  Neither are the
two degenerate widths: on a decoded `zeros = 0` this machine finds the terminator
at cell `8` and halts at head `7` after two steps, and on `zeros = 1` it marks
cell `8`, meets the terminator at `9`, restores that mark through `qFin` and halts
at head `7` after five steps — but those runs are exercised *only* by the literal
probes of the surface tests at concrete inputs, and their quantified endpoint
theorems, like `malformed_strict`, the first-arrival direction of the malformed branch,
are the next slice.  Nothing here is connected to `contentHeader?` or to any parsed
header value, and no pnp4 bridge exists for this module.  `qDone` is an internal
endpoint and never language acceptance; `startConfig` is a phase-local retag of an
actual prior run, not a composed `UniformTM` execution from the raw pair input.  Clock
composition, the fixed parser, the checks, advice freedom, `NP` membership, and
`ContentVerifierBridge` are out of scope: infrastructure, not P-vs-NP mainline progress.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation

open PairEncoding

abbrev stateCount : Nat := 14

def qStart : Fin stateCount := ⟨0, by decide⟩
def qZeroA : Fin stateCount := ⟨1, by decide⟩
def qZeroB : Fin stateCount := ⟨2, by decide⟩
def qSeek : Fin stateCount := ⟨3, by decide⟩
def qSrcA : Fin stateCount := ⟨4, by decide⟩
def qClearA : Fin stateCount := ⟨5, by decide⟩
def qBackA : Fin stateCount := ⟨6, by decide⟩
def qOnTerm : Fin stateCount := ⟨7, by decide⟩
def qSrcB : Fin stateCount := ⟨8, by decide⟩
def qClearB : Fin stateCount := ⟨9, by decide⟩
def qBackB : Fin stateCount := ⟨10, by decide⟩
def qFin : Fin stateCount := ⟨11, by decide⟩
def qDone : Fin stateCount := ⟨12, by decide⟩
def qReject : Fin stateCount := ⟨13, by decide⟩

/-- The complete fixed 14-state, 42-row table.  No width, digit, index, address,
proof, advice, or producer mark occurs in it: every branch is decided by the
symbol under the head.  `qZeroA`/`qZeroB` mark the two consumed gamma zeros and
dispatch on the terminator, `qSeek` walks to it, the `qSrcA`/`qClearA`/`qBackA`
and `qSrcB`/`qClearB`/`qBackB` triples advance the walking terminator once each
through `qOnTerm`, and `qFin` restores counter marks on the width-one branch. -/
def raw (q : Fin stateCount) (s : Option Bool) : Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some false => (qZeroA, some false, .right)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some false => (qZeroB, some true, .right)
    | some true => (qDone, some true, .left)
    | none => (qReject, none, .stay)
  | 2 => match s with
    | some false => (qSeek, some true, .right)
    | some true => (qFin, some true, .left)
    | none => (qReject, none, .stay)
  | 3 => match s with
    | some false => (qSeek, some false, .right)
    | some true => (qSrcA, some true, .right)
    | none => (qReject, none, .stay)
  | 4 => match s with
    | some _ => (qClearA, some true, .left)
    | none => (qBackA, none, .left)
  | 5 => match s with
    | some true => (qOnTerm, none, .right)
    | s => (qReject, s, .stay)
  | 6 => match s with
    | some true => (qOnTerm, some true, .stay)
    | s => (qReject, s, .stay)
  | 7 => match s with
    | some true => (qSrcB, some true, .right)
    | s => (qReject, s, .stay)
  | 8 => match s with
    | some _ => (qClearB, some true, .left)
    | none => (qBackB, none, .left)
  | 9 => match s with
    | some true => (qDone, none, .right)
    | s => (qReject, s, .stay)
  | 10 => match s with
    | some true => (qDone, some true, .stay)
    | s => (qReject, s, .stay)
  | 11 => match s with
    | some true => (qFin, some false, .left)
    | some false => (qDone, some false, .stay)
    | none => (qReject, none, .stay)
  | 12 => (qDone, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qDone
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Phase-local handoff ABI: only the control of the actual G2p-c configuration is
replaced. -/
def retagSecondPayload {N B : Nat}
    (c : Config FixedGammaTargetSecondPayload.stateCount N B) :
    Config stateCount N B := ⟨qStart, c.head, c.tape⟩

/-- The retagged *actual* G2p-c endpoint configuration: a phase-local handoff, not
a composed raw-input execution, and no clock below counts its embedded steps. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagSecondPayload (FixedGammaTargetSecondPayload.machine.run
    (FixedGammaTargetSecondPayload.deadline (a + m))
    (FixedGammaTargetSecondPayload.startConfig B x w))

/-- First terminal time of a decoded width `2 ≤ zeros`: two counter marks and two
terminator advances.  The degenerate widths and a malformed gamma are outside it. -/
def exactClock (zeros : Nat) : Nat := zeros + 7

/-- A time from which a *malformed* gamma — no decoded width — is in `qReject`; the
matching first-arrival direction (`malformed_strict`) is deferred, not proved here. -/
def malformedExactClock : Nat := 1

/-- Public length-only deadline for **this phase only**: it omits the steps
embedded in `startConfig` and is not the intended full loop's deadline. -/
def deadline (N : Nat) : Nat := N

/-- Terminator advance after `r` consumed sources: one cell per *physical* source,
where `N - 9 - zeros` counts the physical cells at or after the first source
`9 + zeros`, not the payload's own; reading `r` as a source count needs `r ≤ zeros`. -/
def walk (N zeros r : Nat) : Nat := min r (N - 9 - zeros)

/-- Digit `i` of the target register: the bootstrap's leading `true` at `i = 0`,
and otherwise the gamma payload cell `8 + zeros + i`, read through the blank
padding so that a cell at or past `a + m` is the virtual zero. -/
def registerBit {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros i : Nat) : Bool :=
  if i = 0 then true
  else (FixedContentTagGate.physicalSymbol (Fin.append x w) (8 + zeros + i)).getD false

/-- Tape with the loop markers installed for `r` consumed sources: the counter
prefix `[8, 7 + r]` marked, the terminator trail
`[8 + zeros, 8 + zeros + walk N zeros r)` blank, the walking terminator at
`8 + zeros + walk N zeros r`, the register `[N + 1, N + 1 + r]` holding its `r + 1`
digits, and the incoming content tape everywhere else.  This module proves the
`r = 2` instance; the definition is general for the deferred round. -/
def loopTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros r : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if 8 ≤ i.val ∧ i.val ≤ 7 + r then some true
  else if 8 + zeros ≤ i.val ∧ i.val < 8 + zeros + walk (a + m) zeros r then none
  else if i.val = 8 + zeros + walk (a + m) zeros r then some true
  else if a + m + 1 ≤ i.val ∧ i.val ≤ a + m + 1 + r then
    some (registerBit x w zeros (i.val - (a + m + 1)))
  else FixedPairContentMarkerErase.contentTape B x w i

/-- Every row of the fixed table, pinned literally, with the resource counts. -/
theorem table_and_resource_pins :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qZeroA, some false, .right) ∧
    machine.step qStart (some true) = (qReject, some true, .stay) ∧
    machine.step qZeroA none = (qReject, none, .stay) ∧
    machine.step qZeroA (some false) = (qZeroB, some true, .right) ∧
    machine.step qZeroA (some true) = (qDone, some true, .left) ∧
    machine.step qZeroB none = (qReject, none, .stay) ∧
    machine.step qZeroB (some false) = (qSeek, some true, .right) ∧
    machine.step qZeroB (some true) = (qFin, some true, .left) ∧
    machine.step qSeek none = (qReject, none, .stay) ∧
    machine.step qSeek (some false) = (qSeek, some false, .right) ∧
    machine.step qSeek (some true) = (qSrcA, some true, .right) ∧
    machine.step qSrcA none = (qBackA, none, .left) ∧
    machine.step qSrcA (some false) = (qClearA, some true, .left) ∧
    machine.step qSrcA (some true) = (qClearA, some true, .left) ∧
    machine.step qClearA none = (qReject, none, .stay) ∧
    machine.step qClearA (some false) = (qReject, some false, .stay) ∧
    machine.step qClearA (some true) = (qOnTerm, none, .right) ∧
    machine.step qBackA none = (qReject, none, .stay) ∧
    machine.step qBackA (some false) = (qReject, some false, .stay) ∧
    machine.step qBackA (some true) = (qOnTerm, some true, .stay) ∧
    machine.step qOnTerm none = (qReject, none, .stay) ∧
    machine.step qOnTerm (some false) = (qReject, some false, .stay) ∧
    machine.step qOnTerm (some true) = (qSrcB, some true, .right) ∧
    machine.step qSrcB none = (qBackB, none, .left) ∧
    machine.step qSrcB (some false) = (qClearB, some true, .left) ∧
    machine.step qSrcB (some true) = (qClearB, some true, .left) ∧
    machine.step qClearB none = (qReject, none, .stay) ∧
    machine.step qClearB (some false) = (qReject, some false, .stay) ∧
    machine.step qClearB (some true) = (qDone, none, .right) ∧
    machine.step qBackB none = (qReject, none, .stay) ∧
    machine.step qBackB (some false) = (qReject, some false, .stay) ∧
    machine.step qBackB (some true) = (qDone, some true, .stay) ∧
    machine.step qFin none = (qReject, none, .stay) ∧
    machine.step qFin (some false) = (qDone, some false, .stay) ∧
    machine.step qFin (some true) = (qFin, some false, .left) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 14 ∧ machine.start = qStart ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qZeroA.val = 1 ∧ qZeroB.val = 2 ∧ qSeek.val = 3 ∧
    qSrcA.val = 4 ∧ qClearA.val = 5 ∧ qBackA.val = 6 ∧ qOnTerm.val = 7 ∧
    qSrcB.val = 8 ∧ qClearB.val = 9 ∧ qBackB.val = 10 ∧ qFin.val = 11 ∧
    qDone.val = 12 ∧ qReject.val = 13 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 42 := by
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
G2p-c endpoint, with the same head and the same tape. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetSecondPayload.machine.run
      (FixedGammaTargetSecondPayload.deadline (a + m))
      (FixedGammaTargetSecondPayload.startConfig B x w)
    let c := startConfig B x w
    c = retagSecondPayload p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Closed forms of every clock and walk of this module. -/
theorem clock_pins (N zeros r : Nat) :
    exactClock zeros = zeros + 7 ∧ malformedExactClock = 1 ∧
      walk N zeros r = min r (N - 9 - zeros) ∧ deadline N = N :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The three inherited register cells are allocated exactly when `2 ≤ a + B` —
not at `a = B = 0`, nor at `a + B = 1`.  Room is never inferred from a header. -/
theorem room_iff (a m B : Nat) :
    a + m + 3 < tapeLength (pairLength a m) B ↔ 2 ≤ a + B := by
  unfold tapeLength pairLength
  omega

/-- Every decoder-valid width finishes inside the public length-only deadline; the
premise is the decoder's own bound, which `gammaZeros?` always supplies. -/
theorem exactClock_le_deadline {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    exactClock zeros ≤ deadline N := by
  unfold exactClock deadline
  omega

/-- Register semantics: digit `0` is the bootstrap's leading `true`, digit `1` the
cell `9 + zeros` and digit `2` the cell `10 + zeros` — the two G2p-b and G2p-c copy
at a decoded `2 ≤ zeros` — and digit `i + 1` the payload cell `9 + zeros + i` read
through the blank padding, so a cell at or past `a + m` yields the virtual `false`. -/
theorem registerBit_pins {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    registerBit x w zeros 0 = true ∧
      registerBit x w zeros 1 =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false ∧
      registerBit x w zeros 2 =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros)).getD false ∧
      ∀ i, registerBit x w zeros (i + 1) =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + i)).getD false := by
  refine ⟨by unfold registerBit; rw [if_pos rfl], ?_, ?_, fun i => ?_⟩
  · unfold registerBit
    rw [if_neg (by omega), show 8 + zeros + 1 = 9 + zeros by omega]
  · unfold registerBit
    rw [if_neg (by omega), show 8 + zeros + 2 = 10 + zeros by omega]
  · unfold registerBit
    rw [if_neg (by omega), show 8 + zeros + (i + 1) = 9 + zeros + i by omega]

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

/-! ### Content cells -/

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

/-- Tag cell `7`, the gamma zeros, and the terminator. -/
private theorem gamma_cells {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    9 + zeros ≤ a + m ∧ content x w (8 + zeros) = some true ∧
      ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false := by
  obtain ⟨hlt, hterm, hzero⟩ :=
    (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hall := ((FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.1).1 htag
  have h7 := hall ⟨7, by decide⟩
  refine ⟨by omega, hterm, fun i h1 h2 => ?_⟩
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [show i = 7 by omega]
    exact h7
  · have hi := hzero (i - 8) (by omega)
    rwa [show 8 + (i - 8) = i by omega] at hi

/-! ### Nat-addressed tapes -/

/-- The incoming G2p-c endpoint tape on a width `2 ≤ zeros`: content plus the three
register cells. -/
private def startNat {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool :=
  if k = a + m + 3 then some (registerBit x w zeros 2)
  else if k = a + m + 2 then some (registerBit x w zeros 1)
  else if k = a + m + 1 then some true
  else content x w k

/-- Nat-addressed form of `loopTape`. -/
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

private theorem startNat_content {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros k : Nat} (h1 : k ≠ a + m + 1) (h2 : k ≠ a + m + 2) (h3 : k ≠ a + m + 3) :
    startNat x w zeros k = content x w k := by
  unfold startNat
  rw [if_neg h3, if_neg h2, if_neg h1]

private theorem loopNat_term {a m : Nat} (x : Bitstring a) (w : Bitstring m) {zeros r : Nat}
    (hr : r ≤ zeros) :
    loopNat x w zeros r (8 + zeros + walk (a + m) zeros r) = some true := by
  unfold loopNat
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

/-! ### Tape shapes of the terminator advance: one family covers every step, since
each leaves the incoming tape with the marks and a window around the terminator
overwritten. -/

/-- Marks at `8` and `9`, the blank trail `[8 + zeros, 8 + zeros + trail)`, then
`some true` up to `term` (overwritten payload cells and the terminator itself), and
the incoming G2p-c tape elsewhere. -/
private def catchNat {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros trail term k : Nat) : Option Bool :=
  if k = 8 ∨ k = 9 then some true
  else if 8 + zeros ≤ k ∧ k < 8 + zeros + trail then none
  else if 8 + zeros ≤ k ∧ k ≤ term then some true
  else startNat x w zeros k

/-- Every window cell the trail does not cover reads `some true`. -/
private theorem catch_true {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros trail term k : Nat} (hz : 2 ≤ zeros) (h1 : 8 + zeros + trail ≤ k)
    (h2 : k ≤ term) : catchNat x w zeros trail term k = some true := by
  unfold catchNat
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, h2⟩]

/-- The cell right of the terminator is the next source, a plain content cell. -/
private theorem catch_next {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros trail term : Nat} (hz : 2 ≤ zeros) (ht : 8 + zeros + trail ≤ term)
    (hle : term + 1 ≤ a + m) :
    catchNat x w zeros trail term (term + 1) = content x w (term + 1) := by
  unfold catchNat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    startNat_content x w (by omega) (by omega) (by omega)]

/-- Writing the walking terminator one cell right of where it stands. -/
private theorem catch_step_term {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros trail term : Nat} (hz : 2 ≤ zeros) (ht : 8 + zeros + trail ≤ term) :
    catchNat x w zeros trail (term + 1) (term + 1) = some true ∧
      ∀ k, k ≠ term + 1 →
        catchNat x w zeros trail (term + 1) k = catchNat x w zeros trail term k := by
  refine ⟨catch_true x w hz (by omega) le_rfl, fun k hk => ?_⟩
  unfold catchNat
  by_cases h89 : k = 8 ∨ k = 9
  · rw [if_pos h89, if_pos h89]
  · rw [if_neg h89, if_neg h89]
    by_cases htr : 8 + zeros ≤ k ∧ k < 8 + zeros + trail
    · rw [if_pos htr, if_pos htr]
    · rw [if_neg htr, if_neg htr]
      by_cases hin : 8 + zeros ≤ k ∧ k ≤ term
      · rw [if_pos hin, if_pos ⟨hin.1, by omega⟩]
      · rw [if_neg hin, if_neg (fun hc => hin ⟨hc.1, by omega⟩)]

/-- Blanking the cell the terminator just left; its own position plays no part. -/
private theorem catch_step_trail {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros trail term : Nat} (hz : 2 ≤ zeros) :
    catchNat x w zeros (trail + 1) term (8 + zeros + trail) = none ∧
      ∀ k, k ≠ 8 + zeros + trail →
        catchNat x w zeros (trail + 1) term k = catchNat x w zeros trail term k := by
  refine ⟨?_, fun k hk => ?_⟩
  · unfold catchNat
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  · unfold catchNat
    by_cases h89 : k = 8 ∨ k = 9
    · rw [if_pos h89, if_pos h89]
    · rw [if_neg h89, if_neg h89]
      by_cases htr : 8 + zeros ≤ k ∧ k < 8 + zeros + trail
      · rw [if_pos htr, if_pos ⟨htr.1, by omega⟩]
      · rw [if_neg (fun hc => htr ⟨hc.1, by omega⟩), if_neg htr]

/-- The endpoint tape is the advance family at its final window. -/
private theorem loop_eq_catch {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hN : 9 + zeros ≤ a + m) (k : Nat) :
    loopNat x w zeros 2 k =
      catchNat x w zeros (walk (a + m) zeros 2) (8 + zeros + walk (a + m) zeros 2) k := by
  have hw : walk (a + m) zeros 2 ≤ 2 ∧ 8 + zeros + walk (a + m) zeros 2 < a + m := by
    unfold walk; omega
  unfold loopNat catchNat
  by_cases h89 : k = 8 ∨ k = 9
  · rw [if_pos (by omega), if_pos h89]
  · rw [if_neg (by omega), if_neg h89]
    by_cases htr : 8 + zeros ≤ k ∧ k < 8 + zeros + walk (a + m) zeros 2
    · rw [if_pos htr, if_pos htr]
    · rw [if_neg htr, if_neg htr]
      by_cases hin : k = 8 + zeros + walk (a + m) zeros 2
      · have hwin : 8 + zeros ≤ k ∧ k ≤ 8 + zeros + walk (a + m) zeros 2 := by omega
        rw [if_pos hin, if_pos hwin]
      · have hwin : ¬ (8 + zeros ≤ k ∧ k ≤ 8 + zeros + walk (a + m) zeros 2) := by
          intro hc
          omega
        rw [if_neg hin, if_neg hwin]
        by_cases hreg : a + m + 1 ≤ k ∧ k ≤ a + m + 1 + 2
        · rcases (show k = a + m + 1 ∨ k = a + m + 2 ∨ k = a + m + 3 by omega)
            with rfl | rfl | rfl
          · rw [if_pos hreg, show a + m + 1 - (a + m + 1) = 0 by omega,
              (registerBit_pins x w zeros).1]
            unfold startNat
            rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
          · rw [if_pos hreg, show a + m + 2 - (a + m + 1) = 1 by omega]
            unfold startNat
            rw [if_neg (by omega), if_pos rfl]
          · rw [if_pos hreg, show a + m + 3 - (a + m + 1) = 2 by omega]
            unfold startNat
            rw [if_pos rfl]
        · rw [if_neg hreg, startNat_content x w (by omega) (by omega) (by omega)]

/-! ### The literal layout of the endpoint tape -/

/-- Literal layout of the endpoint tape: both consumed gamma zeros `some true`,
the input terminator cell blank when the first source was physical, the walking
terminator `some true`, the three register cells holding digits `0`, `1`,
`2`, every allocated cell past the register blank, and the tag prefix `[0, 6]`
untouched literal content. -/
theorem loopTape_layout {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hz : 2 ≤ zeros) (hN : 9 + zeros ≤ a + m)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    loopTape B x w zeros 2 ⟨8, by unfold tapeLength pairLength at hroom ⊢; omega⟩ =
      some true ∧
    loopTape B x w zeros 2 ⟨9, by unfold tapeLength pairLength at hroom ⊢; omega⟩ =
      some true ∧
    (9 + zeros < a + m → loopTape B x w zeros 2
      ⟨8 + zeros, by unfold tapeLength pairLength at hroom ⊢; omega⟩ = none) ∧
    loopTape B x w zeros 2 ⟨8 + zeros + walk (a + m) zeros 2,
        by unfold tapeLength pairLength at hroom ⊢; unfold walk; omega⟩ = some true ∧
    loopTape B x w zeros 2 ⟨a + m + 1, by unfold tapeLength pairLength at hroom ⊢; omega⟩ =
      some true ∧
    loopTape B x w zeros 2 ⟨a + m + 2, by unfold tapeLength pairLength at hroom ⊢; omega⟩ =
      some (registerBit x w zeros 1) ∧
    loopTape B x w zeros 2 ⟨a + m + 3, hroom⟩ = some (registerBit x w zeros 2) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 < i.val →
      loopTape B x w zeros 2 i = none) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), i.val < 7 →
      loopTape B x w zeros 2 i = FixedPairContentMarkerErase.contentTape B x w i) := by
  have hw : walk (a + m) zeros 2 ≤ 2 ∧ 8 + zeros + walk (a + m) zeros 2 < a + m := by
    unfold walk; omega
  refine ⟨?_, ?_, fun hP => ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [loopTape_eq]
    show loopNat x w zeros 2 8 = some true
    unfold loopNat
    rw [if_pos ⟨by omega, by omega⟩]
  · rw [loopTape_eq]
    show loopNat x w zeros 2 9 = some true
    unfold loopNat
    rw [if_pos ⟨by omega, by omega⟩]
  · have h1 : 1 ≤ walk (a + m) zeros 2 := by unfold walk; omega
    rw [loopTape_eq]
    show loopNat x w zeros 2 (8 + zeros) = none
    unfold loopNat
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  · rw [loopTape_eq]
    show loopNat x w zeros 2 (8 + zeros + walk (a + m) zeros 2) = some true
    exact loopNat_term x w (by omega)
  · rw [loopTape_eq]
    show loopNat x w zeros 2 (a + m + 1) = some true
    unfold loopNat
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos ⟨by omega, by omega⟩, show a + m + 1 - (a + m + 1) = 0 by omega,
      (registerBit_pins x w zeros).1]
  · rw [loopTape_eq]
    show loopNat x w zeros 2 (a + m + 2) = some (registerBit x w zeros 1)
    unfold loopNat
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos ⟨by omega, by omega⟩, show a + m + 2 - (a + m + 1) = 1 by omega]
  · rw [loopTape_eq]
    show loopNat x w zeros 2 (a + m + 3) = some (registerBit x w zeros 2)
    unfold loopNat
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos ⟨by omega, by omega⟩, show a + m + 3 - (a + m + 1) = 2 by omega]
  · rw [loopTape_eq]
    unfold loopNat
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact content_ge x w (by omega)
  · rw [loopTape_eq]
    unfold loopNat
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact (contentTape_eq x w i).symm

/-! ### The counter marks -/
private theorem start_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    At (startConfig B x w) qStart 7 (startNat x w zeros) := by
  obtain ⟨-, hh, ht⟩ :=
    FixedGammaTargetSecondPayload.second_payload_at_deadline (B := B) x w htag hg hz hroom
  refine ⟨rfl, hh, fun i => ?_⟩
  change (FixedGammaTargetSecondPayload.machine.run _ _).tape i = _
  rw [ht]
  unfold FixedGammaTargetSecondPayload.secondPayloadTape
    FixedGammaTargetFirstPayload.firstPayloadTape
    FixedGammaTerminatorScratchBootstrap.scratchTape startNat content
    FixedPairContentMarkerErase.contentTape
  rw [(registerBit_pins (zeros := zeros) x w).2.1,
    (registerBit_pins (zeros := zeros) x w).2.2.1]
  unfold FixedContentTagGate.physicalSymbol
  split_ifs <;> rfl

private def preState (zeros s : Nat) : Fin stateCount :=
  if s = 0 then qStart
  else if s = 1 then qZeroA
  else if s = 2 then qZeroB
  else if s ≤ 1 + zeros then qSeek
  else qSrcA

private def preTape {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros s k : Nat) :
    Option Bool :=
  if (k = 8 ∧ 2 ≤ s) ∨ (k = 9 ∧ 3 ≤ s) then some true else startNat x w zeros k

private theorem preTape_same {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros t t' : Nat) (h2 : 2 ≤ t ↔ 2 ≤ t') (h3 : 3 ≤ t ↔ 3 ≤ t') (k : Nat) :
    preTape x w zeros t k = preTape x w zeros t' k := by
  unfold preTape
  by_cases h : (k = 8 ∧ 2 ≤ t) ∨ (k = 9 ∧ 3 ≤ t)
  · refine (if_pos h).trans (if_pos ?_).symm
    rcases h with ⟨hk, ht⟩ | ⟨hk, ht⟩
    · exact Or.inl ⟨hk, h2.1 ht⟩
    · exact Or.inr ⟨hk, h3.1 ht⟩
  · refine (if_neg h).trans (if_neg ?_).symm
    intro hc
    rcases hc with ⟨hk, ht⟩ | ⟨hk, ht⟩
    · exact h (Or.inl ⟨hk, h2.2 ht⟩)
    · exact h (Or.inr ⟨hk, h3.2 ht⟩)

/-- Marking the *first* consumed zero at cell `8` leaves every other cell alone;
the mark at cell `9` must agree. -/
private theorem preTape_keep8 {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros t t' : Nat) (h3 : 3 ≤ t ↔ 3 ≤ t') :
    ∀ k, k ≠ 8 → preTape x w zeros t k = preTape x w zeros t' k := by
  intro k hk
  unfold preTape
  by_cases h : 3 ≤ t
  · have h' : 3 ≤ t' := h3.1 h
    by_cases h9 : k = 9
    · rw [if_pos (Or.inr ⟨h9, h⟩), if_pos (Or.inr ⟨h9, h'⟩)]
    · rw [if_neg (by omega), if_neg (by omega)]
  · have h' : ¬ (3 ≤ t') := fun hc => h (h3.2 hc)
    rw [if_neg (by omega), if_neg (by omega)]

/-- Marking the *second* consumed zero at cell `9` leaves every other cell alone;
the mark at cell `8` must agree. -/
private theorem preTape_keep9 {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros t t' : Nat) (h2 : 2 ≤ t ↔ 2 ≤ t') :
    ∀ k, k ≠ 9 → preTape x w zeros t k = preTape x w zeros t' k := by
  intro k hk
  unfold preTape
  by_cases h : 2 ≤ t
  · have h' : 2 ≤ t' := h2.1 h
    by_cases h8 : k = 8
    · rw [if_pos (Or.inl ⟨h8, h⟩), if_pos (Or.inl ⟨h8, h'⟩)]
    · rw [if_neg (by omega), if_neg (by omega)]
  · have h' : ¬ (2 ≤ t') := fun hc => h (h2.2 hc)
    rw [if_neg (by omega), if_neg (by omega)]

/-- The head walks right from the tag anchor `7` to the first consumed source
`9 + zeros`, marking the two consumed gamma zeros on the way; head and marked
prefix are schedules in the step index alone. -/
private theorem pre_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s ≤ 2 + zeros) :
    At (machine.run s (startConfig B x w)) (preState zeros s) (7 + s)
      (preTape x w zeros s) := by
  obtain ⟨hN, hterm, hfalse⟩ := gamma_cells x w htag hg
  have hfit : ∀ k, k ≤ 9 + zeros → k + 1 < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    omega
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := start_at (B := B) x w htag hg hz hroom
      refine ⟨hq, hh, fun i => (ht i).trans ?_⟩
      unfold preTape
      rw [if_neg (by omega)]
  | succ s ih =>
      have ih := ih (by omega)
      have hzeros : ∀ k, 7 ≤ k → k < 8 + zeros →
          ¬ ((k = 8 ∧ 2 ≤ s) ∨ (k = 9 ∧ 3 ≤ s)) → preTape x w zeros s k = some false := by
        intro k h1 h2 h3
        unfold preTape
        rw [if_neg h3, startNat_content x w (by omega) (by omega) (by omega)]
        exact hfalse k h1 h2
      rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ (3 ≤ s ∧ s ≤ zeros) ∨ s = 1 + zeros by omega)
        with h | h | h | h | h
      · subst h
        simp (disch := omega) only [preState, if_pos, if_neg, if_true] at ih ⊢
        refine stepAt_right ih (hzeros 7 le_rfl (by omega) (by omega)) rfl (by omega)
          (hfit 7 (by omega)) ?_
          (fun i _ => preTape_same x w zeros 1 0 (by omega) (by omega) i)
        exact (preTape_same x w zeros 1 0 (by omega) (by omega) 7).trans
          (hzeros 7 le_rfl (by omega) (by omega))
      · subst h
        simp (disch := omega) only [preState, if_pos, if_neg, if_true] at ih ⊢
        refine stepAt_right ih (hzeros 8 (by omega) (by omega) (by omega)) rfl (by omega)
          (hfit 8 (by omega)) ?_ (preTape_keep8 x w zeros 2 1 (by omega))
        show preTape x w zeros 2 8 = some true
        unfold preTape
        rw [if_pos (Or.inl ⟨rfl, by omega⟩)]
      · subst h
        simp (disch := omega) only [preState, if_pos, if_neg, if_true] at ih ⊢
        refine stepAt_right ih (hzeros 9 (by omega) (by omega) (by omega)) rfl (by omega)
          (hfit 9 (by omega)) ?_ (preTape_keep9 x w zeros 3 2 (by omega))
        show preTape x w zeros 3 9 = some true
        unfold preTape
        rw [if_pos (Or.inr ⟨rfl, by omega⟩)]
      · simp (disch := omega) only [preState, if_pos, if_neg] at ih ⊢
        refine stepAt_right ih (hzeros (7 + s) (by omega) (by omega) (by omega)) rfl
          (by omega) (hfit (7 + s) (by omega)) ?_
          (fun i _ => preTape_same x w zeros (s + 1) s (by omega) (by omega) i)
        exact (preTape_same x w zeros (s + 1) s (by omega) (by omega) (7 + s)).trans
          (hzeros (7 + s) (by omega) (by omega) (by omega))
      · subst h
        simp (disch := omega) only [preState, if_pos, if_neg] at ih ⊢
        have hr : preTape x w zeros (1 + zeros) (7 + (1 + zeros)) = some true := by
          unfold preTape
          rw [if_neg (by omega), startNat_content x w (by omega) (by omega) (by omega),
            show 7 + (1 + zeros) = 8 + zeros by omega]
          exact hterm
        refine stepAt_right ih hr rfl (by omega) (hfit (7 + (1 + zeros)) (by omega)) ?_
          (fun i _ => preTape_same x w zeros (1 + zeros + 1) (1 + zeros) (by omega)
            (by omega) i)
        exact (preTape_same x w zeros (1 + zeros + 1) (1 + zeros) (by omega) (by omega)
          (7 + (1 + zeros))).trans hr

private theorem pre_eq_catch {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hz : 2 ≤ zeros) (hN : 9 + zeros ≤ a + m)
    (hterm : content x w (8 + zeros) = some true) (k : Nat) :
    preTape x w zeros (2 + zeros) k = catchNat x w zeros 0 (8 + zeros) k := by
  unfold preTape catchNat
  by_cases h89 : k = 8 ∨ k = 9
  · rw [if_pos (by rcases h89 with h | h <;> omega), if_pos h89]
  · rw [if_neg (by rcases (show k ≠ 8 ∧ k ≠ 9 by omega) with ⟨h1, h2⟩; omega), if_neg h89,
      if_neg (by omega)]
    by_cases hk : k = 8 + zeros
    · subst hk
      rw [if_pos ⟨by omega, le_rfl⟩, startNat_content x w (by omega) (by omega) (by omega)]
      exact hterm
    · rw [if_neg (fun hc => hk (by omega))]

/-! ### The terminator advance -/
private theorem row_srcA (b : Bool) :
    machine.step qSrcA (some b) = (qClearA, some true, .left) := by
  cases b <;> rfl

private theorem row_srcB (b : Bool) :
    machine.step qSrcB (some b) = (qClearB, some true, .left) := by
  cases b <;> rfl

/-- The whole run on a width `2 ≤ zeros`, in all three source shapes, together
with the fact that no earlier step is terminal. -/
private theorem setup_run {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    At (machine.run (exactClock zeros) (startConfig B x w)) qDone
        (8 + zeros + walk (a + m) zeros 2) (loopNat x w zeros 2) ∧
      ∀ s, 2 + zeros < s → s < exactClock zeros →
        (machine.run s (startConfig B x w)).state ≠ qDone ∧
          (machine.run s (startConfig B x w)).state ≠ qReject := by
  obtain ⟨hN, hterm, hfalse⟩ := gamma_cells x w htag hg
  have hfit : ∀ k, k < a + m → k + 1 < tapeLength (pairLength a m) B := by
    intro k hk
    unfold tapeLength pairLength
    omega
  have hcl : exactClock zeros = 2 + zeros + 1 + 1 + 1 + 1 + 1 := by
    unfold exactClock; omega
  have hpre := pre_at (B := B) x w htag hg hz hroom (2 + zeros) le_rfl
  have hst : preState zeros (2 + zeros) = qSrcA := by
    unfold preState
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [hst, show 7 + (2 + zeros) = 9 + zeros by omega] at hpre
  have h0 : At (machine.run (2 + zeros) (startConfig B x w)) qSrcA (9 + zeros)
      (catchNat x w zeros 0 (8 + zeros)) := by
    obtain ⟨hq, hh, ht⟩ := hpre
    exact ⟨hq, hh, fun i => (ht i).trans (pre_eq_catch x w hz hN hterm i.val)⟩
  have hnext0 : catchNat x w zeros 0 (8 + zeros) (9 + zeros) = content x w (9 + zeros) := by
    have h := catch_next x w (zeros := zeros) (trail := 0) (term := 8 + zeros) hz (by omega)
      (by omega)
    rwa [show 8 + zeros + 1 = 9 + zeros by omega] at h
  rw [hcl]
  rcases (show 9 + zeros = a + m ∨ 9 + zeros < a + m by omega) with hP | hP
  · -- Neither source is physical: the terminator never moves.
    have hw : walk (a + m) zeros 2 = 0 := by unfold walk; omega
    have hterm0 : catchNat x w zeros 0 (8 + zeros) (8 + zeros) = some true :=
      catch_true x w (zeros := zeros) (trail := 0) (term := 8 + zeros) (k := 8 + zeros) hz
        (by omega) le_rfl
    have hblank : catchNat x w zeros 0 (8 + zeros) (9 + zeros) = none := by
      rw [hnext0]
      exact content_ge x w (by omega)
    have h1 : At (machine.run (2 + zeros + 1) (startConfig B x w)) qBackA (8 + zeros)
        (catchNat x w zeros 0 (8 + zeros)) :=
      stepAt_left h0 hblank rfl (by omega) hblank (fun _ _ => rfl)
    have h2 : At (machine.run (2 + zeros + 1 + 1) (startConfig B x w)) qOnTerm (8 + zeros)
        (catchNat x w zeros 0 (8 + zeros)) :=
      stepAt_stay h1 hterm0 rfl rfl hterm0 (fun _ _ => rfl)
    have h3 : At (machine.run (2 + zeros + 1 + 1 + 1) (startConfig B x w)) qSrcB (9 + zeros)
        (catchNat x w zeros 0 (8 + zeros)) :=
      stepAt_right h2 hterm0 rfl (by omega) (hfit (8 + zeros) (by omega)) hterm0
        (fun _ _ => rfl)
    have h4 : At (machine.run (2 + zeros + 1 + 1 + 1 + 1) (startConfig B x w)) qBackB
        (8 + zeros) (catchNat x w zeros 0 (8 + zeros)) :=
      stepAt_left h3 hblank rfl (by omega) hblank (fun _ _ => rfl)
    have h5 := stepAt_stay h4 hterm0 rfl (show 8 + zeros = 8 + zeros + walk (a + m) zeros 2
      by omega) hterm0 (fun _ _ => rfl)
    refine ⟨?_, fun s h1' h2' => ?_⟩
    · obtain ⟨hq, hh, ht⟩ := h5
      refine ⟨hq, hh, fun i => (ht i).trans ?_⟩
      rw [loop_eq_catch x w hN i.val, hw, Nat.add_zero]
    · rcases (show s = 2 + zeros + 1 ∨ s = 2 + zeros + 1 + 1 ∨ s = 2 + zeros + 1 + 1 + 1 ∨
          s = 2 + zeros + 1 + 1 + 1 + 1 by omega) with h | h | h | h <;> subst h
      · rw [h1.1]; exact ⟨by decide, by decide⟩
      · rw [h2.1]; exact ⟨by decide, by decide⟩
      · rw [h3.1]; exact ⟨by decide, by decide⟩
      · rw [h4.1]; exact ⟨by decide, by decide⟩
  · -- The first source is physical: the terminator walks to `9 + zeros`.
    obtain ⟨b, hb⟩ := content_lt x w (k := 9 + zeros) (by omega)
    have hsrc : catchNat x w zeros 0 (8 + zeros) (9 + zeros) = some b := by rw [hnext0, hb]
    obtain ⟨hwr1, hkeep1⟩ := catch_step_term x w (zeros := zeros) (trail := 0)
      (term := 8 + zeros) hz (by omega)
    rw [show 8 + zeros + 1 = 9 + zeros by omega] at hwr1 hkeep1
    have h1 : At (machine.run (2 + zeros + 1) (startConfig B x w)) qClearA (8 + zeros)
        (catchNat x w zeros 0 (9 + zeros)) :=
      stepAt_left h0 hsrc (row_srcA b) (by omega) hwr1 (fun i hi => hkeep1 i hi)
    obtain ⟨hwr2, hkeep2⟩ := catch_step_trail x w (zeros := zeros) (trail := 0)
      (term := 9 + zeros) hz
    rw [Nat.add_zero] at hwr2 hkeep2
    have h2 : At (machine.run (2 + zeros + 1 + 1) (startConfig B x w)) qOnTerm (9 + zeros)
        (catchNat x w zeros 1 (9 + zeros)) :=
      stepAt_right h1 (catch_true x w (zeros := zeros) (trail := 0) (term := 9 + zeros)
        (k := 8 + zeros) hz (by omega) (by omega)) rfl (by omega)
        (hfit (8 + zeros) (by omega)) hwr2 (fun i hi => hkeep2 i hi)
    have hterm1 : catchNat x w zeros 1 (9 + zeros) (9 + zeros) = some true :=
      catch_true x w (zeros := zeros) (trail := 1) (term := 9 + zeros) (k := 9 + zeros) hz
        (by omega) le_rfl
    have h3 : At (machine.run (2 + zeros + 1 + 1 + 1) (startConfig B x w)) qSrcB (10 + zeros)
        (catchNat x w zeros 1 (9 + zeros)) :=
      stepAt_right h2 hterm1 rfl (by omega) (hfit (9 + zeros) (by omega)) hterm1
        (fun _ _ => rfl)
    have hnext1 : catchNat x w zeros 1 (9 + zeros) (10 + zeros) =
        content x w (10 + zeros) := by
      have h := catch_next x w (zeros := zeros) (trail := 1) (term := 9 + zeros) hz (by omega)
        (by omega)
      rwa [show 9 + zeros + 1 = 10 + zeros by omega] at h
    rcases (show 10 + zeros = a + m ∨ 10 + zeros < a + m by omega) with hQ | hQ
    · -- The second source is the boundary blank: the terminator stays put.
      have hw : walk (a + m) zeros 2 = 1 := by unfold walk; omega
      have hblank : catchNat x w zeros 1 (9 + zeros) (10 + zeros) = none := by
        rw [hnext1]
        exact content_ge x w (by omega)
      have h4 : At (machine.run (2 + zeros + 1 + 1 + 1 + 1) (startConfig B x w)) qBackB
          (9 + zeros) (catchNat x w zeros 1 (9 + zeros)) :=
        stepAt_left h3 hblank rfl (by omega) hblank (fun _ _ => rfl)
      have h5 := stepAt_stay h4 hterm1 rfl (show 9 + zeros = 8 + zeros + walk (a + m) zeros 2
        by omega) hterm1 (fun _ _ => rfl)
      refine ⟨?_, fun s h1' h2' => ?_⟩
      · obtain ⟨hq, hh, ht⟩ := h5
        refine ⟨hq, hh, fun i => (ht i).trans ?_⟩
        rw [loop_eq_catch x w hN i.val, hw, show 8 + zeros + 1 = 9 + zeros by omega]
      · rcases (show s = 2 + zeros + 1 ∨ s = 2 + zeros + 1 + 1 ∨ s = 2 + zeros + 1 + 1 + 1 ∨
            s = 2 + zeros + 1 + 1 + 1 + 1 by omega) with h | h | h | h <;> subst h
        · rw [h1.1]; exact ⟨by decide, by decide⟩
        · rw [h2.1]; exact ⟨by decide, by decide⟩
        · rw [h3.1]; exact ⟨by decide, by decide⟩
        · rw [h4.1]; exact ⟨by decide, by decide⟩
    · -- Both sources are physical: the terminator walks two cells.
      have hw : walk (a + m) zeros 2 = 2 := by unfold walk; omega
      obtain ⟨c, hc⟩ := content_lt x w (k := 10 + zeros) (by omega)
      have hsrc2 : catchNat x w zeros 1 (9 + zeros) (10 + zeros) = some c := by
        rw [hnext1, hc]
      obtain ⟨hwr3, hkeep3⟩ := catch_step_term x w (zeros := zeros) (trail := 1)
        (term := 9 + zeros) hz (by omega)
      rw [show 9 + zeros + 1 = 10 + zeros by omega] at hwr3 hkeep3
      have h4 : At (machine.run (2 + zeros + 1 + 1 + 1 + 1) (startConfig B x w)) qClearB
          (9 + zeros) (catchNat x w zeros 1 (10 + zeros)) :=
        stepAt_left h3 hsrc2 (row_srcB c) (by omega) hwr3 (fun i hi => hkeep3 i hi)
      obtain ⟨hwr4, hkeep4⟩ := catch_step_trail x w (zeros := zeros) (trail := 1)
        (term := 10 + zeros) hz
      rw [show 8 + zeros + 1 = 9 + zeros by omega] at hwr4 hkeep4
      have h5 := stepAt_right h4 (catch_true x w (zeros := zeros) (trail := 1)
        (term := 10 + zeros) (k := 9 + zeros) hz (by omega) (by omega)) rfl
        (show 9 + zeros + 1 = 8 + zeros + walk (a + m) zeros 2 by omega)
        (hfit (9 + zeros) (by omega)) hwr4 (fun i hi => hkeep4 i hi)
      refine ⟨?_, fun s h1' h2' => ?_⟩
      · obtain ⟨hq, hh, ht⟩ := h5
        refine ⟨hq, hh, fun i => (ht i).trans ?_⟩
        rw [loop_eq_catch x w hN i.val, hw, show 8 + zeros + 2 = 10 + zeros by omega]
      · rcases (show s = 2 + zeros + 1 ∨ s = 2 + zeros + 1 + 1 ∨ s = 2 + zeros + 1 + 1 + 1 ∨
            s = 2 + zeros + 1 + 1 + 1 + 1 by omega) with h | h | h | h <;> subst h
        · rw [h1.1]; exact ⟨by decide, by decide⟩
        · rw [h2.1]; exact ⟨by decide, by decide⟩
        · rw [h3.1]; exact ⟨by decide, by decide⟩
        · rw [h4.1]; exact ⟨by decide, by decide⟩

private theorem malformed_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    At (machine.run s (startConfig B x w)) qReject (a + m) (content x w) := by
  obtain ⟨-, hh0, ht0⟩ :=
    FixedGammaTargetSecondPayload.malformed_at_deadline (B := B) x w htag hg
  have hbase : At (machine.run 0 (startConfig B x w)) qStart (a + m) (content x w) := by
    refine ⟨rfl, hh0, fun i => ?_⟩
    show (FixedGammaTargetSecondPayload.machine.run _ _).tape i = _
    rw [ht0]
    exact contentTape_eq x w i
  exact At_absorb (stepAt_stay hbase (content_ge x w le_rfl) rfl rfl (content_ge x w le_rfl)
    (fun _ _ => rfl)) (Or.inr rfl) s (by omega)

/-! ### Public execution theorems -/

/-- **The execution theorem of this slice.**  On a matching tag, a decoded width
`2 ≤ zeros`, and the inherited G2p-c room premise, the machine has from step
`exactClock zeros = zeros + 7` on halted in the absorbing `qDone` at head
`8 + zeros + walk (a + m) zeros 2` with tape `loopTape B x w zeros 2`: both
consumed gamma zeros marked, the terminator trail blank, the walking terminator on
the next source's left neighbour, and the three inherited register digits
untouched — the register still holds exactly the three digits it inherited.  Head
and tape cover all three source shapes at once, and `markers_strict` supplies the
first-arrival direction.  `qDone` is an internal endpoint, not language acceptance,
and there is deliberately no converse. -/
theorem markers_installed {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 8 + zeros + walk (a + m) zeros 2 ∧
      d.tape = loopTape B x w zeros 2 := by
  obtain ⟨hq, hh, ht⟩ :=
    At_absorb (setup_run (B := B) x w htag hg hzeros hroom).1 (Or.inl rfl) s hs
  exact ⟨hq, hh, funext fun i => (ht i).trans (loopTape_eq x w zeros 2 i).symm⟩

/-- `exactClock zeros = zeros + 7` is the *first* terminal time of a width
`2 ≤ zeros`: before it the control is in neither terminal state, so this is a
genuine exact first arrival and not merely a time by which the run has halted. -/
theorem markers_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s < exactClock zeros) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject := by
  rcases Nat.lt_or_ge (2 + zeros) s with h | h
  · exact (setup_run (B := B) x w htag hg hzeros hroom).2 s h hs
  · obtain ⟨hq, -, -⟩ := pre_at (B := B) x w htag hg hzeros hroom s h
    show (machine.run s (startConfig B x w)).state ≠ qDone ∧
      (machine.run s (startConfig B x w)).state ≠ qReject
    rw [hq]
    unfold preState
    split_ifs <;> exact ⟨by decide, by decide⟩

/-- The same endpoint at the length-only deadline `deadline N = N` of this phase,
which is not a clock for the composed pipeline: it omits every step embedded in
`startConfig`. -/
theorem markers_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 8 + zeros + walk (a + m) zeros 2 ∧
      d.tape = loopTape B x w zeros 2 := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  exact markers_installed x w htag hg hzeros hroom _ (exactClock_le_deadline hN)

/-- A failed gamma scan: the retagged G2p-c rejection rejects again in one step,
at the boundary head `a + m`, on the unchanged content tape.  No room premise is
needed, and this is not a converse — nothing here says that `qReject` implies a
malformed gamma. -/
theorem malformed_rejects {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : malformedExactClock ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hq, hh, ht⟩ := malformed_at (B := B) x w htag hg s hs
  exact ⟨hq, hh, funext fun i => (ht i).trans (contentTape_eq x w i).symm⟩

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation
