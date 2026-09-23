import Complexity.Uniform.V1.FixedGammaTargetPayloadIteration

/-!
Surface pins for the Part A G2p-e iteration of the gamma payload round.  There is **no new
machine**: every theorem below runs the landed G2p-d `FixedGammaTargetPayloadRound.machine`,
whose 22 states and 66 rows are pinned by that module's own surface test and are unchanged
here; `check_machine_reused` pins the reuse itself.

What is new and pinned here: `round_generic` carries the loop invariant `loopTape B x w zeros r`
from `r` to `r + 1` out of an **arbitrary** configuration matching the `r`-instance, at every
index `1 ≤ r < zeros`, in exactly `roundClock (a+m) = 2*(a+m)-7` steps; `rounds_iterate` runs
that round `k` times out of the landed `startConfig`; and `register_complete` is its
`k = zeros - 2` instance, where the target register `[a+m+1, a+m+1+zeros]` holds all
`zeros + 1` digits.  `qLoop` does not absorb, so each is an *exact* time and no wrapper pins
any endpoint later; there is no phase deadline, no first-arrival/strictness direction and no
converse to pin.

Not here and not available to pin: the exhaustion finish (`qFin`/`qDone` and the restoration of
the gamma zero field), the loop's own deadline, the decrement from `n+1` to `n`, the all-times
clamp/footprint/budget package, any parsed header value, any pnp4 bridge, and any language
statement — `qDone` is not language acceptance and `startConfig` is a phase-local retag of an
actual prior run, not a composed execution from the raw pair input. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetPayloadIterationSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetPayloadIteration
open Complexity.Uniform.V1.FixedGammaTargetPayloadRound (stateCount machine qLoop qCntMark qSrc
  qClear0 qClear1 qVa qVb qVc roundClock startConfig)
open Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation (walk registerBit loopTape)

/-- The machine executed by every theorem of this slice is the landed G2p-d round machine,
not a copy and not a new table.  The first conjunct is a tautology on its face — `machine` is
opened from `FixedGammaTargetPayloadRound` above, so both sides are literally the same
constant — and recording that alias is all it does.  What pins the reuse is that the wrappers
below restate this module's theorems in full against that opened `machine`: had the iteration
module introduced a table of its own, its theorems would be stated over that table and these
restatements — written against the round module's `machine` — would not typecheck.  The
remaining conjuncts pin the reused resource counts and endpoints. -/
theorem check_machine_reused :
    machine = FixedGammaTargetPayloadRound.machine ∧ machine.stateCount = 22 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 66 ∧
      machine.start = qLoop ∧ machine.accept = FixedGammaTargetPayloadRound.qDone ∧
      machine.reject = FixedGammaTargetPayloadRound.qReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def check_loopClock (N zeros : Nat) : Nat := loopClock N zeros

theorem check_loopClock_pins (N zeros : Nat) :
    loopClock N zeros = (zeros - 2) * roundClock N ∧ roundClock N = 2 * N - 7 ∧
      loopClock N 2 = 0 ∧ loopClock N 3 = 2 * N - 7 ∧
      loopClock N 4 = 2 * (2 * N - 7) :=
  loopClock_pins N zeros

/-- The two literal clocks the probes below execute, pinned by kernel reduction. -/
theorem check_loopClock_values :
    roundClock 17 = 27 ∧ loopClock 17 4 = 54 ∧ roundClock 15 = 23 ∧ loopClock 15 4 = 46 := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> rfl

theorem check_room_iff (a m B zeros r : Nat) :
    (a + m + 1 + zeros < tapeLength (pairLength a m) B ↔ zeros ≤ a + B) ∧
      (a + m + 2 + r < tapeLength (pairLength a m) B ↔ r < a + B) ∧
      (2 ≤ zeros → a + m + 1 + zeros < tapeLength (pairLength a m) B →
        a + m + 3 < tapeLength (pairLength a m) B) ∧
      (3 ≤ zeros → a + m + 1 + zeros < tapeLength (pairLength a m) B →
        a + m + 4 < tapeLength (pairLength a m) B) ∧
      (r + 1 ≤ zeros → a + m + 1 + zeros < tapeLength (pairLength a m) B →
        a + m + 2 + r < tapeLength (pairLength a m) B) :=
  room_iff a m B zeros r

theorem check_register_digits {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    registerBit x w zeros 0 = true ∧
      (∀ i, i < zeros → registerBit x w zeros (i + 1) =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + i)).getD false) ∧
      (∀ i, i < zeros → 9 + zeros ≤ 9 + zeros + i ∧ 9 + zeros + i < 9 + 2 * zeros) ∧
      (∀ k, (9 + zeros ≤ k ∧ k < 9 + 2 * zeros) ↔ ∃ i, i < zeros ∧ k = 9 + zeros + i) :=
  register_digits x w zeros

/-- The reusable round, restated in full: arbitrary index `r`, arbitrary incoming
configuration matching the `r`-instance, exact cost `roundClock (a+m)`. -/
theorem check_round_generic {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hr : 1 ≤ r) (hrz : r < zeros)
    (hroom : a + m + 2 + r < tapeLength (pairLength a m) B)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = 8 + zeros + walk (a + m) zeros r)
    (ht : c.tape = loopTape B x w zeros r) :
    let d := machine.run (roundClock (a + m)) c
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros (r + 1) ∧
      d.tape = loopTape B x w zeros (r + 1) :=
  round_generic x w htag hg hr hrz hroom c hq hh ht

/-- The landed hard-coded round is recovered from the generic one: `round_step`'s statement —
the `r = 2 → r = 3` step out of `startConfig` under `3 ≤ zeros` and the round slice's own room
`a+m+4 < tapeLength (pairLength a m) B` — is the `r = 2` instance of `round_generic` applied to
the G2p-d foundation endpoint, under exactly those premises.  So the generic round is a strict
generalisation of the landed one, not a parallel claim beside it. -/
theorem check_round_generic_subsumes_round_step {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 3 ≤ zeros) (hroom : a + m + 4 < tapeLength (pairLength a m) B) :
    let d := machine.run (roundClock (a + m)) (startConfig B x w)
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros 3 ∧
      d.tape = loopTape B x w zeros 3 :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetPayloadLoopFoundation.markers_at_deadline
    (B := B) x w htag hg (by omega) (by omega)
  round_generic (r := 2) x w htag hg (by omega) (by omega) (by omega)
    (startConfig B x w) rfl hh ht

/-- `k` rounds out of the landed G2p-d start configuration. -/
theorem check_rounds_iterate {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B)
    (k : Nat) (hk : 2 + k ≤ zeros) :
    let d := machine.run (k * roundClock (a + m)) (startConfig B x w)
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros (2 + k) ∧
      d.tape = loopTape B x w zeros (2 + k) :=
  rounds_iterate x w htag hg hzeros hroom k hk

/-- The complete target register at the exact time `loopClock (a+m) zeros`. -/
theorem check_register_complete {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    let d := machine.run (loopClock (a + m) zeros) (startConfig B x w)
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros zeros ∧
      d.tape = loopTape B x w zeros zeros ∧
      (∀ j : Nat, j ≤ zeros → a + m + 1 + j < tapeLength (pairLength a m) B) ∧
      ∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j → d.tape i = some (registerBit x w zeros j) :=
  register_complete x w htag hg hzeros hroom

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's execution theorems.
`check_*_handoff` first identifies the *actual* phase-local start configuration with an
explicit configuration for every budget, using only the landed G2p-d foundation endpoint
theorem and the definitional `retagLoopFoundation` handoff; then, at `B = 0`, the landed round
machine's own `machine.run` is reduced by kernel computation on it, for **two** consecutive
rounds.  Each probe is a claim about its own input.  The tag is `10110010` and both words
decode to `zeros = 4`, so exactly two rounds remain (`zeros - 2 = 2`) and the payload block is
`[13, 17)`.  `physWord` has `N = 17`, so both remaining sources — cells `15` and `16` — are
physical content cells carrying `false` and then `true`, which exercises both carried-bit
halves of the table; `virtWord` has `N = 15`, where the payload is truncated after two digits
and both remaining source addresses are the boundary blank `15`, so the terminator never moves
again and the two appended digits are virtual zeros. -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def virtWord : Bitstring 7 := ![false, false, false, false, true, true, false]

/-- Rebuild a configuration from its three projections.  Stated over a configuration
*variable*, so that identifying the phase-local start configuration never has to reduce the
foundation run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) :
    c = ⟨q, ⟨k, hk⟩, T⟩ := by
  obtain ⟨cs, ch, ct⟩ := c
  cases hq
  cases ht
  exact congrArg (fun h => (⟨cs, h, ct⟩ : Config K n B)) (Fin.ext hh)

theorem check_phys_handoff (B : Nat) :
    startConfig B tag physWord =
      ⟨qLoop, ⟨14, by unfold tapeLength pairLength; omega⟩,
        loopTape B tag physWord 4 2⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetPayloadLoopFoundation.markers_at_deadline
    (B := B) (zeros := 4) tag physWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl (hh.trans (by decide)) ht

theorem check_virt_handoff (B : Nat) :
    startConfig B tag virtWord =
      ⟨qLoop, ⟨14, by unfold tapeLength pairLength; omega⟩,
        loopTape B tag virtWord 4 2⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetPayloadLoopFoundation.markers_at_deadline
    (B := B) (zeros := 4) tag virtWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl (hh.trans (by decide)) ht

/-- Both probe inputs really do satisfy the hypotheses the general theorems above assume:
each decodes to `zeros = 4` behind a matching tag, and at the probes' own budget `B = 0` each
allocates the whole completed register `[a+m+1, a+m+1+zeros]` — which is `rounds_iterate`'s
room premise, and implies every single round's.  So `round_generic`, `rounds_iterate` and
`register_complete` are not statements about an unsatisfiable hypothesis set. -/
theorem check_probe_inputs_valid :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      8 + 9 + 1 + 4 < tapeLength (pairLength 8 9) 0 ∧
      FixedContentTagGate.tagMatches (Fin.append tag virtWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag virtWord) = some 4 ∧
      8 + 7 + 1 + 4 < tapeLength (pairLength 8 7) 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 400000 in
/-- Two physical rounds (`N = 17`, `roundClock 17 = 27`, `loopClock 17 4 = 54`).  Round one
has the head on its physical source `15` in `qSrc` at step eleven and carries the `false`
there in the control (`qClear0` at step twelve), then ends at step twenty-seven in `qLoop` on
the advanced terminator `15`, with the third counter mark at `10`, the vacated `14` blank and
a `false` appended at `21`.  Round two is in `qCntMark` on the next counter cell `11` at step
thirty-three, has the head on its physical source `16` in `qSrc` at step thirty-eight and
carries the `true` there in the control (`qClear1` at step thirty-nine), and ends at step
fifty-four in `qLoop` on the advanced terminator `16`, whose `some true` mark is pinned
there, with the vacated `15` blank and the register `[18, 22]` holding
`true, true, false, false, true`.  The two rounds therefore drive both carried-bit
halves of the table. -/
theorem check_phys_probe :
    (machine.run 11 (startConfig 0 tag physWord)).state = qSrc ∧
    (machine.run 11 (startConfig 0 tag physWord)).head.val = 15 ∧
    (machine.run 12 (startConfig 0 tag physWord)).state = qClear0 ∧
    (machine.run 27 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 27 (startConfig 0 tag physWord)).head.val = 15 ∧
    (machine.run 27 (startConfig 0 tag physWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 27 (startConfig 0 tag physWord)).tape ⟨14, by decide⟩ = none ∧
    (machine.run 27 (startConfig 0 tag physWord)).tape ⟨21, by decide⟩ = some false ∧
    (machine.run 33 (startConfig 0 tag physWord)).state = qCntMark ∧
    (machine.run 33 (startConfig 0 tag physWord)).head.val = 11 ∧
    (machine.run 38 (startConfig 0 tag physWord)).state = qSrc ∧
    (machine.run 38 (startConfig 0 tag physWord)).head.val = 16 ∧
    (machine.run 39 (startConfig 0 tag physWord)).state = qClear1 ∧
    (machine.run 54 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 54 (startConfig 0 tag physWord)).head.val = 16 ∧
    (machine.run 54 (startConfig 0 tag physWord)).tape ⟨15, by decide⟩ = none ∧
    (machine.run 54 (startConfig 0 tag physWord)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 54 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 54 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 54 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag physWord)).tape ⟨21, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true := by
  rw [check_phys_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 400000 in
/-- Two truncated rounds (`N = 15`, `roundClock 15 = 23`, `loopClock 15 4 = 46`).  Round one
ends at step twenty-three in `qLoop` on the *unmoved* terminator `14`, with the third counter
mark at `10` and a virtual `false` appended at `19`.  Round two is in `qCntMark` on the next
counter cell `11` at step twenty-eight, has the head on the boundary cell `15` in `qSrc` at
step thirty-two, pads through
`qVa`/`qVb` at steps thirty-three and thirty-four and `qVc` at step forty-five, and ends at
step forty-six in `qLoop` still on `14` — whose `some true` mark is pinned there.  The
boundary cell `15` is pinned still blank at that endpoint, and the register `[16, 20]` holds
`true, true, false, false, false`. -/
theorem check_virt_probe :
    (machine.run 23 (startConfig 0 tag virtWord)).state = qLoop ∧
    (machine.run 23 (startConfig 0 tag virtWord)).head.val = 14 ∧
    (machine.run 23 (startConfig 0 tag virtWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 23 (startConfig 0 tag virtWord)).tape ⟨19, by decide⟩ = some false ∧
    (machine.run 28 (startConfig 0 tag virtWord)).state = qCntMark ∧
    (machine.run 28 (startConfig 0 tag virtWord)).head.val = 11 ∧
    (machine.run 32 (startConfig 0 tag virtWord)).state = qSrc ∧
    (machine.run 32 (startConfig 0 tag virtWord)).head.val = 15 ∧
    (machine.run 33 (startConfig 0 tag virtWord)).state = qVa ∧
    (machine.run 34 (startConfig 0 tag virtWord)).state = qVb ∧
    (machine.run 45 (startConfig 0 tag virtWord)).state = qVc ∧
    (machine.run 46 (startConfig 0 tag virtWord)).state = qLoop ∧
    (machine.run 46 (startConfig 0 tag virtWord)).head.val = 14 ∧
    (machine.run 46 (startConfig 0 tag virtWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 46 (startConfig 0 tag virtWord)).tape ⟨15, by decide⟩ = none ∧
    (machine.run 46 (startConfig 0 tag virtWord)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 46 (startConfig 0 tag virtWord)).tape ⟨17, by decide⟩ = some true ∧
    (machine.run 46 (startConfig 0 tag virtWord)).tape ⟨18, by decide⟩ = some false ∧
    (machine.run 46 (startConfig 0 tag virtWord)).tape ⟨19, by decide⟩ = some false ∧
    (machine.run 46 (startConfig 0 tag virtWord)).tape ⟨20, by decide⟩ = some false := by
  rw [check_virt_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

end Pnp3.Tests.UniformV1FixedGammaTargetPayloadIterationSurfaceTests
