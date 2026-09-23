import Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion

/-!
Surface pins for the Part A G2p-f exhaustion finish of the gamma payload loop.  There is
**no new machine**: every theorem below runs the landed G2p-d
`FixedGammaTargetPayloadRound.machine`, whose 22 states and 66 rows are pinned by that
module's own surface test and are unchanged here.  `check_machine_reused` records the
identity and the five rows this phase executes.

What is new and pinned here.  Out of the `r = zeros` instance of the loop invariant —
G2p-e's `register_complete` endpoint, where every gamma zero carries a consumed-source mark
— the `qCntL` row for `some true` fires the stopping rule into `qFin`, `qFin` sweeps the
counter field back to `some false`, and the machine halts on the tag cell `7` in `qDone`
after exactly `exhaustClock (a+m) zeros = termWalk (a+m) zeros + zeros + 2` steps
(`exhaust_generic`).  `finishTape_pins` says what that endpoint tape is: the gamma zero
field `[7, 8+zeros)` restored to the incoming content tape, and the incoming invariant
everywhere else — consumed sources still blank, walking terminator still standing, register
still holding its `zeros + 1` digits — so it is **not** `contentTape`.  `exhaust_schedule`
pins the control through the phase, `exhaust_strict` pins both that the endpoint persists
(`qDone` absorbs) and that `exhaustClock` is the *first* arrival, and `payload_exhausted`
composes with G2p-e into one exact run from the landed `startConfig` at
`totalClock (a+m) zeros`.

Not here and not available to pin: the decrement from `n+1` digits to `n`, the completion
of the register (that is G2p-e's; this slice only preserves it), any reading of the register
as a number or any claim that a truncated payload's virtual `false` digits are its value, any `contentHeader?` or parsed header value, any pnp4 bridge, a
footprint/budget theorem (so no room premise is shown necessary), any converse, first
arrival measured from `startConfig` rather than from the `r = zeros` configuration, the
degenerate widths `zeros ≤ 1`, and any language statement — `qDone` is an internal control
tag of a machine started here from a phase-local retag of an actual prior run, so it is
neither halting of a composed machine nor language acceptance. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetPayloadExhaustionSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion
open Complexity.Uniform.V1.FixedGammaTargetPayloadIteration (loopClock)
open Complexity.Uniform.V1.FixedGammaTargetPayloadRound (stateCount machine qLoop qCntL qFin
  qDone qReject roundClock startConfig)
open Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation (walk registerBit loopTape)

/-- The machine executed by every theorem of this slice is the landed G2p-d round machine,
not a copy and not a new table.  The first conjunct is a tautology on its face — `machine`
is opened from `FixedGammaTargetPayloadRound` above, so both sides are literally the same
constant — and recording that alias is all it does.  What pins the reuse is that the
wrappers below restate this module's theorems in full against that opened `machine`: had the
exhaustion module introduced a table of its own, its theorems would be stated over that
table and these restatements would not typecheck.  The remaining conjuncts pin the resource
counts, the endpoints, and the five rows the finish actually runs. -/
theorem check_machine_reused :
    machine = FixedGammaTargetPayloadRound.machine ∧ machine.stateCount = 22 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 66 ∧
      machine.start = qLoop ∧ machine.accept = qDone ∧ machine.reject = qReject ∧
      machine.step qLoop (some true) = (qCntL, some true, .left) ∧
      machine.step qCntL none = (qCntL, none, .left) ∧
      machine.step qCntL (some true) = (qFin, some false, .left) ∧
      machine.step qFin (some true) = (qFin, some false, .left) ∧
      machine.step qFin (some false) = (qDone, some false, .stay) ∧
      (∀ s, machine.step qDone s = (qDone, s, .stay)) :=
  machine_reused

def check_termWalk (N zeros : Nat) : Nat := termWalk N zeros
def check_exhaustClock (N zeros : Nat) : Nat := exhaustClock N zeros
def check_totalClock (N zeros : Nat) : Nat := totalClock N zeros

def check_finishTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := finishTape B x w zeros

theorem check_clock_pins (N zeros : Nat) :
    termWalk N zeros = walk N zeros zeros ∧
      exhaustClock N zeros = termWalk N zeros + zeros + 2 ∧
      totalClock N zeros = loopClock N zeros + exhaustClock N zeros ∧
      totalClock N zeros = (zeros - 2) * roundClock N + exhaustClock N zeros ∧
      (9 + 2 * zeros ≤ N → exhaustClock N zeros = 2 * zeros + 2) ∧
      (9 + zeros ≤ N → N ≤ 9 + 2 * zeros → exhaustClock N zeros = N - 7) ∧
      (9 + zeros ≤ N → exhaustClock N zeros ≤ roundClock N) :=
  clock_pins N zeros

/-- The literal clocks the two probes below execute, pinned by kernel reduction.  The finish
cost differs between the two shapes — `10` against `8` — which is the concrete form of
`exhaustClock` not being length-only. -/
theorem check_clock_values :
    termWalk 17 4 = 4 ∧ exhaustClock 17 4 = 10 ∧ loopClock 17 4 = 54 ∧ totalClock 17 4 = 64 ∧
      termWalk 15 4 = 2 ∧ exhaustClock 15 4 = 8 ∧ loopClock 15 4 = 46 ∧
      totalClock 15 4 = 54 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- What the finish restores and what it leaves alone, restated in full. -/
theorem check_finishTape_pins {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
        i.val = a + m + 1 + j →
        finishTape B x w zeros i = some (registerBit x w zeros j)) :=
  finishTape_pins x w htag hg

/-- The control schedule of the finish, restated in full: `qLoop`, then `qCntL` over the
blank trail, then `qFin` from the stopping rule to the halt, with the head walking
monotonically left to `7`.  With `check_exhaust_generic` these conjuncts name the control at
every time up to and including the halt, so no source state and no register state is
entered. -/
theorem check_exhaust_schedule {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
        (machine.run t c).state = qFin) :=
  exhaust_schedule x w htag hg hz c hq hh ht

/-- The exhaustion finish out of an arbitrary `r = zeros` configuration, restated in full:
no room premise, exact cost `exhaustClock (a+m) zeros`, endpoint `qDone` on cell `7` with the
whole tape equal to `finishTape`. -/
theorem check_exhaust_generic {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 1 ≤ zeros) (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = 8 + zeros + termWalk (a + m) zeros)
    (ht : c.tape = loopTape B x w zeros zeros) :
    let d := machine.run (exhaustClock (a + m) zeros) c
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = finishTape B x w zeros :=
  exhaust_generic x w htag hg hz c hq hh ht

/-- First arrival and the all-times clamp, restated in full.  Both directions are proved:
`qDone` is not entered before `exhaustClock (a+m) zeros`, and from that time on the
configuration is constant. -/
theorem check_exhaust_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
          (machine.run t c).tape = finishTape B x w zeros) :=
  exhaust_strict x w htag hg hz c hq hh ht

/-- The concrete exact run out of the landed G2p-d `startConfig`, restated in full.  The
register conjunct is preservation, not completion: register completion is G2p-e's
`register_complete`, and no conjunct here decodes the digits or claims that the virtual
`false`s of a truncated payload are its value. -/
theorem check_payload_exhausted {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
      (∀ t, totalClock (a + m) zeros ≤ t → machine.run t (startConfig B x w) = d) :=
  payload_exhausted x w htag hg hzeros hroom

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's execution theorems.
`check_*_handoff` first identifies the *actual* phase-local start configuration with an
explicit configuration for every budget, using only the landed G2p-d foundation endpoint
theorem and the definitional `retagLoopFoundation` handoff; then, at `B = 0`, the landed
round machine's own `machine.run` is reduced by kernel computation on it, across the two
remaining rounds **and** the finish.  Each probe is a claim about its own input.  The tag is
`10110010` and both words decode to `zeros = 4`, so exactly `zeros - 2 = 2` rounds remain and
the payload block is `[13, 17)`.  `physWord` has `N = 17` and a physically present payload;
`virtWord` has `N = 15`, where the payload is truncated after two digits.  Both probes run
past the endpoint as well, which exhibits `qDone` absorbing. -/

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
each decodes to `zeros = 4` behind a matching tag, and at the probes' own budget `B = 0`
each allocates the whole completed register `[a+m+1, a+m+1+zeros]`, which is
`payload_exhausted`'s room premise.  So none of the theorems above is a statement about an
unsatisfiable hypothesis set. -/
theorem check_probe_inputs_valid :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      8 + 9 + 1 + 4 < tapeLength (pairLength 8 9) 0 ∧
      FixedContentTagGate.tagMatches (Fin.append tag virtWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag virtWord) = some 4 ∧
      8 + 7 + 1 + 4 < tapeLength (pairLength 8 7) 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 1000000 in
/-- The physical shape (`N = 17`, `loopClock 17 4 = 54`, `termWalk 17 4 = 4`,
`exhaustClock 17 4 = 10`, `totalClock 17 4 = 64`).  At step fifty-four the two remaining
rounds are done and the head stands on the walking terminator `16`; the finish then scans
left in `qCntL`, from `15` at step fifty-five to the last counter mark `11` at step
fifty-nine, enters `qFin` at step sixty on cell `10` — so the stopping rule fired on a
*mark*, not on an unconsumed zero, the only `qCntL` row into `qFin` being the `some true`
one — sweeps back to cell `7` at step sixty-three, and halts in `qDone` on `7` at step
sixty-four.  The endpoint pins the restoration cell by cell: the tag cell `7` and every
gamma zero `8,9,10,11` read `some false` again.  It also pins what was *not* restored: the
whole four-cell trail `[12,16)` of consumed sources is blank — cell `13`'s input bit is
`true` — and the walking terminator stands at `16`.  The register `[18,22]` still holds `true, true, false, false, true`.  Steps
sixty-five and seventy show `qDone` absorbing. -/
theorem check_phys_probe :
    (machine.run 54 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 54 (startConfig 0 tag physWord)).head.val = 16 ∧
    (machine.run 55 (startConfig 0 tag physWord)).state = qCntL ∧
    (machine.run 55 (startConfig 0 tag physWord)).head.val = 15 ∧
    (machine.run 59 (startConfig 0 tag physWord)).state = qCntL ∧
    (machine.run 59 (startConfig 0 tag physWord)).head.val = 11 ∧
    (machine.run 60 (startConfig 0 tag physWord)).state = qFin ∧
    (machine.run 60 (startConfig 0 tag physWord)).head.val = 10 ∧
    (machine.run 63 (startConfig 0 tag physWord)).state = qFin ∧
    (machine.run 63 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 64 (startConfig 0 tag physWord)).state = qDone ∧
    (machine.run 64 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨8, by decide⟩ = some false ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨9, by decide⟩ = some false ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨10, by decide⟩ = some false ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨11, by decide⟩ = some false ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨12, by decide⟩ = none ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨13, by decide⟩ = none ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨14, by decide⟩ = none ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨15, by decide⟩ = none ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨21, by decide⟩ = some false ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 65 (startConfig 0 tag physWord)).state = qDone ∧
    (machine.run 70 (startConfig 0 tag physWord)).state = qDone ∧
    (machine.run 70 (startConfig 0 tag physWord)).head.val = 7 := by
  rw [check_phys_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 1000000 in
/-- The truncated shape (`N = 15`, `loopClock 15 4 = 46`, `termWalk 15 4 = 2`,
`exhaustClock 15 4 = 8`, `totalClock 15 4 = 54`).  Only two of the four sources were
physical, so the blank trail is `[12,14)` — both cells pinned blank — and the walking
terminator stands at `14`; the finish is correspondingly two steps cheaper than in the
physical shape.  At step forty-seven the `qCntL` scan is on `13`, at step forty-nine on the
last counter mark `11`, at step fifty it is in `qFin` on `10`, and
it halts in `qDone` on `7` at step fifty-four with the tag cell and all four gamma zeros back
to `some false`.  Cell `14` pins that the endpoint is not the content tape: its input bit is
`false` and it now carries the walking terminator's `some true`.  The register `[16,20]`
still holds `true, true, false, false, false`, its last two digits the virtual zeros of the
truncated payload.  Steps fifty-five and sixty show `qDone` absorbing. -/
theorem check_virt_probe :
    (machine.run 46 (startConfig 0 tag virtWord)).state = qLoop ∧
    (machine.run 46 (startConfig 0 tag virtWord)).head.val = 14 ∧
    (machine.run 47 (startConfig 0 tag virtWord)).state = qCntL ∧
    (machine.run 47 (startConfig 0 tag virtWord)).head.val = 13 ∧
    (machine.run 49 (startConfig 0 tag virtWord)).state = qCntL ∧
    (machine.run 49 (startConfig 0 tag virtWord)).head.val = 11 ∧
    (machine.run 50 (startConfig 0 tag virtWord)).state = qFin ∧
    (machine.run 50 (startConfig 0 tag virtWord)).head.val = 10 ∧
    (machine.run 53 (startConfig 0 tag virtWord)).state = qFin ∧
    (machine.run 53 (startConfig 0 tag virtWord)).head.val = 7 ∧
    (machine.run 54 (startConfig 0 tag virtWord)).state = qDone ∧
    (machine.run 54 (startConfig 0 tag virtWord)).head.val = 7 ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨8, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨9, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨10, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨11, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨12, by decide⟩ = none ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨13, by decide⟩ = none ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨17, by decide⟩ = some true ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨18, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨19, by decide⟩ = some false ∧
    (machine.run 54 (startConfig 0 tag virtWord)).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 55 (startConfig 0 tag virtWord)).state = qDone ∧
    (machine.run 60 (startConfig 0 tag virtWord)).state = qDone ∧
    (machine.run 60 (startConfig 0 tag virtWord)).head.val = 7 := by
  rw [check_virt_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

end Pnp3.Tests.UniformV1FixedGammaTargetPayloadExhaustionSurfaceTests
