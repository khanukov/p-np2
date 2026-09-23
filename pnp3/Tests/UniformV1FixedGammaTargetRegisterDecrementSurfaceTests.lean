import Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement

/-!
Surface pins for the Part A G2q register decrement: a **new** fixed 7-state, 21-row machine that
subtracts one from the target register the G2p-e/G2p-f loop left on the tape.  All 21 transition
rows are restated literally below, not aliased.

What is pinned.  The navigation is symbol-driven throughout — `qSeekTerm` stops on the walking
terminator's `some true`, `qSeekGap` on the boundary blank, `qRegEnd` on the blank past the
register — and the borrow flips the low run of `false` digits, clears the `true` that stops it and
halts there (`check_decrement_generic`).  `decClock (a+m) zeros d = a+m+zeros+d-3` is exact and
`deadline (a+m) = 3*(a+m)` is the length-only bound it meets (`check_clock_pins`);
`check_decrement_strict` pins the all-times clamp and first arrival; `check_register_decremented`
runs the phase out of the phase-local `startConfig`, whose handoff time
`priorDeadline (a+m) = 3*((a+m)*(a+m))` is length-only and covers G2p-f's exact endpoint time
(`check_prior_covers`).  `check_borrow_pins` produces the borrow length from the digits, and
`check_sub_one_bits`/`check_decBit_sub_one` are the arithmetic saying that the endpoint digits are
the digits of `v - 1` for an arbitrary `v` whose bits are the incoming ones.

Not here and not available to pin: any pnp4 bridge, and with it every connection to
`contentHeader?`, `contentInput?`, or a parsed target — nothing supplies the `v` of
`check_decBit_sub_one`, whose `check_decBit_sub_one_instance` value is a hand-written literal; a
footprint or budget theorem, so no room premise is shown necessary; every converse — no wrapper
says that `qDone`, or an endpoint cell, implies anything about `zeros`, about the borrow length,
or about the incoming digits; a malformed-gamma branch; the handoff of this endpoint onward; and
any restoration of the gamma leading-digit convention, which the borrow clears when the register
holds exactly `2 ^ zeros`.  `qDone` is an internal control tag of a machine started here from a
phase-local retag of an actual prior run, so it is neither halting of a composed machine nor
language acceptance, and `decClock` composes no earlier clock. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetRegisterDecrementSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (termWalk totalClock finishTape)
open Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation (registerBit)

def check_stateCount : Nat := stateCount
def check_states : List (Fin stateCount) :=
  [qStart, qSeekTerm, qSeekGap, qRegEnd, qBorrow, qDone, qReject]
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagExhausted {N B : Nat} :
    Config FixedGammaTargetPayloadRound.stateCount N B → Config stateCount N B :=
  retagExhausted
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  startConfig
def check_priorDeadline (N : Nat) : Nat := priorDeadline N
def check_decClock (N zeros d : Nat) : Nat := decClock N zeros d
def check_deadline (N : Nat) : Nat := deadline N
def check_borrow {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) : Nat :=
  borrow x w zeros
def check_decBit {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros d j : Nat) : Bool :=
  decBit x w zeros d j
def check_decTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros d : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := decTape B x w zeros d

/-- All 21 transition rows of the fixed table, restated literally and re-derived by `rfl`,
with the resource counts and the three distinguished states. -/
theorem check_table_rows :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qStart (some true) = (qReject, some true, .stay) ∧
    machine.step qSeekTerm none = (qSeekTerm, none, .right) ∧
    machine.step qSeekTerm (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qSeekTerm (some true) = (qSeekGap, some true, .right) ∧
    machine.step qSeekGap none = (qRegEnd, none, .right) ∧
    machine.step qSeekGap (some false) = (qSeekGap, some false, .right) ∧
    machine.step qSeekGap (some true) = (qSeekGap, some true, .right) ∧
    machine.step qRegEnd none = (qBorrow, none, .left) ∧
    machine.step qRegEnd (some false) = (qRegEnd, some false, .right) ∧
    machine.step qRegEnd (some true) = (qRegEnd, some true, .right) ∧
    machine.step qBorrow none = (qReject, none, .stay) ∧
    machine.step qBorrow (some false) = (qBorrow, some true, .left) ∧
    machine.step qBorrow (some true) = (qDone, some false, .stay) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 7 ∧ machine.start = qStart ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 21 := by
  repeat' apply And.intro
  all_goals rfl

def check_table_and_resource_pins := @table_and_resource_pins

theorem check_per_step_budget_independent :
    ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

/-- The phase-local handoff in full: `startConfig` is the G2p-d round machine retagged at the
length-only time `priorDeadline (a + m)`. -/
theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadRound.machine.run (priorDeadline (a + m))
      (FixedGammaTargetPayloadRound.startConfig B x w)
    let c := startConfig B x w
    c = retagExhausted p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_exact x w

/-- The clocks, the step decomposition, and the length-only deadline. -/
theorem check_clock_pins (N zeros d : Nat) :
    decClock N zeros d = N + zeros + d - 3 ∧ deadline N = 3 * N ∧
      priorDeadline N = 3 * (N * N) ∧
      (9 + zeros ≤ N → decClock N zeros d = (N - 7) + 1 + (zeros + 1) + 1 + d + 1) ∧
      (9 + zeros ≤ N → d ≤ zeros → decClock N zeros d ≤ deadline N) :=
  clock_pins N zeros d

/-- The one extra cell of room this phase needs, and that it implies G2p-f's. -/
theorem check_room_iff (a m B zeros : Nat) :
    (a + m + 2 + zeros < tapeLength (pairLength a m) B ↔ zeros + 1 ≤ a + B) ∧
      (a + m + 2 + zeros < tapeLength (pairLength a m) B →
        a + m + 1 + zeros < tapeLength (pairLength a m) B) :=
  room_iff a m B zeros

/-- The length-only handoff time covers the G2p-e rounds and the G2p-f finish. -/
theorem check_prior_covers {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    totalClock N zeros ≤ priorDeadline N :=
  prior_covers hN

/-- The borrow length, produced from the digits: `borrow x w zeros` low digits are `false`, the
digit above them is `true`, and it never exceeds `zeros`. -/
theorem check_borrow_pins {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    borrow x w zeros ≤ zeros ∧
      (∀ i, i < borrow x w zeros → registerBit x w zeros (zeros - i) = false) ∧
      registerBit x w zeros (zeros - borrow x w zeros) = true :=
  borrow_pins x w zeros

/-- Subtracting one flips the low run: pure arithmetic, no machine and no tape. -/
theorem check_sub_one_bits {v d : Nat} (h1 : ∀ i, i < d → v.testBit i = false)
    (h2 : v.testBit d = true) (j : Nat) :
    (v - 1).testBit j = if j < d then true else if j = d then false else v.testBit j :=
  sub_one_bits h1 h2 j

/-- The endpoint digits are the digits of `v - 1`, and `v - 1` has no digit above `zeros` either.
`v` is universally quantified: nothing here parses anything, and no wrapper supplies a parsed
target. -/
theorem check_decBit_sub_one {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros v : Nat)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = registerBit x w zeros j)
    (hhigh : ∀ i, zeros < i → v.testBit i = false) :
    (∀ j, j ≤ zeros → (v - 1).testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j) ∧
      (∀ i, zeros < i → (v - 1).testBit i = false) :=
  decBit_sub_one x w zeros v hv hhigh

/-- What the decrement writes and what it leaves alone, restated in full. -/
theorem check_decTape_pins {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hd : d ≤ zeros) :
    (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j →
        decTape B x w zeros d i = some (decBit x w zeros d j)) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B),
        i.val < a + m + 1 ∨ a + m + 1 + zeros < i.val →
        decTape B x w zeros d i = finishTape B x w zeros i) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 1 + zeros - d →
        decTape B x w zeros d i = some false) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 + zeros - d < i.val →
        i.val ≤ a + m + 1 + zeros → decTape B x w zeros d i = some true) ∧
      (∀ j : Nat, j < zeros - d → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j →
        decTape B x w zeros d i = some (registerBit x w zeros j)) :=
  decTape_pins x w htag hg hd

/-- The control schedule of the decrement, restated in full.  With
`check_decrement_generic` these conjuncts name the control at every time up to and including
the halt; the head conjuncts cover every time strictly before the halt, where the final
`.stay` step leaves the head on the stopping cell. -/
theorem check_decrement_schedule {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart) (hh : c.head.val = 7)
    (ht : c.tape = finishTape B x w zeros) :
    (∀ t, t ≤ a + m + zeros - 5 → (machine.run t c).head.val = 7 + t) ∧
      (∀ t, a + m + zeros - 4 ≤ t → t < decClock (a + m) zeros d →
        (machine.run t c).head.val = 2 * (a + m) + 2 * zeros - 3 - t) ∧
      (machine.run 0 c).state = qStart ∧
      (∀ t, 1 ≤ t → t ≤ zeros + termWalk (a + m) zeros + 1 →
        (machine.run t c).state = qSeekTerm) ∧
      (∀ t, zeros + termWalk (a + m) zeros + 2 ≤ t → t ≤ a + m - 7 →
        (machine.run t c).state = qSeekGap) ∧
      (∀ t, a + m - 6 ≤ t → t ≤ a + m + zeros - 5 →
        (machine.run t c).state = qRegEnd) ∧
      (∀ t, a + m + zeros - 4 ≤ t → t < decClock (a + m) zeros d →
        (machine.run t c).state = qBorrow) :=
  decrement_schedule x w htag hg hroom hd hlow hstop c hq hh ht

/-- The decrement out of an arbitrary G2p-f endpoint configuration, restated in full: exact
cost `decClock (a+m) zeros d`, endpoint `qDone` on the stopping cell, whole tape equal to
`decTape`. -/
theorem check_decrement_generic {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart) (hh : c.head.val = 7)
    (ht : c.tape = finishTape B x w zeros) :
    let e := machine.run (decClock (a + m) zeros d) c
    e.state = qDone ∧ e.head.val = a + m + 1 + zeros - d ∧
      e.tape = decTape B x w zeros d :=
  decrement_generic x w htag hg hroom hd hlow hstop c hq hh ht

/-- First arrival and the all-times clamp, restated in full.  Both directions are proved:
`qDone` is not entered before `decClock (a+m) zeros d`, and from that time on the
configuration is constant. -/
theorem check_decrement_strict {a m B zeros d : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ i, i < d → registerBit x w zeros (zeros - i) = false)
    (hstop : registerBit x w zeros (zeros - d) = true)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart) (hh : c.head.val = 7)
    (ht : c.tape = finishTape B x w zeros) :
    (∀ t, t < decClock (a + m) zeros d → (machine.run t c).state ≠ qDone) ∧
      (∀ t, decClock (a + m) zeros d ≤ t →
        machine.run t c = machine.run (decClock (a + m) zeros d) c) ∧
      (∀ t, decClock (a + m) zeros d ≤ t →
        (machine.run t c).state = qDone ∧
          (machine.run t c).head.val = a + m + 1 + zeros - d ∧
          (machine.run t c).tape = decTape B x w zeros d) :=
  decrement_strict x w htag hg hroom hd hlow hstop c hq hh ht

/-- The concrete exact run out of the phase-local `startConfig`, restated in full.  No
conjunct decodes the register into a number: `decBit` is content, and the arithmetic reading
is `check_decBit_sub_one`'s, on a `v` nothing here supplies. -/
theorem check_register_decremented {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) :
    let e := machine.run (decClock (a + m) zeros (borrow x w zeros)) (startConfig B x w)
    e.state = qDone ∧ e.head.val = a + m + 1 + zeros - borrow x w zeros ∧
      e.tape = decTape B x w zeros (borrow x w zeros) ∧
      (∀ j : Nat, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B),
        i.val = a + m + 1 + j →
        e.tape i = some (decBit x w zeros (borrow x w zeros) j)) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B),
        i.val < a + m + 1 ∨ a + m + 1 + zeros < i.val →
        e.tape i = finishTape B x w zeros i) ∧
      (∀ t, decClock (a + m) zeros (borrow x w zeros) ≤ t →
        machine.run t (startConfig B x w) = e) :=
  register_decremented x w htag hg hzeros hroom

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's execution theorems.  `check_*_handoff`
identifies the *actual* phase-local start configuration with an explicit configuration for every
budget, using only the landed G2p-f endpoint theorem and this module's clock bound `prior_covers`,
an arithmetic statement about clocks that executes nothing; the runs below are then reduced by
kernel computation on that configuration at `B = 0`.  Each probe is a claim about its own input.
The tag is `10110010` and both words decode to `zeros = 4`, so the register is five digits wide.
`physWord` has `N = 17` and a physically present payload; `virtWord` has `N = 15`, with the payload
truncated after two digits.  They exercise the two shapes of the borrow: `physWord`'s register ends
in a `true`, so `d = 0`, while `virtWord`'s ends in three `false` digits, so `d = 3`. -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def virtWord : Bitstring 7 := ![false, false, false, false, true, true, false]

/-- Rebuild a configuration from its three projections.  Stated over a configuration
*variable*, so that identifying the phase-local start configuration never has to reduce the
G2p-f run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) :
    c = ⟨q, ⟨k, hk⟩, T⟩ := by
  obtain ⟨cs, ch, ct⟩ := c
  cases hq; cases ht
  exact congrArg (fun h => (⟨cs, h, ct⟩ : Config K n B)) (Fin.ext hh)

theorem check_phys_handoff (B : Nat) :
    startConfig B tag physWord =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        finishTape B tag physWord 4⟩ := by
  obtain ⟨-, hh, ht, -, -, -, hclamp⟩ :=
    FixedGammaTargetPayloadExhaustion.payload_exhausted (B := B) (zeros := 4) tag physWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  have hstart : FixedGammaTargetPayloadRound.machine.run (priorDeadline (8 + 9))
      (FixedGammaTargetPayloadRound.startConfig B tag physWord)
      = FixedGammaTargetPayloadRound.machine.run (totalClock (8 + 9) 4)
        (FixedGammaTargetPayloadRound.startConfig B tag physWord) :=
    hclamp _ (prior_covers (by omega))
  refine config_of_parts rfl ?_ ?_
  · change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (8 + 9))
      (FixedGammaTargetPayloadRound.startConfig B tag physWord)).head.val = 7
    rw [hstart]; exact hh
  · change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (8 + 9))
      (FixedGammaTargetPayloadRound.startConfig B tag physWord)).tape = _
    rw [hstart]; exact ht

theorem check_virt_handoff (B : Nat) :
    startConfig B tag virtWord =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        finishTape B tag virtWord 4⟩ := by
  obtain ⟨-, hh, ht, -, -, -, hclamp⟩ :=
    FixedGammaTargetPayloadExhaustion.payload_exhausted (B := B) (zeros := 4) tag virtWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  have hstart : FixedGammaTargetPayloadRound.machine.run (priorDeadline (8 + 7))
      (FixedGammaTargetPayloadRound.startConfig B tag virtWord)
      = FixedGammaTargetPayloadRound.machine.run (totalClock (8 + 7) 4)
        (FixedGammaTargetPayloadRound.startConfig B tag virtWord) :=
    hclamp _ (prior_covers (by omega))
  refine config_of_parts rfl ?_ ?_
  · change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (8 + 7))
      (FixedGammaTargetPayloadRound.startConfig B tag virtWord)).head.val = 7
    rw [hstart]; exact hh
  · change (FixedGammaTargetPayloadRound.machine.run (priorDeadline (8 + 7))
      (FixedGammaTargetPayloadRound.startConfig B tag virtWord)).tape = _
    rw [hstart]; exact ht

/-- Both probe inputs really do satisfy the hypotheses the general theorems above assume:
each decodes to `zeros = 4` behind a matching tag, and at the probes' own budget `B = 0` each
allocates the blank past the register, which is this phase's room premise.  So none of the
theorems above is a statement about an unsatisfiable hypothesis set. -/
theorem check_probe_inputs_valid :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      8 + 9 + 2 + 4 < tapeLength (pairLength 8 9) 0 ∧
      FixedContentTagGate.tagMatches (Fin.append tag virtWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag virtWord) = some 4 ∧
      8 + 7 + 2 + 4 < tapeLength (pairLength 8 7) 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The literal borrow lengths and clocks the two probes execute, pinned by kernel
reduction.  The two costs differ by exactly the borrow: `physWord` stops on the first digit
it reads, `virtWord` walks over three. -/
theorem check_clock_values :
    borrow tag physWord 4 = 0 ∧ decClock 17 4 0 = 18 ∧ deadline 17 = 51 ∧
      totalClock 17 4 = 64 ∧ priorDeadline 17 = 867 ∧
      borrow tag virtWord 4 = 3 ∧ decClock 15 4 3 = 19 ∧ deadline 15 = 45 ∧
      totalClock 15 4 = 54 ∧ priorDeadline 15 = 675 :=
  ⟨by decide, rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl⟩

/-- `check_decBit_sub_one`'s hypotheses are satisfiable, so it is not a statement about an empty
premise set: `virtWord`'s five register digits are the bits of `24`, and the endpoint digits are
then the bits of `23`.  The `24` is supplied here by hand, as a literal chosen to match the digits;
no theorem of this slice or of pnp3 produces it from a parse, which is exactly the deferred pnp4
step. -/
theorem check_decBit_sub_one_instance :
    (∀ j, j ≤ 4 →
        (24 - 1 : Nat).testBit (4 - j) = decBit tag virtWord 4 (borrow tag virtWord 4) j) ∧
      ∀ i, 4 < i → (24 - 1 : Nat).testBit i = false :=
  decBit_sub_one tag virtWord 4 24 (fun j hj => by interval_cases j <;> decide)
    (fun i hi => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi; omega))

set_option maxRecDepth 1000000 in
/-- The physically present payload (`N = 17`, `zeros = 4`, `decClock 17 4 0 = 18`).  The first
scan stops on the walking terminator `16` at step nine — the first `some true` at or right of cell
`8`, the restored gamma zeros being `some false` and the consumed trail blank — and one step later
the head is on the boundary blank `17` in `qSeekGap`, a single step here because the terminator
stands at `N - 1`.  `qRegEnd` enters the register at `18` at step eleven and leaves it at the blank
`23` at step sixteen, and the step back puts `qBorrow` on the least significant digit `22` at step
seventeen.  That digit is `some true`, so the borrow stops at once: step eighteen is `qDone` on
`22`, with the register `[18,22] = true, true, false, false, false` where it was
`true, true, false, false, true` — as a bit pattern read from cell `18`, `11001` became `11000`,
which nothing here claims to be a decoded value.  Cells `7` and `16` sample the region outside the
register — the tag cell is still `some false` and the walking terminator still stands — while it is
`check_register_decremented` that pins the whole of it.  Steps nineteen and twenty-four show `qDone`
absorbing. -/
theorem check_phys_probe :
    (machine.run 9 (startConfig 0 tag physWord)).state = qSeekTerm ∧
    (machine.run 9 (startConfig 0 tag physWord)).head.val = 16 ∧
    (machine.run 10 (startConfig 0 tag physWord)).state = qSeekGap ∧
    (machine.run 10 (startConfig 0 tag physWord)).head.val = 17 ∧
    (machine.run 11 (startConfig 0 tag physWord)).state = qRegEnd ∧
    (machine.run 11 (startConfig 0 tag physWord)).head.val = 18 ∧
    (machine.run 16 (startConfig 0 tag physWord)).state = qRegEnd ∧
    (machine.run 16 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 17 (startConfig 0 tag physWord)).state = qBorrow ∧
    (machine.run 17 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 18 (startConfig 0 tag physWord)).state = qDone ∧
    (machine.run 18 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨21, by decide⟩ = some false ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag physWord)).state = qDone ∧
    (machine.run 24 (startConfig 0 tag physWord)).state = qDone ∧
    (machine.run 24 (startConfig 0 tag physWord)).head.val = 22 := by
  rw [check_phys_handoff 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 1000000 in
/-- The truncated payload (`N = 15`, `zeros = 4`, `decClock 15 4 3 = 19`).  Only two of the four
sources were physical, so the walking terminator stands at `14` and the first scan stops there at
step seven; the boundary blank is `15` at step eight and the register `[16,20]` is entered at step
nine and left at the blank `21` at step fourteen.  The borrow then runs: `qBorrow` on the least
significant digit `20` at step fifteen, on `19` at step sixteen and on `18` at step seventeen —
three `false` digits, two of them the virtual zeros of the truncated payload — and on `17` at step
eighteen, where the digit is `some true` and the borrow stops.  Step nineteen is `qDone` on `17`,
with the register `[16,20] = true, false, true, true, true` where it was
`true, true, false, false, false` — as a bit pattern read from cell `16`, `11000` became `10111`,
which nothing here claims to be a decoded value.  The borrow cleared the digit it stopped on and
set the three below it, and cell `14` pins that the walking terminator outside the register did
not move.  Steps twenty and twenty-five show `qDone` absorbing. -/
theorem check_virt_probe :
    (machine.run 7 (startConfig 0 tag virtWord)).state = qSeekTerm ∧
    (machine.run 7 (startConfig 0 tag virtWord)).head.val = 14 ∧
    (machine.run 8 (startConfig 0 tag virtWord)).state = qSeekGap ∧
    (machine.run 8 (startConfig 0 tag virtWord)).head.val = 15 ∧
    (machine.run 9 (startConfig 0 tag virtWord)).state = qRegEnd ∧
    (machine.run 9 (startConfig 0 tag virtWord)).head.val = 16 ∧
    (machine.run 14 (startConfig 0 tag virtWord)).state = qRegEnd ∧
    (machine.run 14 (startConfig 0 tag virtWord)).head.val = 21 ∧
    (machine.run 15 (startConfig 0 tag virtWord)).state = qBorrow ∧
    (machine.run 15 (startConfig 0 tag virtWord)).head.val = 20 ∧
    (machine.run 16 (startConfig 0 tag virtWord)).state = qBorrow ∧
    (machine.run 16 (startConfig 0 tag virtWord)).head.val = 19 ∧
    (machine.run 17 (startConfig 0 tag virtWord)).state = qBorrow ∧
    (machine.run 17 (startConfig 0 tag virtWord)).head.val = 18 ∧
    (machine.run 18 (startConfig 0 tag virtWord)).state = qBorrow ∧
    (machine.run 18 (startConfig 0 tag virtWord)).head.val = 17 ∧
    (machine.run 19 (startConfig 0 tag virtWord)).state = qDone ∧
    (machine.run 19 (startConfig 0 tag virtWord)).head.val = 17 ∧
    (machine.run 19 (startConfig 0 tag virtWord)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag virtWord)).tape ⟨17, by decide⟩ = some false ∧
    (machine.run 19 (startConfig 0 tag virtWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag virtWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag virtWord)).tape ⟨20, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag virtWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 20 (startConfig 0 tag virtWord)).state = qDone ∧
    (machine.run 25 (startConfig 0 tag virtWord)).state = qDone ∧
    (machine.run 25 (startConfig 0 tag virtWord)).head.val = 17 := by
  rw [check_virt_handoff 0]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetRegisterDecrementSurfaceTests
