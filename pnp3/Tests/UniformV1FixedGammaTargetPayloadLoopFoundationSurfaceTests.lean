import Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation

/-!
Surface pins for the Part A G2p-d loop foundation: the fixed 14-state/42-row
machine that installs the two tape-resident markers a self-stopping gamma payload
loop needs, its phase-local handoff from the *actual* G2p-c second-payload
endpoint, the marker/register tape vocabulary, and the halted endpoint with the
markers installed at the exact first terminal time `exactClock zeros = zeros + 7`.

`exactClock` is width-only and `deadline N = N` is this phase's length-only
deadline; neither counts the steps embedded in `startConfig`.  The two degenerate
widths are covered *only* by the literal probes at the end (width zero halting
after two steps, width one after five with its counter mark restored); their
quantified endpoint theorems do not exist yet, so no wrapper here pins one.  Also
not here and not available to pin: the round, its iteration, the exhaustion
finish, the complete target register, the all-times clamp/footprint/budget
package, any parsed header value or `contentHeader?` fact, and any pnp4 bridge.
`qDone` is an internal endpoint, never language acceptance, and no wrapper states
a converse of any endpoint.
-/

namespace Pnp3.Tests.UniformV1FixedGammaTargetPayloadLoopFoundationSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation

def check_stateCount : Nat := stateCount
def check_states : List (Fin stateCount) :=
  [qStart, qZeroA, qZeroB, qSeek, qSrcA, qClearA, qBackA, qOnTerm, qSrcB, qClearB,
    qBackB, qFin, qDone, qReject]
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagSecondPayload {N B : Nat} :
    Config FixedGammaTargetSecondPayload.stateCount N B → Config stateCount N B :=
  retagSecondPayload
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  startConfig
def check_exactClock (zeros : Nat) : Nat := exactClock zeros
def check_malformedExactClock : Nat := malformedExactClock
def check_deadline (N : Nat) : Nat := deadline N
def check_walk (N zeros r : Nat) : Nat := walk N zeros r
def check_registerBit {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros i : Nat) : Bool :=
  registerBit x w zeros i
def check_loopTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros r : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool :=
  loopTape B x w zeros r

/-- Every clock and the deadline, re-derived here by `rfl` instead of through the
module's own pin.  The deadline is a closed form in `N = a + m` alone — no width,
target, round index, proof, advice, or producer mark occurs in it. -/
theorem check_clock_values (N zeros r : Nat) :
    exactClock zeros = zeros + 7 ∧ malformedExactClock = 1 ∧
      walk N zeros r = min r (N - 9 - zeros) ∧ deadline N = N :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Name-and-type pin of the table theorem: its 42-row-plus-resource conjunction is
written out literally in the module, and this wrapper aliases it.  The rows
themselves are restated literally in `check_table_rows` below. -/
def check_table_and_resource_pins := @table_and_resource_pins

/-- All 42 transition rows of the fixed table, restated literally here and
re-derived by `rfl` rather than the module's own pin, with the resource counts. -/
theorem check_table_rows :
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

theorem check_per_step_budget_independent :
    ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetSecondPayload.machine.run
      (FixedGammaTargetSecondPayload.deadline (a + m))
      (FixedGammaTargetSecondPayload.startConfig B x w)
    let c := startConfig B x w
    c = retagSecondPayload p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  handoff_exact x w

theorem check_clock_pins (N zeros r : Nat) :
    exactClock zeros = zeros + 7 ∧ malformedExactClock = 1 ∧
      walk N zeros r = min r (N - 9 - zeros) ∧ deadline N = N :=
  clock_pins N zeros r

theorem check_room_iff (a m B : Nat) :
    a + m + 3 < tapeLength (pairLength a m) B ↔ 2 ≤ a + B :=
  room_iff a m B

theorem check_exactClock_le_deadline {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    exactClock zeros ≤ deadline N :=
  exactClock_le_deadline hN

theorem check_registerBit_pins {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) :
    registerBit x w zeros 0 = true ∧
      registerBit x w zeros 1 =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false ∧
      registerBit x w zeros 2 =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros)).getD false ∧
      ∀ i, registerBit x w zeros (i + 1) =
        (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + i)).getD false :=
  registerBit_pins x w zeros

theorem check_loopTape_layout {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
      loopTape B x w zeros 2 i = FixedPairContentMarkerErase.contentTape B x w i) :=
  loopTape_layout x w hz hN hroom

theorem check_markers_installed {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 8 + zeros + walk (a + m) zeros 2 ∧
      d.tape = loopTape B x w zeros 2 :=
  markers_installed x w htag hg hzeros hroom s hs

theorem check_markers_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s < exactClock zeros) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  markers_strict x w htag hg hzeros hroom s hs

theorem check_markers_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 8 + zeros + walk (a + m) zeros 2 ∧
      d.tape = loopTape B x w zeros 2 :=
  markers_at_deadline x w htag hg hzeros hroom

theorem check_malformed_rejects {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : malformedExactClock ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_rejects x w htag hg s hs

/-! ### Concrete words used by the probes below -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def malformed : Bitstring 3 := ![false, false, false]
private def widthZero : Bitstring 1 := ![true]
private def widthOne : Bitstring 3 := ![false, true, true]
private def twoBoth : Bitstring 6 := ![false, false, true, false, true, true]
private def twoTight : Bitstring 3 := ![false, false, true]

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's execution theorems.
`check_*_handoff` first identifies the *actual* phase-local start configuration
with an explicit configuration for every budget, using only the landed G2p-c
endpoint theorem and the definitional `retagSecondPayload` handoff; then, at the
concrete budget `B = 0`, this module's own `machine.run` is reduced by kernel
computation on that configuration.  What they check is the address choreography —
the two counter marks at cells `8` and `9`, the width dispatch that reads those
cells, the mark restoration on width one, the blanked terminator trail, and the
walking terminator's final cell.  For width zero and width one they are the only
coverage this module has, and every probe is a claim about its own input, not
about every word of that width.

The tag is `10110010`.  `widthZero` decodes to `zeros = 0` (terminator at cell
`8`, `N = 9`); `widthOne` to `zeros = 1` (terminator at `9`, `N = 11`, payload
digit `true` at `10`); `malformed` has no gamma terminator below the boundary
(`N = 11`).  Both width-two words have their terminator at `10` and consumed payload
cells `11` and `12`: `twoBoth` has `N = 14` (both physical, digits `false` and `true`)
and `twoTight` has `N = 11` (neither physical, so the second *and* third register
digits are both the virtual `false`).  The middle shape — the first source physical,
the second the boundary blank — is covered by `markers_installed` but by no probe here. -/

/-- Rebuild a configuration from its three projections.  Stated over a
configuration *variable*, so that identifying the phase-local start configuration
never has to reduce the G2p-c run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) :
    c = ⟨q, ⟨k, hk⟩, T⟩ := by
  obtain ⟨cs, ch, ct⟩ := c
  cases hq
  cases ht
  exact congrArg (fun h => (⟨cs, h, ct⟩ : Config K n B)) (Fin.ext hh)

theorem check_malformed_handoff (B : Nat) :
    startConfig B tag malformed =
      ⟨qStart, ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag malformed⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.malformed_at_deadline
    (B := B) tag malformed (by decide) (by decide)
  config_of_parts rfl hh ht

theorem check_zero_handoff (B : Nat) :
    startConfig B tag widthZero =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag widthZero⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.zero_width_at_deadline
    (B := B) tag widthZero (by decide) (by decide)
  config_of_parts rfl hh ht

theorem check_one_handoff (B : Nat) :
    startConfig B tag widthOne =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag widthOne
          ((FixedContentTagGate.physicalSymbol (Fin.append tag widthOne) 10).getD false)⟩ :=
  let ⟨_, hh, ht, _⟩ := FixedGammaTargetSecondPayload.width_one_at_deadline
    (B := B) tag widthOne (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

theorem check_both_physical_handoff (B : Nat) :
    startConfig B tag twoBoth =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetSecondPayload.secondPayloadTape B tag twoBoth
          ((FixedContentTagGate.physicalSymbol (Fin.append tag twoBoth) (9 + 2)).getD false)
          ((FixedContentTagGate.physicalSymbol (Fin.append tag twoBoth)
            (10 + 2)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.second_payload_at_deadline
    (B := B) (zeros := 2) tag twoBoth (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

theorem check_tight_handoff (B : Nat) :
    startConfig B tag twoTight =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetSecondPayload.secondPayloadTape B tag twoTight
          ((FixedContentTagGate.physicalSymbol (Fin.append tag twoTight) (9 + 2)).getD false)
          ((FixedContentTagGate.physicalSymbol (Fin.append tag twoTight)
            (10 + 2)).getD false)⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetSecondPayload.second_payload_at_deadline
    (B := B) (zeros := 2) tag twoTight (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

set_option maxRecDepth 8192 in
/-- Malformed: the handed-over configuration is in neither terminal state, one step
rejects in place at the boundary head `N = 11`, and the rejection is absorbing. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ qDone ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ qReject ∧
    (machine.run 1 (startConfig 0 tag malformed)).state = qReject ∧
    (machine.run 1 (startConfig 0 tag malformed)).head.val = 11 ∧
    (machine.run 1 (startConfig 0 tag malformed)).tape ⟨11, by decide⟩ = none ∧
    (machine.run 5 (startConfig 0 tag malformed)).state = qReject := by
  rw [check_malformed_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 8192 in
/-- Width zero: the machine steps onto cell `8`, finds the terminator there, and
halts at head `7` at step two with cells `7` and `8` as handed over. -/
theorem check_zero_probe :
    (machine.run 1 (startConfig 0 tag widthZero)).head.val = 8 ∧
    (machine.run 1 (startConfig 0 tag widthZero)).state ≠ qDone ∧
    (machine.run 2 (startConfig 0 tag widthZero)).state = qDone ∧
    (machine.run 2 (startConfig 0 tag widthZero)).head.val = 7 ∧
    (machine.run 2 (startConfig 0 tag widthZero)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 2 (startConfig 0 tag widthZero)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 6 (startConfig 0 tag widthZero)).state = qDone := by
  rw [check_zero_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 8192 in
/-- Width one: cell `8` is marked at step two, the terminator at cell `9` sends the
run back, the mark is restored at step four, and the machine halts at head `7` at
step five with cells `7`, `8`, `9`, `10` as handed over. -/
theorem check_one_probe :
    (machine.run 2 (startConfig 0 tag widthOne)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 2 (startConfig 0 tag widthOne)).head.val = 9 ∧
    (machine.run 3 (startConfig 0 tag widthOne)).state = qFin ∧
    (machine.run 4 (startConfig 0 tag widthOne)).tape ⟨8, by decide⟩ = some false ∧
    (machine.run 4 (startConfig 0 tag widthOne)).state ≠ qDone ∧
    (machine.run 5 (startConfig 0 tag widthOne)).state = qDone ∧
    (machine.run 5 (startConfig 0 tag widthOne)).head.val = 7 ∧
    (machine.run 5 (startConfig 0 tag widthOne)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 5 (startConfig 0 tag widthOne)).tape ⟨8, by decide⟩ = some false ∧
    (machine.run 5 (startConfig 0 tag widthOne)).tape ⟨9, by decide⟩ = some true ∧
    (machine.run 5 (startConfig 0 tag widthOne)).tape ⟨10, by decide⟩ = some true := by
  rw [check_one_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 8192 in
/-- Both consumed sources physical (`N = 14`): the counter marks appear at steps
two and three, the new terminator is written at `11` at step five and at `12` at
step eight, the vacated cells `10` and `11` are blanked at steps six and nine, and
step nine halts at head `12` with the three inherited register cells untouched.
Step eight is not yet terminal. -/
theorem check_both_physical_probe :
    (machine.run 2 (startConfig 0 tag twoBoth)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 3 (startConfig 0 tag twoBoth)).tape ⟨9, by decide⟩ = some true ∧
    (machine.run 5 (startConfig 0 tag twoBoth)).tape ⟨11, by decide⟩ = some true ∧
    (machine.run 6 (startConfig 0 tag twoBoth)).tape ⟨10, by decide⟩ = none ∧
    (machine.run 8 (startConfig 0 tag twoBoth)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 8 (startConfig 0 tag twoBoth)).state ≠ qDone ∧
    (machine.run 8 (startConfig 0 tag twoBoth)).state ≠ qReject ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).state = qDone ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).head.val = 12 ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).tape ⟨10, by decide⟩ = none ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).tape ⟨11, by decide⟩ = none ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).tape ⟨15, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).tape ⟨16, by decide⟩ = some false ∧
    (machine.run 9 (startConfig 0 tag twoBoth)).tape ⟨17, by decide⟩ = some true := by
  rw [check_both_physical_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 8192 in
/-- Neither consumed source physical (`N = 11`): the terminator stays at `10`,
neither consumed source cell is overwritten and nothing is blanked, and step nine
halts at head `10` with the second and the third register digits both the virtual `false`. -/
theorem check_tight_probe :
    (machine.run 9 (startConfig 0 tag twoTight)).state = qDone ∧
    (machine.run 9 (startConfig 0 tag twoTight)).head.val = 10 ∧
    (machine.run 9 (startConfig 0 tag twoTight)).tape ⟨8, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag twoTight)).tape ⟨9, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag twoTight)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag twoTight)).tape ⟨11, by decide⟩ = none ∧
    (machine.run 9 (startConfig 0 tag twoTight)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag twoTight)).tape ⟨13, by decide⟩ = some false ∧
    (machine.run 9 (startConfig 0 tag twoTight)).tape ⟨14, by decide⟩ = some false := by
  rw [check_tight_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

end Pnp3.Tests.UniformV1FixedGammaTargetPayloadLoopFoundationSurfaceTests
