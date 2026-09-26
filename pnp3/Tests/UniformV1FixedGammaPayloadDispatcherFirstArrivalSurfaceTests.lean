import Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival

/-!
Surface pins for the Part A G3f slice: the strict first arrival of the gamma-payload
dispatcher's **three** absorbing endpoints — `qAllZero` (its `accept`), `qHasOne` and
`qReject` (its `reject`) — on the actual `startConfig` and at the actual path clock.  Every
public declaration of the slice is restated; `check_strictFirstTerminalAt_expand` unfolds the
predicate, so the strictness conjunct is visible as three inequalities at every earlier step.

The probes.  The tag is `10110010`, as in the G3e fixtures.  `malformedWord` has no gamma
terminator below `N = 11`; `zeroWord` decodes to `zeros = 0` with `N = 10`; `middleWord` to
`zeros = 2` with `N = 12` and a physical `true` at the first payload cell `11`; `physWord` to
`zeros = 4` with `N = 17` and a physical `true` at `13`; `tightWord` to `zeros = 2` with
`N = 11`, where the first payload cell `11` is virtual; `oneWord` to `zeros = 1` with
`N = 11`, whose one payload cell `10` is `false`, so its payload is exhausted;
`pendTrueWord` to `zeros = 2` with `N = 13`, `false` at `11` and `true` at `12`; and
`pendVirtWord` to `zeros = 2` with `N = 12`, `false` at `11` and a virtual cell `12`.  The eight
fixtures therefore exercise all seven of the slice's outcome theorems — `first_true` twice, at
`N = 17` and `N = 12` — and both the `k = 0` and the `k = 1` payload reads.

`check_probe_instances` inhabits the hypotheses at those literals and `check_probe_clocks`
reduces the literal path clocks.  `check_*_probe` **derives** the first arrival at each
literal from the slice's theorem, while `check_probe_reductions` is **independent** of those
theorems: it identifies the actual `startConfig 0 tag ·` with G2a's landed `finalConfig` using
`probe_start` and the proved `run_deadline` equality, which execute nothing there, and then reduces
the dispatcher by kernel computation, reading back the working state one step before each clock
and the endpoint index and head at it. So the clocks are cross-checked against the table, not
only against the proofs.

Not here: `qHasOne` remains a second non-reject absorbing endpoint, so no `UniformTM.seq`
routing, no H11 composite and no composed clock; and no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP`, language-membership or `ContentVerifierBridge` statement. -/

namespace Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherFirstArrivalSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadDispatcher
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherRounds
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival

def check_IsTerminal : Fin stateCount → Prop := IsTerminal

def check_StrictFirstTerminalAt :
    {a m : Nat} → (B : Nat) → Bitstring a → Bitstring m → Nat → Fin stateCount → Prop :=
  StrictFirstTerminalAt

theorem check_isTerminal_iff (q : Fin stateCount) :
    IsTerminal q ↔ (q = qAllZero ∨ q = qHasOne ∨ q = qReject) := isTerminal_iff q

theorem check_isTerminal_iff_absorbing (q : Fin stateCount) :
    IsTerminal q ↔ ∀ s, machine.step q s = (q, s, .stay) := isTerminal_iff_absorbing q

theorem check_terminals_distinct :
    qAllZero ≠ qHasOne ∧ qAllZero ≠ qReject ∧ qHasOne ≠ qReject ∧
      machine.accept = qAllZero ∧ machine.reject = qReject ∧ ¬ IsTerminal qCursorStart ∧
      ¬ IsTerminal qCursorRead := terminals_distinct

theorem check_strictFirstTerminalAt_expand {a m : Nat} (B : Nat) (x : Bitstring a)
    (w : Bitstring m) (C : Nat) (q : Fin stateCount) :
    StrictFirstTerminalAt B x w C q ↔
      (machine.run C (startConfig B x w)).state = q ∧
      (q = qAllZero ∨ q = qHasOne ∨ q = qReject) ∧
      ∀ s, s < C →
        (machine.run s (startConfig B x w)).state ≠ qAllZero ∧
        (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
        (machine.run s (startConfig B x w)).state ≠ qReject :=
  strictFirstTerminalAt_expand B x w C q

theorem check_run_frozen_of_terminal {N B : Nat} (c : Config stateCount N B) {s C : Nat}
    (hs : s ≤ C) (h : IsTerminal (machine.run s c).state) :
    machine.run C c = machine.run s c := run_frozen_of_terminal c hs h

theorem check_no_terminal_of_le {N B t : Nat} (c : Config stateCount N B)
    (h : ¬ IsTerminal (machine.run t c).state) :
    ∀ s, s ≤ t → ¬ IsTerminal (machine.run s c).state := no_terminal_of_le c h

theorem check_start_not_terminal {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    ¬ IsTerminal (machine.run 0 (startConfig B x w)).state := start_not_terminal x w

theorem check_run_deadline_eq_of_strictFirstTerminalAt {a m B C : Nat} {q : Fin stateCount}
    (x : Bitstring a) (w : Bitstring m) (h : StrictFirstTerminalAt B x w C q)
    (hle : C ≤ deadline (a + m)) :
    machine.run (deadline (a + m)) (startConfig B x w) =
      machine.run C (startConfig B x w) :=
  run_deadline_eq_of_strictFirstTerminalAt x w h hle

theorem check_malformed_strict_first_terminal {a m B : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    StrictFirstTerminalAt B x w 1 qReject ∧
      (machine.run 1 (startConfig B x w)).head.val = a + m ∧
      (machine.run 1 (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w :=
  malformed_strict_first_terminal x w htag hg

theorem check_zero_width_strict_first_terminal {a m B : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    StrictFirstTerminalAt B x w 2 qAllZero ∧
      (machine.run 2 (startConfig B x w)).head.val = 7 ∧
      (machine.run 2 (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w :=
  zero_width_strict_first_terminal x w htag hg

theorem check_first_true_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (htrue : (Fin.append x w) ⟨9 + zeros, hp⟩ = true) :
    StrictFirstTerminalAt B x w (3 * zeros + 6) qHasOne ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).head.val = 6 ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w :=
  first_true_strict_first_terminal x w htag hg hzero hp htrue

theorem check_first_virtual_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hvirtual : 9 + zeros = a + m) :
    StrictFirstTerminalAt B x w (3 * zeros + 6) qAllZero ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).head.val = 6 ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w :=
  first_virtual_strict_first_terminal x w htag hg hzero hvirtual

theorem check_pending_true_strict_first_terminal {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    StrictFirstTerminalAt B x w (pendingEndClock zeros k) qHasOne ∧
      (machine.run (pendingEndClock zeros k) (startConfig B x w)).head.val = 6 ∧
      (machine.run (pendingEndClock zeros k) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w :=
  pending_true_strict_first_terminal x w htag hg hk hkz hprefix htrue

theorem check_pending_virtual_strict_first_terminal {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    StrictFirstTerminalAt B x w (pendingEndClock zeros k) qAllZero ∧
      (machine.run (pendingEndClock zeros k) (startConfig B x w)).head.val = 6 ∧
      (machine.run (pendingEndClock zeros k) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w :=
  pending_virtual_strict_first_terminal x w htag hg hk hkz hprefix hvirtual

theorem check_exhausted_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    StrictFirstTerminalAt B x w (zeroEndClock zeros) qAllZero ∧
      (machine.run (zeroEndClock zeros) (startConfig B x w)).head.val = 6 ∧
      (machine.run (zeroEndClock zeros) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w :=
  exhausted_strict_first_terminal x w htag hg hzero hprefix

theorem check_tagged_strict_first_terminal {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    ∃ C q, C ≤ deadline (a + m) ∧ StrictFirstTerminalAt B x w C q ∧
      machine.run (deadline (a + m)) (startConfig B x w) =
        machine.run C (startConfig B x w) :=
  tagged_strict_first_terminal x w htag

/-! ### The eight probe words -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def middleWord : Bitstring 4 := ![false, false, true, true]
private def tightWord : Bitstring 3 := ![false, false, true]
private def oneWord : Bitstring 3 := ![false, true, false]
private def zeroWord : Bitstring 2 := ![true, false]
private def malformedWord : Bitstring 3 := ![false, false, false]
private def pendTrueWord : Bitstring 5 := ![false, false, true, false, true]
private def pendVirtWord : Bitstring 4 := ![false, false, true, false]

/-- The tag matches in all eight fixtures; in the order below the seven well-formed words
decode to `zeros = 0`, `1`, `2`, `4`, `2`, `2` and `2`, and the first to no gamma at all. -/
theorem check_probe_instances :
    (FixedContentTagGate.tagMatches (Fin.append tag malformedWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag malformedWord) = none) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag zeroWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag zeroWord) = some 0) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag oneWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag oneWord) = some 1 ∧
      FixedContentTagGate.physicalSymbol (Fin.append tag oneWord) 10 = some false) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag middleWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag middleWord) = some 2 ∧
      (Fin.append tag middleWord) ⟨11, by decide⟩ = true) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      (Fin.append tag physWord) ⟨13, by decide⟩ = true) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag tightWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag tightWord) = some 2 ∧
      9 + 2 = 8 + 3) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag pendTrueWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag pendTrueWord) = some 2 ∧
      FixedContentTagGate.physicalSymbol (Fin.append tag pendTrueWord) 11 = some false ∧
      FixedContentTagGate.physicalSymbol (Fin.append tag pendTrueWord) 12 = some true) ∧
    (FixedContentTagGate.tagMatches (Fin.append tag pendVirtWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag pendVirtWord) = some 2 ∧
      FixedContentTagGate.physicalSymbol (Fin.append tag pendVirtWord) 11 = some false ∧
      9 + 2 + 1 = 8 + 4) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- The literal path clocks the probes use. -/
theorem check_probe_clocks :
    3 * 2 + 6 = 12 ∧ 3 * 4 + 6 = 18 ∧ zeroEndClock 1 = 16 ∧ pendingEndClock 2 1 = 23 ∧
      zeroEndClock 1 ≤ deadline 11 ∧ pendingEndClock 2 1 ≤ deadline 13 :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

/-! ### Derived first arrivals at the literal words -/

/-- Malformed: the shared reject at step `1`, first arrival of any endpoint. -/
theorem check_malformed_probe :
    (machine.run 1 (startConfig 0 tag malformedWord)).state = qReject ∧
      (∀ s, s < 1 →
        (machine.run s (startConfig 0 tag malformedWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag malformedWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag malformedWord)).state ≠ qReject) ∧
      (machine.run 1 (startConfig 0 tag malformedWord)).head.val = 8 + 3 :=
  let h := (strictFirstTerminalAt_expand 0 tag malformedWord 1 qReject).mp
    (malformed_strict_first_terminal tag malformedWord (by decide) (by decide)).1
  ⟨h.1, h.2.2,
    (malformed_strict_first_terminal tag malformedWord (by decide) (by decide)).2.1⟩

/-- Width zero: `qAllZero` at step `2` on head `7`, first arrival of any endpoint. -/
theorem check_zero_width_probe :
    (machine.run 2 (startConfig 0 tag zeroWord)).state = qAllZero ∧
      (∀ s, s < 2 →
        (machine.run s (startConfig 0 tag zeroWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag zeroWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag zeroWord)).state ≠ qReject) ∧
      (machine.run 2 (startConfig 0 tag zeroWord)).head.val = 7 :=
  let h := (strictFirstTerminalAt_expand 0 tag zeroWord 2 qAllZero).mp
    (zero_width_strict_first_terminal tag zeroWord (by decide) (by decide)).1
  ⟨h.1, h.2.2, (zero_width_strict_first_terminal tag zeroWord (by decide) (by decide)).2.1⟩

/-- A physical `true` at the first payload cell of a `zeros = 4` word: `qHasOne` at
step `18`, first arrival of any endpoint. -/
theorem check_first_true_probe :
    (machine.run 18 (startConfig 0 tag physWord)).state = qHasOne ∧
      ∀ s, s < 18 →
        (machine.run s (startConfig 0 tag physWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag physWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag physWord)).state ≠ qReject :=
  let h := (strictFirstTerminalAt_expand 0 tag physWord (3 * 4 + 6) qHasOne).mp
    (first_true_strict_first_terminal (zeros := 4) tag physWord (by decide) (by decide)
      (by omega) (by decide) (by decide)).1
  ⟨h.1, h.2.2⟩

/-- A virtual first payload cell on a `zeros = 2` word: `qAllZero` at step `12`,
first arrival of any endpoint — a different endpoint at the same clock as
`check_middle_true_probe`. -/
theorem check_first_virtual_probe :
    (machine.run 12 (startConfig 0 tag tightWord)).state = qAllZero ∧
      ∀ s, s < 12 →
        (machine.run s (startConfig 0 tag tightWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag tightWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag tightWord)).state ≠ qReject :=
  let h := (strictFirstTerminalAt_expand 0 tag tightWord (3 * 2 + 6) qAllZero).mp
    (first_virtual_strict_first_terminal (zeros := 2) tag tightWord (by decide) (by decide)
      (by omega) (by omega)).1
  ⟨h.1, h.2.2⟩

/-- The same clock `12` on a `zeros = 2` word whose first payload cell is physically
`true`, where the endpoint is `qHasOne` instead. -/
theorem check_middle_true_probe :
    (machine.run 12 (startConfig 0 tag middleWord)).state = qHasOne ∧
      ∀ s, s < 12 →
        (machine.run s (startConfig 0 tag middleWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag middleWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag middleWord)).state ≠ qReject :=
  let h := (strictFirstTerminalAt_expand 0 tag middleWord (3 * 2 + 6) qHasOne).mp
    (first_true_strict_first_terminal (zeros := 2) tag middleWord (by decide) (by decide)
      (by omega) (by decide) (by decide)).1
  ⟨h.1, h.2.2⟩

/-- An exhausted all-`false` payload of width one: `qAllZero` at
`zeroEndClock 1 = 16`, first arrival of any endpoint. -/
theorem check_exhausted_probe :
    (machine.run 16 (startConfig 0 tag oneWord)).state = qAllZero ∧
      ∀ s, s < 16 →
        (machine.run s (startConfig 0 tag oneWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag oneWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag oneWord)).state ≠ qReject :=
  let h := (strictFirstTerminalAt_expand 0 tag oneWord (zeroEndClock 1) qAllZero).mp
    (exhausted_strict_first_terminal (zeros := 1) tag oneWord (by decide) (by decide)
      (by omega) (by
        intro j hj0 hj1
        obtain rfl : j = 10 := by omega
        decide)).1
  ⟨h.1, h.2.2⟩

/-- A `true` payload cell at the positive index `k = 1`: `qHasOne` at
`pendingEndClock 2 1 = 23`, first arrival of any endpoint. -/
theorem check_pending_true_probe :
    (machine.run 23 (startConfig 0 tag pendTrueWord)).state = qHasOne ∧
      ∀ s, s < 23 →
        (machine.run s (startConfig 0 tag pendTrueWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag pendTrueWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag pendTrueWord)).state ≠ qReject :=
  let h := (strictFirstTerminalAt_expand 0 tag pendTrueWord (pendingEndClock 2 1) qHasOne).mp
    (pending_true_strict_first_terminal (zeros := 2) (k := 1) tag pendTrueWord (by decide)
      (by decide) (by omega) (by omega)
      (by
        intro j hj0 hj1
        obtain rfl : j = 11 := by omega
        decide) (by decide)).1
  ⟨h.1, h.2.2⟩

/-- A virtual payload cell at the positive index `k = 1`: `qAllZero` at the same
`pendingEndClock 2 1 = 23`. -/
theorem check_pending_virtual_probe :
    (machine.run 23 (startConfig 0 tag pendVirtWord)).state = qAllZero ∧
      ∀ s, s < 23 →
        (machine.run s (startConfig 0 tag pendVirtWord)).state ≠ qAllZero ∧
        (machine.run s (startConfig 0 tag pendVirtWord)).state ≠ qHasOne ∧
        (machine.run s (startConfig 0 tag pendVirtWord)).state ≠ qReject :=
  let h :=
    (strictFirstTerminalAt_expand 0 tag pendVirtWord (pendingEndClock 2 1) qAllZero).mp
      (pending_virtual_strict_first_terminal (zeros := 2) (k := 1) tag pendVirtWord
        (by decide) (by decide) (by omega) (by omega)
        (by
          intro j hj0 hj1
          obtain rfl : j = 11 := by omega
          decide) (by omega)).1
  ⟨h.1, h.2.2⟩

/-! ### Independent kernel reductions of the same clocks -/

/-- The actual dispatcher `startConfig B tag ·` is G2a's landed `finalConfig`, retagged.
The proved `run_deadline` equality identifies the anchor endpoint; it executes nothing here. -/
private theorem probe_start {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    startConfig B x w = retagG2a (FixedContentGammaAnchor.finalConfig B x w) :=
  congrArg retagG2a (FixedContentGammaAnchor.run_deadline x w htag)

set_option maxRecDepth 100000 in
/-- **The eight probe clocks, reduced**, at seven distinct pre-clock working states.  One
step before each clock the dispatcher is in a working state — `qCursorStart` (`0`) for the
malformed word, `qCursorBackFirst` (`1`) at width zero, `qCursorFillOne` (`8`) for both
`k = 0` physical-true words and `qCursorFillVirtual` (`9`) for the `k = 0` virtual one,
`qZeroFillCounter` (`19`) for the exhausted payload, and `qPendingFillOne` (`23`) and
`qPendingFillVirtual` (`24`) for the two `k = 1` reads — and at the clock it is in
`qReject` (`27`), `qAllZero` (`25`) or `qHasOne` (`26`) on the stated head.  Nothing here
uses the slice's theorems. -/
theorem check_probe_reductions :
    ((machine.run 0 (startConfig 0 tag malformedWord)).state.val = 0 ∧
      (machine.run 1 (startConfig 0 tag malformedWord)).state.val = 27 ∧
      (machine.run 1 (startConfig 0 tag malformedWord)).head.val = 11) ∧
    ((machine.run 1 (startConfig 0 tag zeroWord)).state.val = 1 ∧
      (machine.run 2 (startConfig 0 tag zeroWord)).state.val = 25 ∧
      (machine.run 2 (startConfig 0 tag zeroWord)).head.val = 7) ∧
    ((machine.run 17 (startConfig 0 tag physWord)).state.val = 8 ∧
      (machine.run 18 (startConfig 0 tag physWord)).state.val = 26 ∧
      (machine.run 18 (startConfig 0 tag physWord)).head.val = 6) ∧
    ((machine.run 11 (startConfig 0 tag middleWord)).state.val = 8 ∧
      (machine.run 12 (startConfig 0 tag middleWord)).state.val = 26 ∧
      (machine.run 12 (startConfig 0 tag middleWord)).head.val = 6) ∧
    ((machine.run 11 (startConfig 0 tag tightWord)).state.val = 9 ∧
      (machine.run 12 (startConfig 0 tag tightWord)).state.val = 25 ∧
      (machine.run 12 (startConfig 0 tag tightWord)).head.val = 6) ∧
    ((machine.run 15 (startConfig 0 tag oneWord)).state.val = 19 ∧
      (machine.run 16 (startConfig 0 tag oneWord)).state.val = 25 ∧
      (machine.run 16 (startConfig 0 tag oneWord)).head.val = 6) ∧
    ((machine.run 22 (startConfig 0 tag pendTrueWord)).state.val = 23 ∧
      (machine.run 23 (startConfig 0 tag pendTrueWord)).state.val = 26 ∧
      (machine.run 23 (startConfig 0 tag pendTrueWord)).head.val = 6) ∧
    ((machine.run 22 (startConfig 0 tag pendVirtWord)).state.val = 24 ∧
      (machine.run 23 (startConfig 0 tag pendVirtWord)).state.val = 25 ∧
      (machine.run 23 (startConfig 0 tag pendVirtWord)).head.val = 6) := by
  rw [probe_start 0 tag malformedWord (by decide), probe_start 0 tag zeroWord (by decide),
    probe_start 0 tag physWord (by decide), probe_start 0 tag middleWord (by decide),
    probe_start 0 tag tightWord (by decide), probe_start 0 tag oneWord (by decide),
    probe_start 0 tag pendTrueWord (by decide), probe_start 0 tag pendVirtWord (by decide)]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherFirstArrivalSurfaceTests
