import Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline

/-!
# Strict first terminal arrival for the gamma-payload dispatcher (Part A G3f)

G2k/G2l/G2m give the dispatcher an exact clock on every activated path and a
length-only deadline classification, but no common strict first-arrival surface
covering every path.  The remaining proof work differs by family.
For the malformed, the width-zero and the two `k = 0` paths it is total:
`malformed_exact`, `zero_width_exact`, `first_true_exact` and
`first_virtual_exact` are plain run equations carrying no exclusion at all, so
the four theorems below are new content.  For the two pending paths and the
exhausted one the `TrueExecution`/`VirtualExecution`/`ZeroExecution` bundles
already carry all three exclusions — their own endpoint strictly before the
clock, the other two at every time — so there the work is a repackaging into the
single form a later composition consumes.

This module closes exactly that gap, for the three absorbing endpoints
`qAllZero`, `qHasOne` and `qReject` together.  Every path theorem is about the
actual `FixedGammaPayloadDispatcher.startConfig` — the retagged G2a deadline run
— and the actual path-dependent clock; nothing here is generic in a machine, in
a source, or in a contract structure, and nothing routes or composes the
dispatcher with a later phase.  The absorption helpers also apply to arbitrary
configurations of this same fixed dispatcher.

The argument is small because the endpoints absorb.  A terminal entered at `s`
is still there at every `t ≥ s`, so (i) any terminal-free checkpoint at `t`
clears every `s ≤ t`, and (ii) if a terminal did appear before the path clock,
the whole configuration — head included — would already be the endpoint
configuration.  The two `k = 0` cleanups have no intermediate checkpoint at all
in the dispatcher's own API, so this slice adds exactly one there,
`FixedGammaPayloadDispatcher.first_read_exact`, transporting the cursor phase's
read through the private embedding that module owns; they then close on (ii)
plus the one-cell-per-transition head bound: the read sits at cell `9 + zeros`
at time `2 * zeros + 3`, the endpoint at cell `6` at time `3 * zeros + 6`, and
`zeros + 3` transitions is exactly the distance.

Not here: `qHasOne` is still a second non-reject absorbing outcome, which
`UniformTM.seq` cannot route, so H11 is not composed here; Part A G3g's merged
composite does that, and no statement below mentions raw-input acceptance, `AcceptsAt`,
`DecidesWithin`, a language, or `ContentVerifierBridge`.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival

set_option maxHeartbeats 800000

open PairEncoding
open FixedGammaPayloadDispatcher
open FixedGammaPayloadDispatcherRounds
open FixedGammaPayloadDispatcherDeadline

/-- The dispatcher's terminal set: its `accept` (`qAllZero`), its `reject`
(`qReject`), and the third absorbing endpoint `qHasOne`, which is neither. -/
def IsTerminal (q : Fin stateCount) : Prop :=
  q = qAllZero ∨ q = qHasOne ∨ q = qReject

theorem isTerminal_iff (q : Fin stateCount) :
    IsTerminal q ↔ (q = qAllZero ∨ q = qHasOne ∨ q = qReject) := Iff.rfl

/-- `IsTerminal` is not a chosen subset: it is exactly the absorbing part of the
fixed 84-row table.  Two of the three are the machine's `accept` and `reject`;
`qHasOne` is a third, which is why the `accept`/`reject` pair a `UniformTM.seq`
composition routes does not cover the dispatcher's stopping behaviour. -/
theorem isTerminal_iff_absorbing (q : Fin stateCount) :
    IsTerminal q ↔ ∀ s, machine.step q s = (q, s, .stay) := by
  constructor
  · rw [isTerminal_iff]
    rintro (rfl | rfl | rfl) <;> intro s <;> cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro h
    rw [isTerminal_iff]
    fin_cases q <;> first | decide | exact absurd (h none) (by decide)

theorem terminals_distinct :
    qAllZero ≠ qHasOne ∧ qAllZero ≠ qReject ∧ qHasOne ≠ qReject ∧
      machine.accept = qAllZero ∧ machine.reject = qReject ∧ ¬ IsTerminal qCursorStart ∧
      ¬ IsTerminal qCursorRead := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, ?_, ?_⟩ <;>
    rw [isTerminal_iff] <;> decide

/-- The strict first arrival of *any* dispatcher endpoint, on the actual start
configuration and at an explicit clock. -/
def StrictFirstTerminalAt {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (C : Nat) (q : Fin stateCount) : Prop :=
  (machine.run C (startConfig B x w)).state = q ∧ IsTerminal q ∧
    ∀ s, s < C → ¬ IsTerminal (machine.run s (startConfig B x w)).state

theorem strictFirstTerminalAt_expand {a m : Nat} (B : Nat) (x : Bitstring a)
    (w : Bitstring m) (C : Nat) (q : Fin stateCount) :
    StrictFirstTerminalAt B x w C q ↔
      (machine.run C (startConfig B x w)).state = q ∧
      (q = qAllZero ∨ q = qHasOne ∨ q = qReject) ∧
      ∀ s, s < C →
        (machine.run s (startConfig B x w)).state ≠ qAllZero ∧
        (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
        (machine.run s (startConfig B x w)).state ≠ qReject := by
  simp only [StrictFirstTerminalAt, isTerminal_iff, not_or]

/-- Absorption, once: a terminal at `s` is the whole configuration at every
`C ≥ s`. -/
theorem run_frozen_of_terminal {N B : Nat} (c : Config stateCount N B) {s C : Nat}
    (hs : s ≤ C) (h : IsTerminal (machine.run s c).state) :
    machine.run C c = machine.run s c := by
  rw [show C = s + (C - s) by omega, machine.run_add]
  rcases h with h | h | h
  · exact (endpoints_absorb _).1 h _
  · exact (endpoints_absorb _).2.1 h _
  · exact (endpoints_absorb _).2.2 h _

/-- **The reusable step.**  A terminal-free configuration at `t` was terminal-free
at every earlier time: an endpoint entered earlier would still be there at `t`. -/
theorem no_terminal_of_le {N B t : Nat} (c : Config stateCount N B)
    (h : ¬ IsTerminal (machine.run t c).state) :
    ∀ s, s ≤ t → ¬ IsTerminal (machine.run s c).state := by
  intro s hs hbad
  exact h (by rw [run_frozen_of_terminal c hs hbad]; exact hbad)

/-- Time zero is the retagged G2a handoff in `qCursorStart`, never an endpoint. -/
theorem start_not_terminal {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    ¬ IsTerminal (machine.run 0 (startConfig B x w)).state := by
  have h : (machine.run 0 (startConfig B x w)).state = qCursorStart := rfl
  rw [h, isTerminal_iff]
  decide

/-- A strict first terminal at or below the deadline carries its whole
configuration to the deadline, so G2m's deadline classification reads back
verbatim at the path clock. -/
theorem run_deadline_eq_of_strictFirstTerminalAt {a m B C : Nat} {q : Fin stateCount}
    (x : Bitstring a) (w : Bitstring m) (h : StrictFirstTerminalAt B x w C q)
    (hle : C ≤ deadline (a + m)) :
    machine.run (deadline (a + m)) (startConfig B x w) =
      machine.run C (startConfig B x w) :=
  run_frozen_of_terminal _ hle (by rw [h.1]; exact h.2.1)

/-! The two lemmas below are the leftward mirror of `UniformTM.run_head_le` in
`BudgetTransport`, which bounds rightward motion only.  They are kept private
here rather than generalised into that module, which the whole V1 tree imports,
because this slice needs them at one concrete machine. -/

/-- One transition moves the head address left by at most one cell. -/
private theorem head_le_moveHead_succ {length : Nat} (head : Fin length) (move : Move) :
    head.val ≤ (moveHead head move).val + 1 := by
  cases move with
  | left => simp only [moveHead]; omega
  | stay => simp only [moveHead]; omega
  | right =>
      simp only [moveHead]
      split
      · show head.val ≤ head.val + 1 + 1
        omega
      · omega

private theorem head_le_run_add {N B : Nat} (c : Config stateCount N B) (n : Nat) :
    c.head.val ≤ (machine.run n c).head.val + n := by
  induction n with
  | zero => simp only [UniformTM.run]; omega
  | succ n ih =>
      have h : (machine.run n c).head.val ≤
          (machine.stepConfig (machine.run n c)).head.val + 1 :=
        head_le_moveHead_succ (machine.run n c).head _
      change c.head.val ≤ (machine.stepConfig (machine.run n c)).head.val + (n + 1)
      omega

/-! ### The malformed and zero-width paths -/

/-- Malformed gamma: the shared reject at step `1` is the first endpoint, and the
only earlier time is the start. -/
theorem malformed_strict_first_terminal {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    StrictFirstTerminalAt B x w 1 qReject ∧
      (machine.run 1 (startConfig B x w)).head.val = a + m ∧
      (machine.run 1 (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  have he := malformed_exact (B := B) x w htag hg
  dsimp only at he
  refine ⟨⟨he.1, Or.inr (Or.inr rfl), ?_⟩, he.2.1, he.2.2⟩
  intro s hs
  have hs0 : s = 0 := by omega
  subst hs0
  exact start_not_terminal x w

/-- The one table row the zero-width path needs: out of `qCursorStart` the
dispatcher enters `qCursorBackFirst` or the shared reject, never `qAllZero` and
never `qHasOne`. -/
private theorem step_from_cursorStart {N B : Nat} (c : Config stateCount N B)
    (h : c.state = qCursorStart) :
    (machine.stepConfig c).state = qCursorBackFirst ∨
      (machine.stepConfig c).state = qReject := by
  rcases c with ⟨q, head, tape⟩
  change q = qCursorStart at h
  subst h
  change (machine.step qCursorStart (tape head)).1 = qCursorBackFirst ∨
    (machine.step qCursorStart (tape head)).1 = qReject
  cases tape head with
  | none => exact Or.inr (by decide)
  | some b => cases b with
    | false => exact Or.inr (by decide)
    | true => exact Or.inl (by decide)

/-- Zero width: `qAllZero` at step `2` is the first endpoint.  Step `1` is not an
endpoint because the start row cannot produce `qAllZero`, and a reject there
would still be a reject at step `2`. -/
theorem zero_width_strict_first_terminal {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    StrictFirstTerminalAt B x w 2 qAllZero ∧
      (machine.run 2 (startConfig B x w)).head.val = 7 ∧
      (machine.run 2 (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  have he := zero_width_exact (B := B) x w htag hg
  have hstate : (machine.run 2 (startConfig B x w)).state = qAllZero := by rw [he]
  refine ⟨⟨hstate, Or.inl rfl, ?_⟩, by rw [he], by rw [he]⟩
  intro s hs hbad
  rcases (show s = 0 ∨ s = 1 by omega) with hs0 | hs1
  · subst hs0
    exact start_not_terminal x w hbad
  · subst hs1
    have h1 : (machine.run 1 (startConfig B x w)).state = qAllZero := by
      rw [← run_frozen_of_terminal (startConfig B x w) (show 1 ≤ 2 by omega) hbad]
      exact hstate
    have hstep := step_from_cursorStart (N := pairLength a m) (B := B)
      (startConfig B x w) rfl
    change (machine.run 1 (startConfig B x w)).state = qCursorBackFirst ∨
      (machine.run 1 (startConfig B x w)).state = qReject at hstep
    rcases hstep with h | h
    · exact absurd (h.symm.trans h1) (by decide)
    · exact absurd (h.symm.trans h1) (by decide)

/-! ### The two `k = 0` cleanups -/

/-- The head bound that closes both `k = 0` cleanups.  A terminal strictly before
`3 * zeros + 6` would freeze the run at the cleaned head `6`; the cursor read at
time `2 * zeros + 3` is at cell `9 + zeros` and is not an endpoint, so such a
terminal needs at least `zeros + 3` further transitions — exactly the number the
path still has left. -/
private theorem first_cleanup_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hend : (machine.run (3 * zeros + 6) (startConfig B x w)).head.val = 6) :
    ∀ s, s < 3 * zeros + 6 → ¬ IsTerminal (machine.run s (startConfig B x w)).state := by
  have hread := first_read_exact (B := B) x w htag hg hzero
  dsimp only at hread
  intro s hs hbad
  by_cases hle : s ≤ 2 * zeros + 3
  · refine no_terminal_of_le (startConfig B x w) ?_ s hle hbad
    rw [hread.1, isTerminal_iff]
    decide
  · have hfr := run_frozen_of_terminal (startConfig B x w) (Nat.le_of_lt hs) hbad
    rw [hfr] at hend
    have hsplit : machine.run s (startConfig B x w) =
        machine.run (s - (2 * zeros + 3))
          (machine.run (2 * zeros + 3) (startConfig B x w)) := by
      rw [← machine.run_add]
      congr 1
      omega
    have hdisp := head_le_run_add (machine.run (2 * zeros + 3) (startConfig B x w))
      (s - (2 * zeros + 3))
    rw [← hsplit, hend, hread.2] at hdisp
    omega

/-- First payload cell physically `true`: `qHasOne` at `3 * zeros + 6` is the
first endpoint of any kind. -/
theorem first_true_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (htrue : (Fin.append x w) ⟨9 + zeros, hp⟩ = true) :
    StrictFirstTerminalAt B x w (3 * zeros + 6) qHasOne ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).head.val = 6 ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  have he := first_true_exact (B := B) x w htag hg hzero hp htrue
  have hhead : (machine.run (3 * zeros + 6) (startConfig B x w)).head.val = 6 := by rw [he]
  exact ⟨⟨by rw [he], Or.inr (Or.inl rfl),
    first_cleanup_strict x w htag hg hzero hhead⟩, hhead, by rw [he]⟩

/-- First payload cell virtual: `qAllZero` at the same `3 * zeros + 6` is the
first endpoint of any kind.  The width-zero case is *not* this one; it keeps its
own clock `2` and its own head `7` above. -/
theorem first_virtual_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hvirtual : 9 + zeros = a + m) :
    StrictFirstTerminalAt B x w (3 * zeros + 6) qAllZero ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).head.val = 6 ∧
      (machine.run (3 * zeros + 6) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  have he := first_virtual_exact (B := B) x w htag hg hzero hvirtual
  have hhead : (machine.run (3 * zeros + 6) (startConfig B x w)).head.val = 6 := by rw [he]
  exact ⟨⟨by rw [he], Or.inl rfl,
    first_cleanup_strict x w htag hg hzero hhead⟩, hhead, by rw [he]⟩

/-! ### The positive-round paths -/

/-- A `true` payload cell at a positive index `k`: `qHasOne` at `pendingEndClock`
is the first endpoint of any kind.  G2l already excludes `qHasOne` before the
clock and the other two at all times; this repackages the three. -/
theorem pending_true_strict_first_terminal {a m B zeros k : Nat} (x : Bitstring a)
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
        FixedPairContentMarkerErase.contentTape B x w := by
  have he := true_exact (B := B) x w htag hg hk hkz hprefix htrue
  refine ⟨⟨he.1, Or.inr (Or.inl rfl), ?_⟩, he.2.1, he.2.2.1⟩
  intro s hs hbad
  rcases hbad with h | h | h
  · exact (he.2.2.2.2 s).1 h
  · exact he.2.2.2.1 s hs h
  · exact (he.2.2.2.2 s).2 h

/-- A virtual payload cell at a positive index `k`: `qAllZero` at
`pendingEndClock` is the first endpoint of any kind. -/
theorem pending_virtual_strict_first_terminal {a m B zeros k : Nat} (x : Bitstring a)
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
        FixedPairContentMarkerErase.contentTape B x w := by
  have he := virtual_exact (B := B) x w htag hg hk hkz hprefix hvirtual
  refine ⟨⟨he.1, Or.inl rfl, ?_⟩, he.2.1, he.2.2.1⟩
  intro s hs hbad
  rcases hbad with h | h | h
  · exact he.2.2.2.1 s hs h
  · exact (he.2.2.2.2 s).1 h
  · exact (he.2.2.2.2 s).2 h

/-- A payload that is `false` in every one of its `zeros` cells: `qAllZero` at
`zeroEndClock` is the first endpoint of any kind. -/
theorem exhausted_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    StrictFirstTerminalAt B x w (zeroEndClock zeros) qAllZero ∧
      (machine.run (zeroEndClock zeros) (startConfig B x w)).head.val = 6 ∧
      (machine.run (zeroEndClock zeros) (startConfig B x w)).tape =
        FixedPairContentMarkerErase.contentTape B x w := by
  have he := zero_exact (B := B) x w htag hg hzero hprefix
  refine ⟨⟨he.1, Or.inl rfl, ?_⟩, he.2.1, he.2.2.1⟩
  intro s hs hbad
  rcases hbad with h | h | h
  · exact he.2.2.2.1 s hs h
  · exact (he.2.2.2.2 s).1 h
  · exact (he.2.2.2.2 s).2 h

/-! ### The total statement -/

private theorem prefix_absolute {L zeros k : Nat} (z : Bitstring L)
    (hp : ∀ t, t < k →
      FixedContentTagGate.physicalSymbol z (9 + zeros + t) = some false) :
    ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol z j = some false := by
  intro j hj0 hj1
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj0
  simpa [Nat.add_assoc] using hp t (by omega)

/-- **Every tagged input has a strict first endpoint**, at or below the
length-only deadline, and the configuration there is exactly the deadline
configuration.  So G2m's `tagged_endpoint_classification`, `qHasOne_iff`,
`qAllZero_iff` and `qReject_iff` all read back at the first arrival `C`, and the
dispatcher needs no deadline padding to be stopped.  This is one direction only:
it produces a `C`, and says nothing about which parsed target an endpoint
characterises. -/
theorem tagged_strict_first_terminal {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    ∃ C q, C ≤ deadline (a + m) ∧ StrictFirstTerminalAt B x w C q ∧
      machine.run (deadline (a + m)) (startConfig B x w) =
        machine.run C (startConfig B x w) := by
  have hpack {C : Nat} {q : Fin stateCount} (hle : C ≤ deadline (a + m))
      (h : StrictFirstTerminalAt B x w C q) :
      ∃ C q, C ≤ deadline (a + m) ∧ StrictFirstTerminalAt B x w C q ∧
        machine.run (deadline (a + m)) (startConfig B x w) =
          machine.run C (startConfig B x w) :=
    ⟨C, q, hle, h, run_deadline_eq_of_strictFirstTerminalAt x w h hle⟩
  have htaglen : 8 ≤ a + m := by
    rcases FixedContentTagGate.tag_contract (Fin.append x w) with
      ⟨_, _, _, _, _, _, _, _, _, hlen⟩
    exact hlen htag
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | none =>
      exact hpack (malformedClock_le_deadline htaglen)
        (malformed_strict_first_terminal x w htag hg).1
  | some zeros =>
      have hfit : 9 + zeros ≤ a + m := by
        have h := ((FixedContentGammaTerminator.gamma_contract _).1 zeros hg).1
        omega
      cases zeros with
      | zero =>
          exact hpack (zeroWidthClock_le_deadline htaglen)
            (zero_width_strict_first_terminal x w htag hg).1
      | succ z =>
          obtain ⟨k, -, hp, he⟩ := gamma_payload_first_index (Fin.append x w) hg
          rcases he with he | he | he
          · subst he
            exact hpack (zeroEndClock_le_deadline hfit (by omega))
              (exhausted_strict_first_terminal x w htag hg (by omega) (by
                intro j hj0 hj1
                exact prefix_absolute (Fin.append x w) hp j hj0 (by omega))).1
          · obtain ⟨hkz, htrue⟩ := he
            rcases Nat.eq_zero_or_pos k with hk0 | hk1
            · subst hk0
              rw [Nat.add_zero] at htrue
              have hpos : 9 + (z + 1) < a + m := by
                unfold FixedContentTagGate.physicalSymbol at htrue
                split at htrue
                · assumption
                · contradiction
              exact hpack (firstEndClock_le_deadline hfit)
                (first_true_strict_first_terminal x w htag hg (by omega) hpos (by
                  simpa [FixedContentTagGate.physicalSymbol, hpos] using htrue)).1
            · exact hpack (pendingEndClock_le_deadline hfit hk1 hkz)
                (pending_true_strict_first_terminal x w htag hg hk1 hkz
                  (prefix_absolute (Fin.append x w) hp) htrue).1
          · obtain ⟨hkz, hvirt⟩ := he
            rcases Nat.eq_zero_or_pos k with hk0 | hk1
            · subst hk0
              exact hpack (firstEndClock_le_deadline hfit)
                (first_virtual_strict_first_terminal x w htag hg (by omega)
                  (by omega)).1
            · exact hpack (pendingEndClock_le_deadline hfit hk1 hkz)
                (pending_virtual_strict_first_terminal x w htag hg hk1 hkz
                  (prefix_absolute (Fin.append x w) hp) hvirt).1

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherFirstArrival
