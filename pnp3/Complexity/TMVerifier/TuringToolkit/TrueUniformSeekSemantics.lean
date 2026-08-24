import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminal

/-!
# T1c-3: canonical semantics of the true uniform seek

This module closes the T1 execution chain.  T1b-C delivered the three exact
`TM.runConfig` theorems *from the genuine `T1M.initialConfig`* to the two
terminal boundaries, at the closed clock `t1DecideTotal r`.  T1c-2 delivered
the three exact terminal theorems *from those boundary configurations* to the
literal `t1AcceptState` / `t1RejectState`, at the closed clock
`t1TerminalSteps r`.  Here the two halves are spliced with `runConfig_add`,
the result is padded through the stable sinks up to the **unchanged public
clock** `t1Clock`, and the public `TM.run` / `TM.accepts` semantics are
computed exactly.

## What is proved

* `t1TotalSteps r = t1DecideTotal r + t1TerminalSteps r` — the total honest
  step count, selected by `r.data[r.index]?` exactly as its two summands are.
* `t1CS_runConfig_total_success_exact`, `t1CS_runConfig_total_oob_exact`,
  `t1CS_runConfig_total_oob_empty_exact` — from `T1M.initialConfig
  (t1Point (encodeT1 r))`, after exactly `t1TotalSteps r` genuine steps, the
  machine sits in the literal accept/reject state with head `0` and an exact
  final tape.
* `t1CS_runConfig_total_reject_exact` — the two out-of-bounds arms merged: the
  final tape is *bit-for-bit* `(T1M.initialConfig (t1Point (encodeT1 r))).tape`.
* `t1CS_totalSteps_le_clock` — `t1TotalSteps r ≤ t1Clock (encodeT1 r).length`.
  The public clock is untouched: `t1CS.timeBound` is still `t1Clock`.
* `t1CS_run_success_exact`, `t1CS_run_reject_exact` — the *full* public
  `T1M.run` at the public clock, obtained by padding only inside the stable
  `accept` / `reject` sinks (`t1CS_runConfig_sink`).  No other state is ever
  claimed stable.
* `t1CS_accepts_eq_isSome` — `TM.accepts (M := T1M) … = (r.data[r.index]?).isSome`,
  with `t1CS_accepts_iff` / `t1CS_accepts_eq_decide_lt` as the equivalent
  propositional and range forms.  This is *full* acceptance of the compiled
  machine — the complete dependent `Sigma` state compared against
  `T1M.accept` — not a phase-only or local-state-only shortcut.
* `t1CS_run_output_at` / `t1CS_run_tape_off` / `t1CS_run_success_tape_eq` — on
  the accepting run the output cell `t1OutputPosition r` holds the selected
  bit `v` and **every** other cell agrees with the input tape; on the
  rejecting run (`t1CS_run_reject_tape_eq`) the whole tape agrees with the
  input tape and `t1CS_accepts_eq_isSome` returns `false`.

## Scope

* **Canonical inputs only.**  Every theorem below is stated at the point
  `t1Point (encodeT1 r)` for a `T1Request r`, i.e. at the canonical encoder
  image.  Nothing is claimed for physical tapes that are not `encodeT1 r`.
* **The malformed / trailing-input caveat is retained verbatim.**
  `T1Physical` remains reserved vocabulary: no theorem here consumes or
  discharges it, and no rejection theorem is claimed for non-canonical,
  malformed, or trailing-padded physical tapes.  A tape that fails to decode
  is outside this module's scope; the T1a validation prefix is the only place
  where grammar failure is even mentioned, and it is not lifted to a
  `TM.accepts` statement.
* **One fixed machine, no advice.**  Everything runs on the single
  zero-parameter program `t1CS`; the transition table is never unfolded
  outside `TrueUniformSeek.lean`, and no runtime, offset, or advice string is
  supplied by any caller.  The public clock `t1Clock` is unchanged — this
  module only *fits inside* it.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## The total honest clock -/

/-- **The total step count of the canonical run.**  The decision prefix
(T1a validation, rewind, cursor installation, seek loop, terminal handoff)
plus the terminal arm (output write and index repair).  Both summands are
selected by `r.data[r.index]?`, so `t1TotalSteps` is too. -/
def t1TotalSteps (r : T1Request) : Nat :=
  t1DecideTotal r + t1TerminalSteps r

theorem t1TotalSteps_some (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    t1TotalSteps r = t1DecideTotal r + t1SuccessTerminalSteps r := by
  unfold t1TotalSteps
  rw [t1TerminalSteps_some r v hv]

theorem t1TotalSteps_none (r : T1Request) (hv : r.data[r.index]? = none) :
    t1TotalSteps r = t1DecideTotal r + t1OobTerminalSteps r := by
  unfold t1TotalSteps
  rw [t1TerminalSteps_none r hv]

/-! ## Exact composition from the real initial configuration -/

/-- **The exact accepting run, from the genuine initial configuration.**
When the selected slot exists and holds `v`, exactly `t1TotalSteps r` genuine
steps take `T1M.initialConfig (t1Point (encodeT1 r))` to the literal
`t1AcceptState` with the head back on cell `0` and the final tape
`t1OutputFrames r v`. -/
theorem t1CS_runConfig_total_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r v).flatMap T1Frame.bits))
        .accept .p0 false false false false := by
  rw [t1TotalSteps_some r v hv, runConfig_add,
    t1CS_runConfig_decide_success_exact r v hv,
    t1CS_terminal_success_exact r v hv]

/-- **The exact rejecting run with nonempty data.**  The final tape is
`t1OutputFrames r false`, i.e. the fully repaired canonical layout. -/
theorem t1CS_runConfig_total_oob_exact (r : T1Request)
    (hv : r.data[r.index]? = none) (hne : 0 < r.data.length) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r false).flatMap T1Frame.bits))
        .reject .p0 false false false false := by
  have hlt : r.data.length - 1 < r.data.length := by omega
  obtain ⟨v, hlast⟩ : ∃ v, r.data[r.data.length - 1]? = some v :=
    ⟨r.data[r.data.length - 1], List.getElem?_eq_getElem hlt⟩
  rw [t1TotalSteps_none r hv, runConfig_add,
    t1CS_runConfig_decide_oob_exact r v hv hne hlast,
    t1CS_terminal_oob_exact r v hv hne]

/-- **The exact rejecting run with empty data.**  The tape is never written
at all: the final tape is literally the initial tape. -/
theorem t1CS_runConfig_total_oob_empty_exact (r : T1Request)
    (hdata : r.data = []) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false := by
  have hlen : r.data.length = 0 := by rw [hdata]; rfl
  have hnone : r.data[r.index]? = none := (t1Selected_none_iff r).2 (by omega)
  rw [t1TotalSteps_none r hnone, runConfig_add,
    t1CS_runConfig_decide_oob_empty_exact r hdata,
    t1CS_terminal_oob_empty_exact r hdata]

/-- **The two rejecting arms merged.**  Whenever the selected slot does not
exist, the run leaves the tape *bit-for-bit* equal to the input tape and
lands in the literal reject state with the head on cell `0`. -/
theorem t1CS_runConfig_total_reject_exact (r : T1Request)
    (hv : r.data[r.index]? = none) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1TotalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false := by
  by_cases hL : r.data.length = 0
  · exact t1CS_runConfig_total_oob_empty_exact r
      (List.eq_nil_of_length_eq_zero hL)
  · have hne : 0 < r.data.length := by omega
    have h := t1CS_runConfig_total_oob_exact r hv hne
    rwa [t1CS_oob_final_tape_eq r] at h

/-! ## The total clock fits the unchanged public clock -/

private theorem t1sClockArith (N k j L P Q R : Nat)
    (hk : k ≤ N) (hj : j ≤ N) (hL : L ≤ N) (hP : P ≤ R) (hQ : Q ≤ R) :
    (2 * N + 9 + (4 * k + 17 + (8 * P + 29 * k) + (8 * k + 8)) +
        (17 * k + 8 * L + 35) ≤ 128 * R + 256 * N + 256) ∧
      (2 * N + 9 + (4 * k + 17 + (8 * Q + 29 * j) + (16 * j + 32)) +
        (4 * k + 13 * L + 14) ≤ 128 * R + 256 * N + 256) ∧
      (2 * N + 9 + (4 * k + 12) + (4 * k + 13 * L + 14) ≤
        128 * R + 256 * N + 256) :=
  ⟨by omega, by omega, by omega⟩

/-- **The whole canonical run fits inside the public clock.**  Every branch —
success, nonempty out-of-bounds, empty out-of-bounds — plus the terminal arm
stays below `t1Clock (encodeT1 r).length`, so the public `TM.run` has room for
the exact split above followed by sink padding.  `t1Clock` itself is
untouched. -/
theorem t1CS_totalSteps_le_clock (r : T1Request) :
    t1TotalSteps r ≤ t1Clock (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hk : r.index ≤ (encodeT1 r).length := by omega
  have hj : r.data.length - 1 ≤ (encodeT1 r).length := by omega
  have hLen : r.data.length ≤ (encodeT1 r).length := by omega
  have hP : r.index * r.index ≤
      (encodeT1 r).length * (encodeT1 r).length := Nat.mul_le_mul hk hk
  have hQ : (r.data.length - 1) * (r.data.length - 1) ≤
      (encodeT1 r).length * (encodeT1 r).length := Nat.mul_le_mul hj hj
  have harith := t1sClockArith (encodeT1 r).length r.index (r.data.length - 1)
    r.data.length (r.index * r.index)
    ((r.data.length - 1) * (r.data.length - 1))
    ((encodeT1 r).length * (encodeT1 r).length) hk hj hLen hP hQ
  have hclock : t1Clock (encodeT1 r).length =
      128 * ((encodeT1 r).length * (encodeT1 r).length) +
        256 * (encodeT1 r).length + 256 := by
    simp only [t1Clock, pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one,
      Nat.one_mul]
    omega
  rw [hclock]
  unfold t1TotalSteps t1DecideTotal
  cases hsel : r.data[r.index]? with
  | some v =>
      rw [t1DecideSteps_some r v hsel, t1TerminalSteps_some r v hsel]
      unfold t1SuccessSteps t1SuccessTerminalSteps
      rw [t1LoopSteps_mul]
      exact harith.1
  | none =>
      rw [t1DecideSteps_none r hsel, t1TerminalSteps_none r hsel]
      unfold t1OobTerminalSteps
      by_cases hL : r.data.length = 0
      · rw [t1OobSteps_nil r hL]
        exact harith.2.2
      · rw [t1OobSteps_cons r hL, t1LoopSteps_mul]
        exact harith.2.1

/-! ## Padding through the stable sinks only

The two lemmas below are the *only* padding steps in this module, and they
fire exclusively on `accept` / `reject` configurations, where
`t1CS_runConfig_sink` supplies genuine stability.  No intermediate mode is
ever assumed idle. -/

private theorem t1sPad_accept (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .accept .p0 false false false false)
        steps =
      t1AlignedConfig n h hh tape .accept .p0 false false false false :=
  t1CS_runConfig_sink _ t1AcceptState (Or.inl rfl) rfl steps

private theorem t1sPad_reject (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .reject .p0 false false false false)
        steps =
      t1AlignedConfig n h hh tape .reject .p0 false false false false :=
  t1CS_runConfig_sink _ t1RejectState (Or.inr rfl) rfl steps

/-- The public run is `runConfig` at the public clock; the machine's declared
runtime is still exactly `t1Clock`. -/
private theorem t1sRun_eq (r : T1Request) :
    T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r)) =
      TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1Clock (encodeT1 r).length) := rfl

private theorem t1sClock_split (r : T1Request) :
    ∃ m, t1Clock (encodeT1 r).length = t1TotalSteps r + m :=
  ⟨t1Clock (encodeT1 r).length - t1TotalSteps r, by
    have := t1CS_totalSteps_le_clock r
    omega⟩

/-! ## The full public run -/

/-- **The full accepting run.**  At the unchanged public clock
`t1Clock (encodeT1 r).length`, the compiled machine `T1M` on the canonical
input `t1Point (encodeT1 r)` ends in the literal `t1AcceptState`, head on
cell `0`, with final tape `t1OutputFrames r v`. -/
theorem t1CS_run_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r v).flatMap T1Frame.bits))
        .accept .p0 false false false false := by
  obtain ⟨m, hm⟩ := t1sClock_split r
  rw [t1sRun_eq r, hm, runConfig_add,
    t1CS_runConfig_total_success_exact r v hv, t1sPad_accept]

/-- **The full rejecting run.**  At the same public clock, when the selected
slot does not exist the machine ends in the literal `t1RejectState`, head on
cell `0`, with the tape bit-for-bit equal to the input tape. -/
theorem t1CS_run_reject_exact (r : T1Request)
    (hv : r.data[r.index]? = none) :
    T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false := by
  obtain ⟨m, hm⟩ := t1sClock_split r
  rw [t1sRun_eq r, hm, runConfig_add,
    t1CS_runConfig_total_reject_exact r hv, t1sPad_reject]

/-- The head is back on cell `0` on every canonical run. -/
theorem t1CS_run_head_zero (r : T1Request) :
    ((T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).head : Nat)
      = 0 := by
  cases hsel : r.data[r.index]? with
  | some v => rw [t1CS_run_success_exact r v hsel]; rfl
  | none => rw [t1CS_run_reject_exact r hsel]; rfl

/-! ## Full acceptance semantics

`TM.accepts` compares the *complete* dependent control state
`Σ i : Fin 1, T1State` against `T1M.accept = ⟨t1CS.acceptPhase,
t1CS.acceptState⟩`.  The two lemmas below discharge that comparison from the
exact final configurations — the accepting side by the literal state equality
and the rejecting side by `t1RejectState ≠ t1AcceptState`.  Neither route
weakens the claim to a phase-only test. -/

private theorem t1sReject_ne_accept : t1RejectState ≠ t1AcceptState := by
  decide

private theorem t1sAccept_state_eq (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) :
    (t1AlignedConfig n h hh tape .accept .p0 false false false false).state =
      T1M.accept := rfl

private theorem t1sReject_state_ne (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) :
    ¬ ((t1AlignedConfig n h hh tape .reject .p0 false false false false).state =
      T1M.accept) := by
  intro hcon
  exact t1sReject_ne_accept (congrArg Sigma.snd hcon)

/-- **The T1 acceptance theorem.**  The one fixed machine `t1CS`, run on the
canonical encoding of `r` for its own declared public clock, accepts exactly
when the requested slot exists.  This is full `TM.accepts` on the compiled
machine: the whole dependent state is compared to `T1M.accept`. -/
theorem t1CS_accepts_eq_isSome (r : T1Request) :
    TM.accepts (M := T1M) (encodeT1 r).length (t1Point (encodeT1 r)) =
      (r.data[r.index]?).isSome := by
  unfold TM.accepts
  cases hsel : r.data[r.index]? with
  | some v =>
      rw [t1CS_run_success_exact r v hsel]
      exact decide_eq_true (t1sAccept_state_eq _ _ _ _)
  | none =>
      rw [t1CS_run_reject_exact r hsel]
      exact decide_eq_false (t1sReject_state_ne _ _ _ _)

/-- Propositional form of the acceptance theorem. -/
theorem t1CS_accepts_iff (r : T1Request) :
    TM.accepts (M := T1M) (encodeT1 r).length (t1Point (encodeT1 r)) = true ↔
      (r.data[r.index]?).isSome = true := by
  rw [t1CS_accepts_eq_isSome r]

/-- Acceptance as the in-range test on the request. -/
theorem t1CS_accepts_eq_decide_lt (r : T1Request) :
    TM.accepts (M := T1M) (encodeT1 r).length (t1Point (encodeT1 r)) =
      decide (r.index < r.data.length) := by
  rw [t1CS_accepts_eq_isSome r]
  cases hsel : r.data[r.index]? with
  | some v =>
      have : ¬ (r.data.length ≤ r.index) := by
        intro hle
        rw [(t1Selected_none_iff r).2 hle] at hsel
        exact Option.noConfusion hsel
      simp only [Option.isSome_some]
      exact (decide_eq_true (by omega)).symm
  | none =>
      have hle : r.data.length ≤ r.index := (t1Selected_none_iff r).1 hsel
      simp only [Option.isSome_none]
      exact (decide_eq_false (by omega)).symm

/-! ## Output correctness on the full run -/

/-- **The accepting run's tape, globally.**  It is the input tape with the
single cell `t1OutputPosition r` overwritten by the selected bit. -/
theorem t1CS_run_success_tape_eq (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape =
      t1WriteCell (t1OutputPosition r) v
        (T1M.initialConfig (t1Point (encodeT1 r))).tape := by
  rw [t1CS_run_success_exact r v hv, t1AlignedConfig_tape,
    t1CS_success_final_tape_eq r v]

/-- **The output cell of the accepting run carries the selected bit.** -/
theorem t1CS_run_output_at (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v)
    (i : Fin (T1M.tapeLength (encodeT1 r).length))
    (hi : (i : Nat) = t1OutputPosition r) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape i = v := by
  rw [t1CS_run_success_exact r v hv, t1AlignedConfig_tape]
  exact t1CS_success_final_tape_at r v i hi

/-- **Every other cell of the accepting run's tape is the input cell.** -/
theorem t1CS_run_tape_off (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v)
    (i : Fin (T1M.tapeLength (encodeT1 r).length))
    (hi : (i : Nat) ≠ t1OutputPosition r) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape i =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape i := by
  rw [t1CS_run_success_exact r v hv, t1AlignedConfig_tape]
  exact t1CS_success_final_tape_off r v i hi

/-- **The rejecting run leaves the tape untouched**, and does not accept. -/
theorem t1CS_run_reject_tape_eq (r : T1Request)
    (hv : r.data[r.index]? = none) :
    (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape := by
  rw [t1CS_run_reject_exact r hv, t1AlignedConfig_tape]

theorem t1CS_run_reject_not_accepts (r : T1Request)
    (hv : r.data[r.index]? = none) :
    TM.accepts (M := T1M) (encodeT1 r).length (t1Point (encodeT1 r)) = false := by
  rw [t1CS_accepts_eq_isSome r, hv]
  rfl

/-- **The canonical semantics in one statement.**  On every canonical input
the machine accepts exactly when the slot exists, and the observable output
cell holds the selected bit while all other cells are preserved. -/
theorem t1CS_canonical_semantics (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    TM.accepts (M := T1M) (encodeT1 r).length (t1Point (encodeT1 r)) = true ∧
      (∀ i : Fin (T1M.tapeLength (encodeT1 r).length),
        (i : Nat) = t1OutputPosition r →
          (T1M.run (n := (encodeT1 r).length)
            (t1Point (encodeT1 r))).tape i = v) ∧
      (∀ i : Fin (T1M.tapeLength (encodeT1 r).length),
        (i : Nat) ≠ t1OutputPosition r →
          (T1M.run (n := (encodeT1 r).length) (t1Point (encodeT1 r))).tape i =
            (T1M.initialConfig (t1Point (encodeT1 r))).tape i) := by
  refine ⟨?_, fun i hi => t1CS_run_output_at r v hv i hi,
    fun i hi => t1CS_run_tape_off r v hv i hi⟩
  rw [t1CS_accepts_eq_isSome r, hv]
  rfl

end Pnp3.Internal.PsubsetPpoly.TM
