import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoop

/-!
# T1b-C: the genuine seek-loop driver

This module closes the **iteration** of the destructive seek loop that T1b-B
left open.  It adds no machine, no state, no clock, no vocabulary and no
advice: every `TM.runConfig` fact below is assembled from

* T1b-B's one-iteration theorems `t1CS_loop_iteration_exact` and
  `t1CS_loop_oob_exact`, and its backward multi-frame scan
  `t1CS_scan_back_skip`;
* T1b-A's installation capstone `t1CS_mutationConfig_zero`, its
  `bof`-transition macro-step `t1CS_seekIndexBack_frame_success`, and its
  empty-data public-clock theorem `t1CS_run_encoded_oob_empty_data`;
* T1a's validation/rewind capstone `t1CS_validate_rewind_encoded_exact`.

The control table is never unfolded here, and the machine is the one fixed
`T1M` throughout.

## The loop clock

```text
t1LoopSteps m = 8 * m ^ 2 + 29 * m
```

is exactly the sum of T1b-B's one-iteration costs: `t1LoopSteps (m+1) -
t1LoopSteps m = 16 * m + 37` (`t1LoopSteps_succ`), which is the exact cost
`t1CS_loop_iteration_exact` charges for the step `Σ(j) → Σ(j+1)` at `j = m`.

## Results proved in this module

* `t1CS_loop_iterate_exact` — the **loop driver**: a genuine induction on `m`
  over `TM.runConfig`.  For `m ≤ r.index` and `m < r.data.length`, starting
  from `Σ(r, 0, r.data[0])` — the configuration T1b-A's installation actually
  reaches — the machine is in `Σ(r, m, r.data[m])` after exactly
  `t1LoopSteps m` genuine steps.  Both endpoints are the canonical layout at
  their own index, so the theorem carries the full tape conservation
  statement of T1b-B, iterated.
* `t1CS_loop_success_tail_exact` — the **success tail**: from `Σ(r, r.index,
  latch)`, where the index field is fully spent, the backward scan crosses
  `spent^k · separator · data^k` and the `bof` anchor hands control to the
  idle `successStart` boundary in exactly `8 * r.index + 8` steps.  The tape
  is unchanged and stated exactly: it is still the canonical layout
  `t1LoopFrames r r.index`, i.e. the *unique* cursor frame sits in data slot
  `r.index`, the index field holds `r.index` `spent` markers and no `index`
  marker, and the head is left on cell `0`, the first cell of the `bof`
  anchor.  The latch is carried through untouched.
* `t1CS_loop_success_from_zero_exact`, `t1CS_loop_oob_from_zero_exact` — the
  two composites from `Σ(0)`, with exact closed step counts.
* `t1CS_runConfig_decide_success_exact`,
  `t1CS_runConfig_decide_oob_exact`,
  `t1CS_runConfig_decide_oob_empty_exact` — the three exact `TM.runConfig`
  theorems from the **real** `T1M.initialConfig`, all with the same closed
  clock `t1DecideTotal r`, whose value is selected by `r.data[r.index]?`
  through `t1DecideSteps`.  The dependent `if`/`match` equality on
  configurations is genuinely unwieldy (each branch carries its own head
  position, tape and latch), so the terminal split is delivered as these
  exact case theorems keyed by `r.data[r.index]? = some v` / `= none`, plus
  the `none` split into empty and nonempty data.  No runtime is ever
  supplied by the caller.
* `t1CS_decideTotal_le_clock` — the whole decision prefix fits inside the
  public clock `t1Clock (encodeT1 r).length`.
* `t1CS_run_encoded_decide_success`, `t1CS_run_encoded_decide_oob_nonempty`,
  `t1CS_run_encoded_decide_oob_empty` and the dichotomy
  `t1CS_run_encoded_decide_oob` — the same split under the genuine public
  clock: the boundary is padded out with the idle-boundary run theorems, so
  `T1M.run` itself is the boundary configuration.

## Deliberately *not* claimed here

`successStart` and `oobStart` remain **idle semantic boundaries** owned by
T1c.  Nothing below claims acceptance, rejection, an output write, or repair
of the consumed index field.  In particular the out-of-bounds boundary is
reached on the *intermediate* tape `t1LoopFramesRestored`, whose index field
is spent, exactly as T1b-B documented.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## The closed-form loop clock -/

/-- **The exact cumulative cost of `m` genuine loop iterations.**  T1b-B
charges `16 * j + 37` steps for the iteration `Σ(j) → Σ(j+1)`; the sum of
those costs for `j < m` is this closed form. -/
def t1LoopSteps (m : Nat) : Nat := 8 * m ^ 2 + 29 * m

@[simp] theorem t1LoopSteps_zero : t1LoopSteps 0 = 0 := by
  simp [t1LoopSteps]

theorem t1LoopSteps_one : t1LoopSteps 1 = 37 := by
  simp [t1LoopSteps]

/-- Squaring a successor, without the `ring` tactic (which is outside this
module's import closure). -/
private theorem t1dSqSucc (x : Nat) : (x + 1) ^ 2 = x * x + 2 * x + 1 := by
  have h1 : (x + 1) * (x + 1) = x * (x + 1) + (x + 1) := Nat.succ_mul x (x + 1)
  have h2 : x * (x + 1) = x * x + x := Nat.mul_succ x x
  rw [pow_two]
  omega

/-- The pow-free normal form, used by the clock estimate. -/
theorem t1LoopSteps_mul (m : Nat) : t1LoopSteps m = 8 * (m * m) + 29 * m := by
  simp only [t1LoopSteps, pow_two]

/-- **The exact sum recurrence.**  The increment is precisely the
one-iteration cost `16 * m + 37` of `t1CS_loop_iteration_exact`. -/
theorem t1LoopSteps_succ (m : Nat) :
    t1LoopSteps (m + 1) = t1LoopSteps m + (16 * m + 37) := by
  simp only [t1LoopSteps]
  rw [t1dSqSucc m, pow_two]
  omega

/-! ## Local layout helpers

T1b-B's own layout splits are `private`, so the three list facts the driver
needs are re-derived here.  They are pure list algebra: no execution claim,
no new vocabulary. -/

private theorem t1dSkipRun_mem (j : Nat) (d : List Bool) :
    ∀ f ∈ (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
        (d.take j).map T1Frame.data),
      f = .spent ∨ f = .separator ∨ ∃ v, f = .data v := by
  intro f hf
  rcases List.mem_append.1 hf with h1 | h2
  · rcases List.mem_append.1 h1 with h | h
    · exact Or.inl (List.eq_of_mem_replicate h)
    · exact Or.inr (Or.inl (by simpa using h))
  · rcases List.mem_map.1 h2 with ⟨v, _, rfl⟩
    exact Or.inr (Or.inr ⟨v, rfl⟩)

private theorem t1dLoopFrames_split_scan (r : T1Request) (j : Nat) :
    t1LoopFrames r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j) T1Frame.index) ++
        (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take j).map T1Frame.data) ++
        (T1Frame.cursor :: ((r.data.drop (j+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank])) := by
  simp [t1LoopFrames, t1MutationFrames, List.append_assoc]

private theorem t1dLoopFrames_split_bof (r : T1Request) (j : Nat) :
    t1LoopFrames r j =
      ([] : List T1Frame) ++ T1Frame.bof ::
        (List.replicate (r.index - j) T1Frame.index ++
          List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take j).map T1Frame.data ++ [T1Frame.cursor] ++
          (r.data.drop (j+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  simp [t1LoopFrames, t1MutationFrames, List.append_assoc]

private theorem t1dIdxPre_length (r : T1Request) (j : Nat) :
    ([T1Frame.bof] ++ List.replicate (r.index - j) T1Frame.index).length =
      r.index - j + 1 := by
  simp

private theorem t1dSkipRun_length (r : T1Request) (j : Nat)
    (hj : j ≤ r.data.length) :
    (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
      (r.data.take j).map T1Frame.data).length = 2 * j + 1 := by
  simp
  omega

/-! ## Physical safety facts

All three are unconditional consequences of the encoder length, so the
configurations below never carry a hypothesis-dependent safety proof. -/

/-- The `bof` anchor and its successor cell are inside the tape. -/
theorem t1dBof_safe (r : T1Request) :
    (0 : Nat) + 4 < T1M.tapeLength (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  omega

/-- The head position the out-of-bounds boundary is reached on, for the last
data slot, is inside the tape. -/
theorem t1dOobHead_safe (r : T1Request) :
    4 * (r.index + (r.data.length - 1) + 3) + 3 <
      T1M.tapeLength (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  omega

/-- The head position the empty-data out-of-bounds boundary is reached on is
inside the tape. -/
theorem t1dEmptyOobHead_safe (r : T1Request) :
    4 * (r.index + 2) + 3 < T1M.tapeLength (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  omega

/-! ## The loop driver -/

/-- **The genuine loop induction.**  For every `m ≤ r.index` with
`m < r.data.length`, the machine started in the canonical configuration
`Σ(r, 0, r.data[0])` — the one T1b-A's installation genuinely reaches — is
in `Σ(r, m, r.data[m])` after exactly `t1LoopSteps m` genuine
`TM.runConfig` steps.

The proof is an induction on `m` whose step is exactly one application of
T1b-B's `t1CS_loop_iteration_exact`; the arithmetic is the exact sum
recurrence `t1LoopSteps_succ`.  Because both endpoints are the canonical
layout at their own index, the statement carries the iterated conservation
content: `m` index units have been consumed and `m` `spent` markers written,
the unique cursor frame has walked from data slot `0` to data slot `m`,
slots `0 … m-1` carry their original data bits again, and the `bof` anchor,
the separator, the untouched data slots, the observable output frame, the
finish frame and the blank frame are all unchanged. -/
theorem t1CS_loop_iterate_exact (r : T1Request) (b : Bool)
    (h0 : 0 < r.data.length) (hb : r.data[0]? = some b) :
    ∀ (m : Nat), m ≤ r.index → ∀ (hmd : m < r.data.length) (v : Bool),
      r.data[m]? = some v →
      TM.runConfig (M := T1M) (t1MutationConfig r 0 h0 b) (t1LoopSteps m) =
        t1MutationConfig r m hmd v := by
  intro m
  induction m with
  | zero =>
      intro _ hmd v hv
      have hvb : v = b := by
        rw [hb] at hv
        exact (Option.some.inj hv).symm
      subst hvb
      rw [t1LoopSteps_zero]
      rfl
  | succ m ih =>
      intro hm hmd v hv
      have hmk : m < r.index := by omega
      have hmd' : m < r.data.length := by omega
      obtain ⟨w, hw⟩ : ∃ w, r.data[m]? = some w :=
        ⟨r.data[m], List.getElem?_eq_getElem hmd'⟩
      have hIH := ih (by omega) hmd' w hw
      have hstep := t1CS_loop_iteration_exact r m hmk hmd w v hw hv
      rw [t1LoopSteps_succ, runConfig_add, hIH]
      exact hstep

/-- The loop driver with flat binders: the same statement, packaged for
downstream use. -/
theorem t1CS_loop_reach_exact (r : T1Request) (m : Nat) (hm : m ≤ r.index)
    (hmd : m < r.data.length) (b v : Bool) (hb : r.data[0]? = some b)
    (hv : r.data[m]? = some v) :
    TM.runConfig (M := T1M)
        (t1MutationConfig r 0 (Nat.lt_of_le_of_lt (Nat.zero_le m) hmd) b)
        (t1LoopSteps m) =
      t1MutationConfig r m hmd v :=
  t1CS_loop_iterate_exact r b (Nat.lt_of_le_of_lt (Nat.zero_le m) hmd) hb m hm
    hmd v hv

/-! ## The success tail -/

/-- **The success tail.**  At `j = r.index` the index field is fully spent,
so the backward scan crosses the whole run `spent^k · separator · data^k`
(`4` genuine steps per frame, `k = r.index`) and the following
`seekIndexBack` frame read finds the `bof` anchor, which hands control to
the idle `successStart` boundary: exactly `4 * (2k+1) + 4 = 8k + 8` steps.

Everything is stated exactly.  The tape is *unchanged* — it is still the
canonical layout `t1LoopFrames r r.index`, that is

```text
bof · spent^k · separator · data(b₀)…data(b_{k-1}) · cursor
    · data(b_{k+1})… · output(false) · finish · blank
```

so the index field carries `k` `spent` markers and **no** `index` marker,
and the unique cursor frame sits in data slot `k`.  The head is left on cell
`0`, the first cell of the `bof` anchor, and the latch is carried through
untouched: the tail never inspects it. -/
theorem t1CS_loop_success_tail_exact (r : T1Request) (latch : Bool)
    (hk : r.index < r.data.length) :
    TM.runConfig (M := T1M) (t1MutationConfig r r.index hk latch)
        (8 * r.index + 8) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .successStart .p0 false false false latch := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  have hcb : t1CursorBase r r.index = 4 * (r.index + r.index + 2) := by
    unfold t1CursorBase t1CursorFrameIndex
    omega
  have hL1 := t1dIdxPre_length r r.index
  have hLS := t1dSkipRun_length r r.index (Nat.le_of_lt hk)
  have hsafe0 : (0 : Nat) + 4 < T1M.tapeLength (encodeT1 r).length :=
    t1dBof_safe r
  -- Phase A: the backward scan crosses `spent^k · separator · data^k`.
  have hA : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + r.index + 2) - 1)
        (by omega)
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false latch)
      (4 * (2 * r.index + 1)) =
      t1AlignedConfig (encodeT1 r).length 3 (by omega)
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false latch := by
    have hscan := t1CS_scan_back_skip (encodeT1 r).length
      ([T1Frame.bof] ++ List.replicate (r.index - r.index) T1Frame.index)
      (List.replicate r.index T1Frame.spent ++ [T1Frame.separator] ++
        (r.data.take r.index).map T1Frame.data)
      (T1Frame.cursor :: ((r.data.drop (r.index+1)).map T1Frame.data ++
        [T1Frame.output false, T1Frame.finish, T1Frame.blank]))
      (by rw [hL1]; omega) (t1dSkipRun_mem r.index r.data)
      (by rw [hL1, hLS]; omega) latch
    rw [← t1dLoopFrames_split_scan r r.index] at hscan
    simp only [hL1, hLS,
      show 4 * (r.index - r.index + 1 + (2 * r.index + 1)) - 1 =
        4 * (r.index + r.index + 2) - 1 from by omega,
      show 4 * (r.index - r.index + 1) - 1 = 3 from by omega] at hscan
    exact hscan
  -- Phase B: the `bof` anchor hands control to the idle success boundary.
  have hbits : t1PhysicalBitsAt hsafe0
      (t1ListTape (n := (encodeT1 r).length)
        ((t1LoopFrames r r.index).flatMap T1Frame.bits)) =
      T1Frame.bof.bits := by
    rw [t1dLoopFrames_split_bof r r.index]
    exact t1PhysicalBitsAt_flatMap (encodeT1 r).length [] _ T1Frame.bof
      (by simpa using hsafe0)
  have hB : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length 3 (by omega)
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false latch) 4 =
      t1AlignedConfig (encodeT1 r).length 0 (by omega)
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .successStart .p0 false false false latch :=
    t1CS_seekIndexBack_frame_success (encodeT1 r).length 0 hsafe0
      (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits)) latch hbits
  simp only [t1MutationConfig, t1MutationTape_eq_listTape, hcb]
  rw [show 8 * r.index + 8 = 4 * (2 * r.index + 1) + 4 from by omega,
    runConfig_add, hA, hB]

/-! ## The two composites from `Σ(0)` -/

/-- **Success, from the configuration the installation reaches.**  When the
selected slot `r.index` exists, the driver walks the cursor to it and the
success tail reaches the idle `successStart` boundary, in exactly
`t1LoopSteps r.index + (8 * r.index + 8)` genuine steps, with the latch
holding `r.data[r.index]`. -/
theorem t1CS_loop_success_from_zero_exact (r : T1Request) (b v : Bool)
    (hk : r.index < r.data.length) (hb : r.data[0]? = some b)
    (hv : r.data[r.index]? = some v) :
    TM.runConfig (M := T1M)
        (t1MutationConfig r 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hk) b)
        (t1LoopSteps r.index + (8 * r.index + 8)) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .successStart .p0 false false false v := by
  have h0 : 0 < r.data.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hreach := t1CS_loop_iterate_exact r b h0 hb r.index (le_refl _) hk v hv
  have htail := t1CS_loop_success_tail_exact r v hk
  calc TM.runConfig (M := T1M) (t1MutationConfig r 0 h0 b)
        (t1LoopSteps r.index + (8 * r.index + 8))
      = TM.runConfig (M := T1M)
          (TM.runConfig (M := T1M) (t1MutationConfig r 0 h0 b)
            (t1LoopSteps r.index)) (8 * r.index + 8) :=
        runConfig_add _ _ _
    _ = _ := by rw [hreach]; exact htail

/-- **Out of bounds with nonempty data, from the configuration the
installation reaches.**  When the data field is nonempty but shorter than the
index, the driver walks the cursor to the last slot `L-1` and T1b-B's
out-of-bounds step reaches the idle `oobStart` boundary, in exactly
`t1LoopSteps (L-1) + (16 * (L-1) + 32)` genuine steps.

The final tape is T1b-B's exact intermediate layout
`t1LoopFramesRestored r (L-1)`: the data field is fully restored and carries
no cursor frame, while the index field is **not** restored — it holds `L`
`spent` markers and `r.index - L` unconsumed `index` frames.  No repair is
claimed, and `oobStart` is an idle boundary, not a rejection. -/
theorem t1CS_loop_oob_from_zero_exact (r : T1Request) (b v : Bool)
    (hlen : r.data.length ≤ r.index) (hne : 0 < r.data.length)
    (hb : r.data[0]? = some b)
    (hv : r.data[r.data.length - 1]? = some v) :
    TM.runConfig (M := T1M) (t1MutationConfig r 0 hne b)
        (t1LoopSteps (r.data.length - 1) +
          (16 * (r.data.length - 1) + 32)) =
      t1AlignedConfig (encodeT1 r).length
        (4 * (r.index + (r.data.length - 1) + 3) + 3) (t1dOobHead_safe r)
        (t1ListTape
          ((t1LoopFramesRestored r (r.data.length - 1)).flatMap T1Frame.bits))
        .oobStart .p0 false false false v := by
  have hjd : r.data.length - 1 < r.data.length := by omega
  have hjk : r.data.length - 1 < r.index := by omega
  have hj1 : r.data.length - 1 + 1 = r.data.length := by omega
  have hreach := t1CS_loop_iterate_exact r b hne hb (r.data.length - 1)
    (by omega) hjd v hv
  have hoob := t1CS_loop_oob_exact r (r.data.length - 1) hjk hj1 v hv
  calc TM.runConfig (M := T1M) (t1MutationConfig r 0 hne b)
        (t1LoopSteps (r.data.length - 1) + (16 * (r.data.length - 1) + 32))
      = TM.runConfig (M := T1M)
          (TM.runConfig (M := T1M) (t1MutationConfig r 0 hne b)
            (t1LoopSteps (r.data.length - 1)))
          (16 * (r.data.length - 1) + 32) := runConfig_add _ _ _
    _ = _ := by rw [hreach]; exact hoob

/-! ## The decision clock, selected by `r.data[r.index]?` -/

/-- Mutation-phase cost when the selected slot exists: installation, the
loop driver, and the success tail. -/
def t1SuccessSteps (r : T1Request) : Nat :=
  4 * r.index + 17 + t1LoopSteps r.index + (8 * r.index + 8)

/-- Mutation-phase cost when the selected slot does not exist.  With no data
frames at all the first probe already finds the output frame; otherwise the
loop driver runs to the last slot and falls off there. -/
def t1OobSteps (r : T1Request) : Nat :=
  if r.data.length = 0 then 4 * r.index + 12
  else 4 * r.index + 17 + t1LoopSteps (r.data.length - 1) +
    (16 * (r.data.length - 1) + 32)

/-- **The mutation-phase clock, selected by the option `r.data[r.index]?`.**
This is the only place the terminal dichotomy is packaged as a single
`match`: the *configurations* are delivered as exact case theorems, because
each branch has its own head position, tape and latch. -/
def t1DecideSteps (r : T1Request) : Nat :=
  match r.data[r.index]? with
  | some _ => t1SuccessSteps r
  | none => t1OobSteps r

/-- The whole decision prefix: T1a validation and rewind, then the mutation
phase. -/
def t1DecideTotal (r : T1Request) : Nat :=
  2 * (encodeT1 r).length + 9 + t1DecideSteps r

theorem t1OobSteps_nil (r : T1Request) (h : r.data.length = 0) :
    t1OobSteps r = 4 * r.index + 12 := by
  unfold t1OobSteps
  rw [if_pos h]

theorem t1OobSteps_cons (r : T1Request) (h : r.data.length ≠ 0) :
    t1OobSteps r = 4 * r.index + 17 + t1LoopSteps (r.data.length - 1) +
      (16 * (r.data.length - 1) + 32) := by
  unfold t1OobSteps
  rw [if_neg h]

theorem t1DecideSteps_some (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) : t1DecideSteps r = t1SuccessSteps r := by
  unfold t1DecideSteps
  rw [hv]

theorem t1DecideSteps_none (r : T1Request) (hv : r.data[r.index]? = none) :
    t1DecideSteps r = t1OobSteps r := by
  unfold t1DecideSteps
  rw [hv]

/-- The selector is `none` exactly when the request is out of range. -/
theorem t1Selected_none_iff (r : T1Request) :
    r.data[r.index]? = none ↔ r.data.length ≤ r.index :=
  List.getElem?_eq_none_iff

/-! ## Exact `TM.runConfig` theorems from the real initial configuration -/

private theorem t1dValidateRewind (r : T1Request) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (2 * (encodeT1 r).length + 9) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation := by
  have hval := t1CS_validate_rewind_encoded_exact r
  simp only at hval
  exact hval

private theorem t1dCons_of_pos (r : T1Request) (h : 0 < r.data.length) :
    ∃ b rest, r.data = b :: rest := by
  cases hd : r.data with
  | nil => rw [hd] at h; simp at h
  | cons b rest => exact ⟨b, rest, rfl⟩

/-- **The exact success case, from the genuine initial configuration.**  When
`r.data[r.index]? = some v`, the machine reaches the idle `successStart`
boundary after exactly `t1DecideTotal r` genuine steps, with the latch
holding `v`, the head on cell `0`, and the tape the canonical layout
`t1LoopFrames r r.index` — cursor in data slot `r.index`, index field spent
to `spent^(r.index)`. -/
theorem t1CS_runConfig_decide_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1DecideTotal r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .successStart .p0 false false false v := by
  have hk : r.index < r.data.length := by
    by_contra hcon
    rw [t1Selected_none_iff r |>.mpr (by omega)] at hv
    exact Option.noConfusion hv
  obtain ⟨b, rest, hdata⟩ := t1dCons_of_pos r (by omega)
  have h0 : 0 < r.data.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hb : r.data[0]? = some b := by rw [hdata]; rfl
  have hsplit : t1DecideTotal r = (2 * (encodeT1 r).length + 9) +
      ((4 * r.index + 17) + (t1LoopSteps r.index + (8 * r.index + 8))) := by
    unfold t1DecideTotal
    rw [t1DecideSteps_some r v hv]
    unfold t1SuccessSteps
    omega
  have hzero : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation)
      (4 * r.index + 17) = t1MutationConfig r 0 h0 b :=
    t1CS_mutationConfig_zero r b rest hdata
  rw [hsplit, runConfig_add, t1dValidateRewind r, runConfig_add, hzero]
  exact t1CS_loop_success_from_zero_exact r b v hk hb hv

/-- **The exact out-of-bounds case with nonempty data, from the genuine
initial configuration.**  The step count is the same closed
`t1DecideTotal r`; the terminal boundary is `oobStart` on T1b-B's exact
intermediate tape, whose index field is spent and *not* repaired. -/
theorem t1CS_runConfig_decide_oob_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = none) (hne : 0 < r.data.length)
    (hlast : r.data[r.data.length - 1]? = some v) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1DecideTotal r) =
      t1AlignedConfig (encodeT1 r).length
        (4 * (r.index + (r.data.length - 1) + 3) + 3) (t1dOobHead_safe r)
        (t1ListTape
          ((t1LoopFramesRestored r (r.data.length - 1)).flatMap T1Frame.bits))
        .oobStart .p0 false false false v := by
  have hlen : r.data.length ≤ r.index := (t1Selected_none_iff r).1 hv
  obtain ⟨b, rest, hdata⟩ := t1dCons_of_pos r hne
  have hb : r.data[0]? = some b := by rw [hdata]; rfl
  have hsplit : t1DecideTotal r = (2 * (encodeT1 r).length + 9) +
      ((4 * r.index + 17) +
        (t1LoopSteps (r.data.length - 1) +
          (16 * (r.data.length - 1) + 32))) := by
    unfold t1DecideTotal
    rw [t1DecideSteps_none r hv, t1OobSteps_cons r (by omega)]
    omega
  have hzero : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation)
      (4 * r.index + 17) = t1MutationConfig r 0 hne b :=
    t1CS_mutationConfig_zero r b rest hdata
  rw [hsplit, runConfig_add, t1dValidateRewind r, runConfig_add, hzero]
  exact t1CS_loop_oob_from_zero_exact r b v hlen hne hb hlast

/-- **The exact empty-data out-of-bounds case, from the genuine initial
configuration**, at the same closed clock `t1DecideTotal r`.  With no data
frames the first probe already finds the observable output frame, so the
entire tape is still the input tape. -/
theorem t1CS_runConfig_decide_oob_empty_exact (r : T1Request)
    (hdata : r.data = []) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (t1DecideTotal r) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
        (t1dEmptyOobHead_safe r)
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
        false false false false := by
  have hlen : r.data.length = 0 := by rw [hdata]; rfl
  have hnone : r.data[r.index]? = none := (t1Selected_none_iff r).2 (by omega)
  have hsplit : t1DecideTotal r =
      (2 * (encodeT1 r).length + 9) + (4 * r.index + 12) := by
    unfold t1DecideTotal
    rw [t1DecideSteps_none r hnone, t1OobSteps_nil r hlen]
  rw [hsplit, runConfig_add, t1dValidateRewind r]
  exact t1CS_oob_empty_data_exact r hdata

/-! ## The decision prefix fits the public clock -/

private theorem t1dClockArith (N k j P Q R : Nat)
    (hk : k ≤ N) (hj : j ≤ N) (hP : P ≤ R) (hQ : Q ≤ R) :
    (2 * N + 9 + (4 * k + 17 + (8 * P + 29 * k) + (8 * k + 8)) ≤
        128 * R + 256 * N + 256) ∧
      (2 * N + 9 + (4 * k + 17 + (8 * Q + 29 * j) + (16 * j + 32)) ≤
        128 * R + 256 * N + 256) ∧
      (2 * N + 9 + (4 * k + 12) ≤ 128 * R + 256 * N + 256) :=
  ⟨by omega, by omega, by omega⟩

/-- **The whole decision prefix fits inside the public clock.**  Every branch
of `t1DecideSteps` — success, nonempty out-of-bounds, empty out-of-bounds —
plus the T1a validation and rewind prefix stays below
`t1Clock (encodeT1 r).length`, so the public `TM.run` has room for the same
split. -/
theorem t1CS_decideTotal_le_clock (r : T1Request) :
    t1DecideTotal r ≤ t1Clock (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hk : r.index ≤ (encodeT1 r).length := by omega
  have hj : r.data.length - 1 ≤ (encodeT1 r).length := by omega
  have hP : r.index * r.index ≤
      (encodeT1 r).length * (encodeT1 r).length := Nat.mul_le_mul hk hk
  have hQ : (r.data.length - 1) * (r.data.length - 1) ≤
      (encodeT1 r).length * (encodeT1 r).length := Nat.mul_le_mul hj hj
  have harith := t1dClockArith (encodeT1 r).length r.index (r.data.length - 1)
    (r.index * r.index) ((r.data.length - 1) * (r.data.length - 1))
    ((encodeT1 r).length * (encodeT1 r).length) hk hj hP hQ
  have hclock : t1Clock (encodeT1 r).length =
      128 * ((encodeT1 r).length * (encodeT1 r).length) +
        256 * (encodeT1 r).length + 256 := by
    simp only [t1Clock, t1dSqSucc]
    omega
  rw [hclock]
  unfold t1DecideTotal
  cases hsel : r.data[r.index]? with
  | some v =>
      rw [t1DecideSteps_some r v hsel]
      unfold t1SuccessSteps
      rw [t1LoopSteps_mul]
      exact harith.1
  | none =>
      rw [t1DecideSteps_none r hsel]
      by_cases hL : r.data.length = 0
      · rw [t1OobSteps_nil r hL]
        exact harith.2.2
      · rw [t1OobSteps_cons r hL, t1LoopSteps_mul]
        exact harith.2.1

/-! ## The same split under the genuine public clock -/

/-- **Success under the public clock.**  The decision prefix reaches the idle
`successStart` boundary, and the boundary is idle, so the machine's whole
`TM.run` *is* that configuration.  This is an execution theorem, not an
acceptance claim: `successStart` is a semantic boundary owned by T1c. -/
theorem t1CS_run_encoded_decide_success (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    T1M.run (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
        .successStart .p0 false false false v := by
  have hle := t1CS_decideTotal_le_clock r
  have hsplit : t1Clock (encodeT1 r).length =
      t1DecideTotal r + (t1Clock (encodeT1 r).length - t1DecideTotal r) := by
    omega
  rw [TM.run]
  change TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
      (t1Clock (encodeT1 r).length) = _
  rw [hsplit, runConfig_add, t1CS_runConfig_decide_success_exact r v hv]
  exact t1CS_runConfig_successStart _ _ _ _ v _

/-- **Nonempty out-of-bounds under the public clock.** -/
theorem t1CS_run_encoded_decide_oob_nonempty (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = none) (hne : 0 < r.data.length)
    (hlast : r.data[r.data.length - 1]? = some v) :
    T1M.run (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length
        (4 * (r.index + (r.data.length - 1) + 3) + 3) (t1dOobHead_safe r)
        (t1ListTape
          ((t1LoopFramesRestored r (r.data.length - 1)).flatMap T1Frame.bits))
        .oobStart .p0 false false false v := by
  have hle := t1CS_decideTotal_le_clock r
  have hsplit : t1Clock (encodeT1 r).length =
      t1DecideTotal r + (t1Clock (encodeT1 r).length - t1DecideTotal r) := by
    omega
  rw [TM.run]
  change TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
      (t1Clock (encodeT1 r).length) = _
  rw [hsplit, runConfig_add,
    t1CS_runConfig_decide_oob_exact r v hv hne hlast]
  exact t1CS_runConfig_oobStart _ _ _ _ v _

/-- **Empty-data out-of-bounds under the public clock.**  This is a direct
named alias of T1b-A's public-clock theorem, included so that the driver's
three public terminal cases have a uniform API. -/
theorem t1CS_run_encoded_decide_oob_empty (r : T1Request) (hdata : r.data = []) :
    T1M.run (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
        (t1dEmptyOobHead_safe r)
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
        false false false false :=
  t1CS_run_encoded_oob_empty_data r hdata

/-- **The public out-of-bounds dichotomy.**  When the selected slot does not
exist, the machine's whole `TM.run` is one of exactly two idle `oobStart`
configurations: the untouched input tape when there is no data at all, or
T1b-B's exact intermediate tape for the last data slot.  Neither disjunct
claims repair, output, or rejection. -/
theorem t1CS_run_encoded_decide_oob (r : T1Request)
    (hv : r.data[r.index]? = none) :
    (r.data = [] ∧ T1M.run (t1Point (encodeT1 r)) =
        t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
          (t1dEmptyOobHead_safe r)
          (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
          false false false false) ∨
      (∃ v, r.data[r.data.length - 1]? = some v ∧
        T1M.run (t1Point (encodeT1 r)) =
          t1AlignedConfig (encodeT1 r).length
            (4 * (r.index + (r.data.length - 1) + 3) + 3)
            (t1dOobHead_safe r)
            (t1ListTape
              ((t1LoopFramesRestored r (r.data.length - 1)).flatMap
                T1Frame.bits))
            .oobStart .p0 false false false v) := by
  by_cases hdata : r.data = []
  · exact Or.inl ⟨hdata, t1CS_run_encoded_decide_oob_empty r hdata⟩
  · have hne : 0 < r.data.length := by
      cases hd : r.data with
      | nil => exact absurd hd hdata
      | cons b rest => simp
    obtain ⟨v, hlast⟩ : ∃ v, r.data[r.data.length - 1]? = some v :=
      ⟨r.data[r.data.length - 1], List.getElem?_eq_getElem (by omega)⟩
    exact Or.inr ⟨v, hlast,
      t1CS_run_encoded_decide_oob_nonempty r v hv hne hlast⟩

end Pnp3.Internal.PsubsetPpoly.TM
