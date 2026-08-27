import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalControl
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriver

/-!
# T1c-2: terminal execution

T1c-1 activated the two terminal boundaries and proved one genuine
`TM.runConfig` macro step per new mode.  This module *chains* those macro
steps along the canonical tapes the T1b driver actually reaches, and closes
the terminal arms:

* the **success arm** runs from the exact `successStart` configuration
  produced by `t1CS_runConfig_decide_success_exact` to the literal
  `t1AcceptState` with the head back on cell `0`;
* the **out-of-bounds arms** (nonempty and empty data) run from the exact
  `oobStart` configurations produced by `t1CS_runConfig_decide_oob_exact` and
  `t1CS_runConfig_decide_oob_empty_exact` to the literal `t1RejectState`,
  again with the head on cell `0`.

Everything is exact: the step counts are closed arithmetic in `r.index` and
`r.data.length`, and the final tape is pinned as a concrete frame list, not
merely constrained.

## The canonical final tapes

```text
t1OutputFrames r v   = bof · index^k · separator · data(b₀…b_{L-1})
                            · output v · finish · blank
t1SpentFrames  r v   = bof · spent^k · separator · data(b₀…b_{L-1})
                            · output v · finish · blank
```

`t1OutputFrames r false` is the encoder layout plus the observable blank
frame, i.e. `t1ValidationFrames r`, whose tape is the initial tape
(`t1ListTape_validation_eq_initial`).  Hence:

* **success**: the final tape is `t1OutputFrames r v`, which is the initial
  tape with the single cell `t1OutputPosition r` overwritten by `v`
  (`t1CS_success_final_tape_eq`, `t1CS_success_final_tape_off`,
  `t1CS_success_final_tape_at`);
* **out of bounds**: the final tape is `t1ValidationFrames r`, i.e. *equal*
  to the initial tape (`t1CS_oob_final_tape_eq`), and the observable output
  frame still reads `output false`.

In both cases the index field is fully repaired: the final frame list
contains no `spent` marker at all and exactly `r.index` `index` markers
(`t1OutputFrames_count_spent`, `t1OutputFrames_count_index`).  The
intermediate `spent^k` layout `t1SpentFrames` is only ever a *midpoint* of
the terminal trace.

## Deliberately *not* claimed here

Nothing below executes `TM.runConfig` from `T1M.initialConfig` or composes with
the public clock `t1Clock`, and there is no acceptance `iff`.  Those are T1c-3.  The three
terminal theorems start from the *exact* boundary configurations the driver
produces, so T1c-3 is a `runConfig_add` splice plus a sink padding argument.

The machine is still the one fixed zero-parameter `t1CS`; the transition
table is never unfolded outside `TrueUniformSeek.lean`, and no runtime,
offset or advice is supplied by any caller.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Terminal frame vocabulary -/

/-- **The canonical success layout.**  The encoder layout with the observable
output frame carrying `v` instead of `false`, plus the observable blank
frame.  At `v = false` this is `t1ValidationFrames r`. -/
def t1OutputFrames (r : T1Request) (v : Bool) : List T1Frame :=
  [T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
    [T1Frame.separator] ++ r.data.map T1Frame.data ++
    [T1Frame.output v, T1Frame.finish, T1Frame.blank]

/-- **The midpoint layout of the success arm.**  Same as `t1OutputFrames`,
but the index field is still spent: this is what the tape looks like after
the cursor slot and the output frame have been written and before the shared
repair pass runs. -/
def t1SpentFrames (r : T1Request) (v : Bool) : List T1Frame :=
  [T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
    [T1Frame.separator] ++ r.data.map T1Frame.data ++
    [T1Frame.output v, T1Frame.finish, T1Frame.blank]

/-- The physical cell where the observable output frame starts. -/
def t1OutputBase (r : T1Request) : Nat := 4 * (r.index + r.data.length + 2)

theorem t1OutputPosition_eq (r : T1Request) :
    t1OutputPosition r = t1OutputBase r + 3 := rfl

/-- At `v = false` the success layout *is* the validation layout. -/
theorem t1OutputFrames_false (r : T1Request) :
    t1OutputFrames r false = t1ValidationFrames r := by
  simp [t1OutputFrames, t1ValidationFrames, encodeT1Frames, List.append_assoc]

@[simp] theorem t1OutputFrames_length (r : T1Request) (v : Bool) :
    (t1OutputFrames r v).length = r.index + r.data.length + 5 := by
  simp [t1OutputFrames]
  omega

/-! ### Physical safety facts

All heads visited by the terminal arms live inside the fixed tape, as an
unconditional consequence of the encoder length. -/

theorem t1tOutputBase_safe (r : T1Request) :
    t1OutputBase r + 4 < T1M.tapeLength (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  simp only [t1OutputBase]
  omega

/-- The observable output payload cell lies inside the fixed tape. -/
theorem t1OutputPosition_safe (r : T1Request) :
    t1OutputPosition r < T1M.tapeLength (encodeT1 r).length := by
  have h := t1tOutputBase_safe r
  rw [t1OutputPosition_eq]
  omega

theorem t1tOutputEntry_safe (r : T1Request) :
    t1OutputBase r - 1 < T1M.tapeLength (encodeT1 r).length := by
  have := t1tOutputBase_safe r
  omega

/-! ### Conservation of the index field

The two counting facts below are the exact restoration statement: the
terminal frame list carries **no** `spent` marker and exactly `r.index`
`index` markers, i.e. every unit consumed by the seek loop is put back. -/

private theorem t1tCount_data (f : T1Frame) (d : List Bool)
    (hf : ∀ v : Bool, f ≠ T1Frame.data v) :
    (d.map T1Frame.data).count f = 0 := by
  refine List.count_eq_zero.2 ?_
  intro hmem
  rcases List.mem_map.1 hmem with ⟨v, _, hv⟩
  exact hf v hv.symm

private theorem t1tCount_replicate_ne (f g : T1Frame) (m : Nat) (h : f ≠ g) :
    (List.replicate m g).count f = 0 :=
  List.count_eq_zero.2 (fun hmem => h (List.eq_of_mem_replicate hmem))

/-- **No index unit stays spent.** -/
theorem t1OutputFrames_count_spent (r : T1Request) (v : Bool) :
    (t1OutputFrames r v).count T1Frame.spent = 0 := by
  cases v <;>
    simp [t1OutputFrames, List.count_append,
      t1tCount_replicate_ne T1Frame.spent T1Frame.index r.index (by simp),
      t1tCount_data T1Frame.spent r.data (fun _ => by simp)]

/-- **Every index unit is restored**: exactly `r.index` of them, the number
the encoder produced. -/
theorem t1OutputFrames_count_index (r : T1Request) (v : Bool) :
    (t1OutputFrames r v).count T1Frame.index = r.index := by
  cases v <;>
    simp [t1OutputFrames, List.count_append,
      t1tCount_data T1Frame.index r.data (fun _ => by simp)]

/-! ### Pointwise conservation of the tape -/

private theorem t1tOutput_split (r : T1Request) (v : Bool) :
    t1OutputFrames r v =
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
        [T1Frame.separator] ++ r.data.map T1Frame.data) ++
        T1Frame.output v :: [T1Frame.finish, T1Frame.blank] := by
  simp [t1OutputFrames, List.append_assoc]

private theorem t1tOutput_pre_length (r : T1Request) :
    4 * (([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
      [T1Frame.separator] ++ r.data.map T1Frame.data).length) =
      t1OutputBase r := by
  simp [t1OutputBase]
  omega

/-- The three low cells of the observable output frame read `1 0 0` on the
initial tape; only the fourth carries the answer. -/
private theorem t1tWriteFrame_output {L : Nat} (base : Nat) (v : Bool)
    (tape : Fin L → Bool)
    (h0 : ∀ i : Fin L, (i : Nat) = base → tape i = true)
    (h1 : ∀ i : Fin L, (i : Nat) = base + 1 → tape i = false)
    (h2 : ∀ i : Fin L, (i : Nat) = base + 2 → tape i = false) :
    t1WriteFrame base (T1Frame.output v).bits tape =
      t1WriteCell (base + 3) v tape := by
  funext i
  by_cases hi3 : (i : Nat) = base + 3
  · cases v <;>
      simp [t1WriteFrame, t1WriteCell, T1Frame.bits, hi3, List.getD]
  · by_cases hin : base ≤ (i : Nat) ∧ (i : Nat) < base + 4
    · have hcase : (i : Nat) = base ∨ (i : Nat) = base + 1 ∨
          (i : Nat) = base + 2 := by omega
      rcases hcase with hc | hc | hc
      · cases v <;>
          simp [t1WriteFrame, t1WriteCell, T1Frame.bits, hc, List.getD, h0 i hc]
      · cases v <;>
          simp [t1WriteFrame, t1WriteCell, T1Frame.bits, hc, List.getD, h1 i hc]
      · cases v <;>
          simp [t1WriteFrame, t1WriteCell, T1Frame.bits, hc, List.getD, h2 i hc]
    · simp [t1WriteFrame, t1WriteCell, hin, hi3]

/-- **Pointwise conservation, success arm.**  The canonical success tape is
the *initial* tape with a single cell overwritten: cell
`t1OutputPosition r`, which now holds the selected data bit `v`. -/
theorem t1CS_success_final_tape_eq (r : T1Request) (v : Bool) :
    t1ListTape (n := (encodeT1 r).length)
        ((t1OutputFrames r v).flatMap T1Frame.bits) =
      t1WriteCell (t1OutputPosition r) v
        (T1M.initialConfig (t1Point (encodeT1 r))).tape := by
  have hpre := t1tOutput_pre_length r
  have hbase := t1tOutputBase_safe r
  have hwrite := t1ListTape_write_frame (n := (encodeT1 r).length)
    ([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
      [T1Frame.separator] ++ r.data.map T1Frame.data)
    [T1Frame.finish, T1Frame.blank] (T1Frame.output false) (T1Frame.output v)
  rw [hpre] at hwrite
  rw [← t1tOutput_split r v, ← t1tOutput_split r false,
    t1OutputFrames_false r, t1ListTape_validation_eq_initial r] at hwrite
  rw [hwrite, t1OutputPosition_eq]
  have hbits : t1PhysicalBitsAt (n := (encodeT1 r).length)
      (h := t1OutputBase r) hbase
      (T1M.initialConfig (t1Point (encodeT1 r))).tape =
      (T1Frame.output false).bits := by
    rw [← t1ListTape_validation_eq_initial r, ← t1OutputFrames_false r,
      t1tOutput_split r false]
    have hbf := t1PhysicalBitsAt_flatMap (encodeT1 r).length
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
        [T1Frame.separator] ++ r.data.map T1Frame.data)
      [T1Frame.finish, T1Frame.blank] (T1Frame.output false)
      (by rw [hpre]; exact hbase)
    simpa only [hpre] using hbf
  simp only [t1PhysicalBitsAt, T1Frame.bits, List.cons.injEq] at hbits
  obtain ⟨hb0, hb1, hb2, _⟩ := hbits
  refine t1tWriteFrame_output _ v _ ?_ ?_ ?_
  · intro i hi
    have hfin : i = (⟨t1OutputBase r, by omega⟩ : Fin _) := Fin.ext hi
    rw [hfin]; exact hb0
  · intro i hi
    have hfin : i = (⟨t1OutputBase r + 1, by omega⟩ : Fin _) := Fin.ext hi
    rw [hfin]; exact hb1
  · intro i hi
    have hfin : i = (⟨t1OutputBase r + 2, by omega⟩ : Fin _) := Fin.ext hi
    rw [hfin]; exact hb2

/-- Away from `t1OutputPosition r` the success tape is the input tape. -/
theorem t1CS_success_final_tape_off (r : T1Request) (v : Bool)
    (i : Fin (T1M.tapeLength (encodeT1 r).length))
    (hi : (i : Nat) ≠ t1OutputPosition r) :
    t1ListTape (n := (encodeT1 r).length)
        ((t1OutputFrames r v).flatMap T1Frame.bits) i =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape i := by
  rw [t1CS_success_final_tape_eq r v]
  simp [t1WriteCell, hi]

/-- At `t1OutputPosition r` the success tape holds the selected bit. -/
theorem t1CS_success_final_tape_at (r : T1Request) (v : Bool)
    (i : Fin (T1M.tapeLength (encodeT1 r).length))
    (hi : (i : Nat) = t1OutputPosition r) :
    t1ListTape (n := (encodeT1 r).length)
        ((t1OutputFrames r v).flatMap T1Frame.bits) i = v := by
  rw [t1CS_success_final_tape_eq r v]
  simp [t1WriteCell, hi]

/-- **Pointwise conservation, out-of-bounds arm.**  The rejecting arm leaves
the tape bit-for-bit equal to the input tape; in particular the observable
output frame still reads `output false`. -/
theorem t1CS_oob_final_tape_eq (r : T1Request) :
    t1ListTape (n := (encodeT1 r).length)
        ((t1OutputFrames r false).flatMap T1Frame.bits) =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape := by
  rw [t1OutputFrames_false r, t1ListTape_validation_eq_initial r]

/-! ## The shared repair pass -/

/-- **Backward multi-frame skip.**  `repairSeek` crosses a run of frames that
need no repair in exactly four genuine steps per frame, leaving the tape and
the latch untouched.  Structurally the mirror of `t1CS_scan_back_skip`. -/
theorem t1CS_repair_scan_skip (n : Nat) (pre skipped suffix : List T1Frame)
    (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, f = .index ∨ f = .separator ∨ f = .finish ∨
      (∃ v, f = .data v) ∨ ∃ v, f = .output v)
    (hsafe : 4 * (pre.length + skipped.length) < T1M.tapeLength n)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (pre.length + skipped.length) - 1) (by omega)
          (t1ListTape ((pre ++ skipped ++ suffix).flatMap T1Frame.bits))
          .repairSeek .p3 false false false latch)
        (4 * skipped.length) =
      t1AlignedConfig n (4 * pre.length - 1) (by omega)
        (t1ListTape ((pre ++ skipped ++ suffix).flatMap T1Frame.bits))
        .repairSeek .p3 false false false latch := by
  induction skipped generalizing pre with
  | nil => simp
  | cons f rest ih =>
      have hf : f = .index ∨ f = .separator ∨ f = .finish ∨
          (∃ v, f = .data v) ∨ ∃ v, f = .output v := hskip f (by simp)
      have hrest : ∀ g ∈ rest, g = .index ∨ g = .separator ∨ g = .finish ∨
          (∃ v, g = .data v) ∨ ∃ v, g = .output v :=
        fun g hg => hskip g (by simp [hg])
      have hlen : (pre ++ [f]).length = pre.length + 1 := by simp
      have hsafe' : 4 * ((pre ++ [f]).length + rest.length) <
          T1M.tapeLength n := by
        rw [hlen]
        simp only [List.length_cons] at hsafe
        omega
      have hbase : 4 * pre.length + 4 < T1M.tapeLength n := by
        simp only [List.length_cons] at hsafe
        omega
      have hIH := ih (pre ++ [f]) (by omega) hrest hsafe'
      simp only [hlen, show 4 * (pre.length + 1 + rest.length) - 1 =
          4 * (pre.length + (rest.length + 1)) - 1 from by omega,
        show 4 * (pre.length + 1) - 1 = 4 * pre.length + 3 from by omega,
        List.append_assoc, List.nil_append, List.cons_append] at hIH
      have hbits : t1PhysicalBitsAt hbase
          (t1ListTape (n := n)
            ((pre ++ f :: (rest ++ suffix)).flatMap T1Frame.bits)) = f.bits :=
        t1PhysicalBitsAt_flatMap n pre (rest ++ suffix) f hbase
      have hstep := t1CS_repairSeek_frame_skip n (4 * pre.length) (by omega)
        hbase
        (t1ListTape (n := n)
          ((pre ++ f :: (rest ++ suffix)).flatMap T1Frame.bits))
        latch f hf hbits
      rw [show 4 * (f :: rest).length = 4 * rest.length + 4 by simp; omega,
        runConfig_add]
      simp only [List.length_cons, List.append_assoc, List.cons_append]
      rw [hIH, hstep]

/-- **One repair cycle.**  Thirteen genuine steps turn a single `spent`
marker back into an `index` frame and return to the repair scan's entry shape
one frame to the left: `4` to scan the marker, `4` to rewrite it, `4` to walk
back, `1` to hop off. -/
theorem t1CS_repair_cycle (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = T1Frame.spent.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base + 3) (by omega) tape .repairSeek .p3
          false false false latch) 13 =
      t1AlignedConfig n (base - 1) (by omega)
        (t1WriteFrame base T1Frame.index.bits tape) .repairSeek .p3
        false false false latch := by
  have hA := t1CS_repairSeek_frame_write n base hsafe tape latch hbits
  have hB := t1CS_repairWrite_frame n base hsafe tape latch
  have hC := t1CS_repairBack_walk n base hsafe
    (t1WriteFrame base T1Frame.index.bits tape) latch
  have hD := t1CS_repairHop_step n base hpos (by omega)
    (t1WriteFrame base T1Frame.index.bits tape) latch
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base + 3) (by omega) tape .repairSeek .p3
        false false false latch) (4 + 4 + 4 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add, hA, hB, hC, hD]

/-- **The repair induction.**  A whole run of `s` `spent` markers is turned
back into `s` `index` frames in exactly `13 * s` genuine steps, the head
ending on the last cell of the frame preceding the run.  Nothing outside the
run is touched. -/
theorem t1CS_repair_spent_run (n : Nat) (pre suffix : List T1Frame) (s : Nat)
    (hpre : 0 < pre.length)
    (hsafe : 4 * (pre.length + s) < T1M.tapeLength n) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (pre.length + s) - 1) (by omega)
          (t1ListTape ((pre ++ List.replicate s T1Frame.spent ++
            suffix).flatMap T1Frame.bits))
          .repairSeek .p3 false false false latch)
        (13 * s) =
      t1AlignedConfig n (4 * pre.length - 1) (by omega)
        (t1ListTape ((pre ++ List.replicate s T1Frame.index ++
          suffix).flatMap T1Frame.bits))
        .repairSeek .p3 false false false latch := by
  induction s generalizing pre with
  | zero => simp
  | succ s ih =>
      have hlen : (pre ++ [T1Frame.spent]).length = pre.length + 1 := by simp
      have hsafe' : 4 * ((pre ++ [T1Frame.spent]).length + s) <
          T1M.tapeLength n := by
        rw [hlen]; omega
      have hbase : 4 * pre.length + 4 < T1M.tapeLength n := by omega
      have hIH := ih (pre ++ [T1Frame.spent]) (by omega) hsafe'
      simp only [hlen,
        show 4 * (pre.length + 1 + s) - 1 = 4 * (pre.length + (s + 1)) - 1
          from by omega,
        show 4 * (pre.length + 1) - 1 = 4 * pre.length + 3 from by omega,
        List.append_assoc, List.cons_append, List.nil_append] at hIH
      have hbits : t1PhysicalBitsAt hbase
          (t1ListTape (n := n) ((pre ++ T1Frame.spent ::
            (List.replicate s T1Frame.index ++ suffix)).flatMap
            T1Frame.bits)) = T1Frame.spent.bits :=
        t1PhysicalBitsAt_flatMap n pre _ T1Frame.spent hbase
      have hcycle := t1CS_repair_cycle n (4 * pre.length) (by omega) hbase
        (t1ListTape (n := n) ((pre ++ T1Frame.spent ::
          (List.replicate s T1Frame.index ++ suffix)).flatMap T1Frame.bits))
        latch hbits
      have hframe := t1ListTape_write_frame (n := n) pre
        (List.replicate s T1Frame.index ++ suffix) T1Frame.spent T1Frame.index
      rw [← hframe] at hcycle
      rw [show 13 * (s + 1) = 13 * s + 13 from by omega, runConfig_add]
      simp only [List.replicate_succ, List.append_assoc, List.cons_append]
        at hIH hcycle ⊢
      rw [hIH, hcycle]

/-- **The generic cost of one repair pass.**  `m` skipped frames, `s` markers
repaired, `a` untouched index units, plus the `bof` read and the final
dispatch. -/
def t1RepairSteps (a s m : Nat) : Nat := 4 * m + 13 * s + 4 * a + 5

/-- **The shared repair pass, end to end.**  From the repair scan's entry
shape on the last cell of the rightmost frame that needs visiting, the
machine skips `mid`, repairs the whole `spent` run, skips the untouched index
units, reads the `bof` anchor and dispatches — landing *literally* in
`t1AcceptState` or `t1RejectState` (every scratch bit and the latch cleared)
with the head on cell `0`.

The tape statement is exact: the only change is `spent^s ↦ index^s`, so the
index field ends with `a + s` `index` frames and no `spent` marker, while
`mid` and `tail` are bit-for-bit preserved. -/
theorem t1CS_repair_pass_exact (n a s : Nat) (mid tail : List T1Frame)
    (hmid : ∀ f ∈ mid, f = .index ∨ f = .separator ∨ f = .finish ∨
      (∃ v, f = .data v) ∨ ∃ v, f = .output v)
    (hsafe : 4 * (1 + a + s + mid.length) < T1M.tapeLength n)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (1 + a + s + mid.length) - 1) (by omega)
          (t1ListTape (([T1Frame.bof] ++ List.replicate a T1Frame.index ++
            List.replicate s T1Frame.spent ++ mid ++ tail).flatMap
            T1Frame.bits))
          .repairSeek .p3 false false false latch)
        (t1RepairSteps a s mid.length) =
      t1AlignedConfig n 0 (by omega)
        (t1ListTape (([T1Frame.bof] ++ List.replicate (a + s) T1Frame.index ++
          mid ++ tail).flatMap T1Frame.bits))
        (bif latch then T1Mode.accept else T1Mode.reject) .p0
        false false false false := by
  have hlenA : ([T1Frame.bof] ++ List.replicate a T1Frame.index ++
      List.replicate s T1Frame.spent).length = 1 + a + s := by
    simp only [List.length_append, List.length_replicate,
      List.length_singleton]
  have hlenB : ([T1Frame.bof] ++ List.replicate a T1Frame.index).length =
      1 + a := by
    simp only [List.length_append, List.length_replicate,
      List.length_singleton]
  have hlenC : ([T1Frame.bof] : List T1Frame).length = 1 := rfl
  have hrepl : List.replicate (a + s) T1Frame.index =
      List.replicate a T1Frame.index ++ List.replicate s T1Frame.index :=
    List.replicate_add a s _
  -- Phase A: skip `mid`, right to left.
  have hA := t1CS_repair_scan_skip n
    ([T1Frame.bof] ++ List.replicate a T1Frame.index ++
      List.replicate s T1Frame.spent) mid tail (by simp) hmid
    (by simp only [hlenA]; exact hsafe) latch
  simp only [hlenA] at hA
  -- Phase B: repair the whole `spent` run.
  have hB := t1CS_repair_spent_run n
    ([T1Frame.bof] ++ List.replicate a T1Frame.index) (mid ++ tail) s
    (by simp) (by simp only [hlenB]; omega) latch
  simp only [hlenB] at hB
  -- Phase C: skip the untouched index units.
  have hC := t1CS_repair_scan_skip n [T1Frame.bof]
    (List.replicate a T1Frame.index)
    (List.replicate s T1Frame.index ++ mid ++ tail) (by simp)
    (fun f hf => Or.inl (List.eq_of_mem_replicate hf))
    (by simp only [hlenC, List.length_replicate]; omega) latch
  simp only [hlenC, List.length_replicate,
    show 4 * 1 - 1 = 3 from rfl] at hC
  -- Phase D: the `bof` anchor ends the pass.
  have hbofSafe : (0 : Nat) + 4 < T1M.tapeLength n := by omega
  have hbits : t1PhysicalBitsAt hbofSafe
      (t1ListTape (n := n) (([T1Frame.bof] ++
        List.replicate a T1Frame.index ++ List.replicate s T1Frame.index ++
        mid ++ tail).flatMap T1Frame.bits)) = T1Frame.bof.bits := by
    have hbf := t1PhysicalBitsAt_flatMap n []
      (List.replicate a T1Frame.index ++ List.replicate s T1Frame.index ++
        mid ++ tail) T1Frame.bof (by simpa using hbofSafe)
    simpa [List.append_assoc] using hbf
  have hD := t1CS_repairSeek_frame_done n 0 hbofSafe
    (t1ListTape (n := n) (([T1Frame.bof] ++
      List.replicate a T1Frame.index ++ List.replicate s T1Frame.index ++
      mid ++ tail).flatMap T1Frame.bits)) latch hbits
  simp only [Nat.zero_add] at hD
  -- assemble
  have hsplit : t1RepairSteps a s mid.length =
      4 * mid.length + (13 * s + (4 * a + (4 + 1))) := by
    simp only [t1RepairSteps]; omega
  rw [hsplit, runConfig_add, runConfig_add, runConfig_add, runConfig_add]
  simp only [hrepl, List.append_assoc] at hA hB hC hD ⊢
  rw [hA, hB, hC, hD]
  cases latch with
  | false => simpa using t1CS_repairDone_reject n 0 (by omega) _
  | true => simpa using t1CS_repairDone_accept n 0 (by omega) _

/-! ## The success arm

The output phase reuses T1a's forward macro-scan `t1CS_scan_frames`, so two
grammar-path lemmas per new forward mode are all that is needed. -/

private theorem t1tAdvanceList_append : ∀ (xs : List T1Frame) (mode : T1Mode)
    (ys : List T1Frame),
    t1AdvanceList mode (xs ++ ys) = t1AdvanceList (t1AdvanceList mode xs) ys := by
  intro xs
  induction xs with
  | nil => intro mode ys; rfl
  | cons f rest ih => intro mode ys; simpa [t1AdvanceList] using ih _ ys

private theorem t1tPath_append : ∀ (xs : List T1Frame) (mode : T1Mode)
    (ys : List T1Frame), T1ValidPath mode xs →
    T1ValidPath (t1AdvanceList mode xs) ys → T1ValidPath mode (xs ++ ys) := by
  intro xs
  induction xs with
  | nil => intro mode ys _ hy; simpa [t1AdvanceList] using hy
  | cons f rest ih =>
      intro mode ys hx hy
      rcases hx with ⟨hfwd, hnext, hrest⟩
      exact ⟨hfwd, hnext, ih _ ys hrest (by simpa [t1AdvanceList] using hy)⟩

private theorem t1tSeekCursor_path : ∀ (frames : List T1Frame),
    (∀ f ∈ frames, f = .spent ∨ f = .separator ∨ ∃ v, f = .data v) →
    T1ValidPath .outSeekCursor frames := by
  intro frames
  induction frames with
  | nil => intro _; trivial
  | cons f rest ih =>
      intro hall
      have hf : f = .spent ∨ f = .separator ∨ ∃ v, f = .data v :=
        hall f (by simp)
      have hstep : t1Advance .outSeekCursor f = .outSeekCursor := by
        rcases hf with rfl | rfl | ⟨w, rfl⟩ <;> rfl
      refine ⟨T1ForwardMode.outSeekCursor, ?_, ?_⟩
      · rw [hstep]; exact fun h => T1Mode.noConfusion h
      · rw [hstep]; exact ih (fun g hg => hall g (by simp [hg]))

private theorem t1tSeekCursor_advance : ∀ (frames : List T1Frame),
    (∀ f ∈ frames, f = .spent ∨ f = .separator ∨ ∃ v, f = .data v) →
    t1AdvanceList .outSeekCursor frames = .outSeekCursor := by
  intro frames
  induction frames with
  | nil => intro _; rfl
  | cons f rest ih =>
      intro hall
      have hf : f = .spent ∨ f = .separator ∨ ∃ v, f = .data v :=
        hall f (by simp)
      have hstep : t1Advance .outSeekCursor f = .outSeekCursor := by
        rcases hf with rfl | rfl | ⟨w, rfl⟩ <;> rfl
      simp only [t1AdvanceList, hstep]
      exact ih (fun g hg => hall g (by simp [hg]))

private theorem t1tSeekOutput_path : ∀ (frames : List T1Frame),
    (∀ f ∈ frames, ∃ v, f = .data v) → T1ValidPath .outSeekOutput frames := by
  intro frames
  induction frames with
  | nil => intro _; trivial
  | cons f rest ih =>
      intro hall
      obtain ⟨w, rfl⟩ := hall f (by simp)
      exact ⟨T1ForwardMode.outSeekOutput, fun h => T1Mode.noConfusion h,
        ih (fun g hg => hall g (by simp [hg]))⟩

private theorem t1tSeekOutput_advance : ∀ (frames : List T1Frame),
    (∀ f ∈ frames, ∃ v, f = .data v) →
    t1AdvanceList .outSeekOutput frames = .outSeekOutput := by
  intro frames
  induction frames with
  | nil => intro _; rfl
  | cons f rest ih =>
      intro hall
      obtain ⟨w, rfl⟩ := hall f (by simp)
      simp only [t1AdvanceList]
      exact ih (fun g hg => hall g (by simp [hg]))

private theorem t1tMap_data_mem (d : List Bool) :
    ∀ f ∈ d.map T1Frame.data, ∃ v, f = T1Frame.data v := by
  intro f hf
  rcases List.mem_map.1 hf with ⟨v, _, rfl⟩
  exact ⟨v, rfl⟩

private theorem t1tSkip_mem (j : Nat) (d : List Bool) :
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

/-- Splicing the restored slot back into the data field. -/
private theorem t1tMap_data_split (d : List Bool) (k : Nat) (v : Bool)
    (hv : d[k]? = some v) :
    (d.take k).map T1Frame.data ++ T1Frame.data v ::
        (d.drop (k+1)).map T1Frame.data =
      d.map T1Frame.data := by
  have hk : k < d.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hv
    exact Option.noConfusion hv
  have hget : d[k] = v := by
    have hsome := List.getElem?_eq_getElem hk
    rw [hsome] at hv
    exact Option.some.inj hv
  have hdrop : d.drop k = v :: d.drop (k+1) := by
    rw [List.drop_eq_getElem_cons hk, hget]
  calc (d.take k).map T1Frame.data ++ T1Frame.data v ::
          (d.drop (k+1)).map T1Frame.data
      = (d.take k).map T1Frame.data ++ (v :: d.drop (k+1)).map T1Frame.data :=
        rfl
    _ = (d.take k).map T1Frame.data ++ (d.drop k).map T1Frame.data := by
        rw [hdrop]
    _ = (d.take k ++ d.drop k).map T1Frame.data := (List.map_append ..).symm
    _ = d.map T1Frame.data := by rw [List.take_append_drop]

/-! ### The success layout, split three ways -/

private theorem t1tLoop_split (r : T1Request) :
    t1LoopFrames r r.index =
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
        [T1Frame.separator] ++ (r.data.take r.index).map T1Frame.data) ++
        T1Frame.cursor :: ((r.data.drop (r.index+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  simp [t1LoopFrames, t1MutationFrames, List.append_assoc]

private theorem t1tSpent_split_cursor (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    t1SpentFrames r false =
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
        [T1Frame.separator] ++ (r.data.take r.index).map T1Frame.data) ++
        T1Frame.data v :: ((r.data.drop (r.index+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  have hmap := t1tMap_data_split r.data r.index v hv
  simp only [t1SpentFrames]
  rw [← hmap]
  simp [List.append_assoc]

private theorem t1tSpent_split_scan (r : T1Request) (w : Bool) :
    t1SpentFrames r w =
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
        [T1Frame.separator] ++
        (r.data.take (r.index+1)).map T1Frame.data) ++
        (r.data.drop (r.index+1)).map T1Frame.data ++
        [T1Frame.output w, T1Frame.finish, T1Frame.blank] := by
  have hmap : (r.data.take (r.index+1)).map T1Frame.data ++
      (r.data.drop (r.index+1)).map T1Frame.data = r.data.map T1Frame.data := by
    rw [← List.map_append, List.take_append_drop]
  simp only [t1SpentFrames]
  rw [← hmap]
  simp [List.append_assoc]

private theorem t1tSpent_split_output (r : T1Request) (w : Bool) :
    t1SpentFrames r w =
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
        [T1Frame.separator] ++ r.data.map T1Frame.data) ++
        T1Frame.output w :: [T1Frame.finish, T1Frame.blank] := by
  simp [t1SpentFrames, List.append_assoc]

/-- Cost of the success arm's output phase: the `successStart` dispatch, the
walk off the anchor, the forward cursor search (including the cursor frame
itself), the cursor restore, the forward output search (including the output
frame), the turn and the output write. -/
def t1OutputSteps (r : T1Request) : Nat :=
  4 * r.index + 4 * r.data.length + 26

/-- **The output phase of the success arm.**  From the exact `successStart`
configuration the driver reaches, the machine restores the cursor slot to the
latched data value, walks to the observable output frame and writes
`output v` into it, in exactly `t1OutputSteps r` genuine steps.

The head is left on the last cell of the frame preceding the output frame,
in the repair scan's entry shape, with the latch set to the accept tag.  The
tape is the exact midpoint layout `t1SpentFrames r v`: data field fully
restored (slot `r.index` reads `v` again), output frame carrying `v`, index
field still spent. -/
theorem t1CS_output_write_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length 0
          (t1_lt_tapeLength _ _ (Nat.zero_le _))
          (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
          .successStart .p0 false false false v)
        (t1OutputSteps r) =
      t1AlignedConfig (encodeT1 r).length (t1OutputBase r - 1)
        (t1tOutputEntry_safe r)
        (t1ListTape ((t1SpentFrames r v).flatMap T1Frame.bits))
        .repairSeek .p3 false false false true := by
  have hkL : r.index < r.data.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hv
    exact Option.noConfusion hv
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  have hobase : t1OutputBase r = 4 * (r.index + r.data.length + 2) := rfl
  -- lengths of the two forward scans
  have htake : ((r.data.take r.index).map T1Frame.data).length = r.index := by
    simp; omega
  have htake1 :
      ((r.data.take (r.index+1)).map T1Frame.data).length = r.index + 1 := by
    simp; omega
  have hdrop : ((r.data.drop (r.index+1)).map T1Frame.data).length =
      r.data.length - (r.index + 1) := by simp
  have hcursorRun : (List.replicate r.index T1Frame.spent ++
      [T1Frame.separator] ++ (r.data.take r.index).map T1Frame.data ++
      [T1Frame.cursor]).length = 2 * r.index + 2 := by
    simp only [List.length_append, List.length_replicate,
      List.length_singleton, htake]
    omega
  have houtRun : ((r.data.drop (r.index+1)).map T1Frame.data ++
      [T1Frame.output false]).length = r.data.length - r.index := by
    simp only [List.length_append, List.length_singleton, hdrop]
    omega
  -- the boundary tape
  set T0 : Fin (T1M.tapeLength (encodeT1 r).length) → Bool :=
    t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits) with hT0
  -- Step 1: the boundary fires; Step 2: walk off the anchor.
  have h1 := t1CS_successStart_dispatch (encodeT1 r).length 0
    (t1_lt_tapeLength _ _ (Nat.zero_le _)) T0 v
  have h2 := t1CS_outWalk_walk (encodeT1 r).length 0 (by omega) T0 v
  -- Step 3: the forward cursor search, including the cursor frame.
  have hpath3 : T1ValidPath .outSeekCursor
      (List.replicate r.index T1Frame.spent ++ [T1Frame.separator] ++
        (r.data.take r.index).map T1Frame.data ++ [T1Frame.cursor]) := by
    refine t1tPath_append _ _ _
      (t1tSeekCursor_path _ (t1tSkip_mem r.index r.data)) ?_
    rw [t1tSeekCursor_advance _ (t1tSkip_mem r.index r.data)]
    exact ⟨T1ForwardMode.outSeekCursor, fun h => T1Mode.noConfusion h, trivial⟩
  have hadv3 : t1AdvanceList .outSeekCursor
      (List.replicate r.index T1Frame.spent ++ [T1Frame.separator] ++
        (r.data.take r.index).map T1Frame.data ++ [T1Frame.cursor]) =
      .outBackup := by
    rw [t1tAdvanceList_append,
      t1tSeekCursor_advance _ (t1tSkip_mem r.index r.data)]
    rfl
  have h3 := t1CS_scan_frames (encodeT1 r).length [T1Frame.bof]
    (List.replicate r.index T1Frame.spent ++ [T1Frame.separator] ++
      (r.data.take r.index).map T1Frame.data ++ [T1Frame.cursor])
    ((r.data.drop (r.index+1)).map T1Frame.data ++
      [T1Frame.output false, T1Frame.finish, T1Frame.blank])
    .outSeekCursor hpath3
    (by simp only [List.length_singleton, hcursorRun]; omega) v
  rw [hadv3] at h3
  simp only [List.length_singleton, hcursorRun,
    show 4 * 1 = 4 from rfl,
    show 4 * (1 + (2 * r.index + 2)) = 4 * (2 * r.index + 2) + 4 from by omega]
    at h3
  have h3tape : ([T1Frame.bof] ++
      (List.replicate r.index T1Frame.spent ++ [T1Frame.separator] ++
        (r.data.take r.index).map T1Frame.data ++ [T1Frame.cursor]) ++
      ((r.data.drop (r.index+1)).map T1Frame.data ++
        [T1Frame.output false, T1Frame.finish, T1Frame.blank])) =
      t1LoopFrames r r.index := by
    rw [t1tLoop_split r]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [h3tape, ← hT0] at h3
  -- Step 4: back onto the cursor frame; Step 5: restore the data frame.
  have hcurSafe : 4 * (2 * r.index + 2) + 4 <
      T1M.tapeLength (encodeT1 r).length := by omega
  have h4 := t1CS_outBackup_walk (encodeT1 r).length (4 * (2 * r.index + 2))
    hcurSafe T0 v
  have h5 := t1CS_outWriteData_frame (encodeT1 r).length
    (4 * (2 * r.index + 2)) hcurSafe T0 v
  -- identify the restored tape
  have hT1 : t1WriteFrame (4 * (2 * r.index + 2)) (T1Frame.data v).bits T0 =
      t1ListTape ((t1SpentFrames r false).flatMap T1Frame.bits) := by
    have hw := t1ListTape_write_frame (n := (encodeT1 r).length)
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
        [T1Frame.separator] ++ (r.data.take r.index).map T1Frame.data)
      ((r.data.drop (r.index+1)).map T1Frame.data ++
        [T1Frame.output false, T1Frame.finish, T1Frame.blank])
      T1Frame.cursor (T1Frame.data v)
    simp only [List.length_append, List.length_replicate,
      List.length_singleton, htake,
      show 1 + r.index + 1 + r.index = 2 * r.index + 2 from by omega] at hw
    rw [← t1tLoop_split r, ← t1tSpent_split_cursor r v hv] at hw
    exact hw.symm
  rw [hT1] at h5
  set T1 : Fin (T1M.tapeLength (encodeT1 r).length) → Bool :=
    t1ListTape ((t1SpentFrames r false).flatMap T1Frame.bits) with hT1def
  -- Step 6: the forward output search, including the output frame.
  have hpath6 : T1ValidPath .outSeekOutput
      ((r.data.drop (r.index+1)).map T1Frame.data ++
        [T1Frame.output false]) := by
    refine t1tPath_append _ _ _
      (t1tSeekOutput_path _ (t1tMap_data_mem _)) ?_
    rw [t1tSeekOutput_advance _ (t1tMap_data_mem _)]
    exact ⟨T1ForwardMode.outSeekOutput, fun h => T1Mode.noConfusion h, trivial⟩
  have hadv6 : t1AdvanceList .outSeekOutput
      ((r.data.drop (r.index+1)).map T1Frame.data ++
        [T1Frame.output false]) = .outTurn := by
    rw [t1tAdvanceList_append, t1tSeekOutput_advance _ (t1tMap_data_mem _)]
    rfl
  have hpre6 : ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
      [T1Frame.separator] ++
      (r.data.take (r.index+1)).map T1Frame.data).length =
      2 * r.index + 3 := by
    simp only [List.length_append, List.length_replicate,
      List.length_singleton, htake1]
    omega
  have h6 := t1CS_scan_frames (encodeT1 r).length
    ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
      [T1Frame.separator] ++ (r.data.take (r.index+1)).map T1Frame.data)
    ((r.data.drop (r.index+1)).map T1Frame.data ++ [T1Frame.output false])
    [T1Frame.finish, T1Frame.blank] .outSeekOutput hpath6
    (by simp only [hpre6, houtRun]; omega) v
  rw [hadv6] at h6
  simp only [hpre6, houtRun,
    show 4 * (2 * r.index + 3 + (r.data.length - r.index)) =
      t1OutputBase r + 4 from by simp only [hobase]; omega] at h6
  have h6tape : ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
      [T1Frame.separator] ++ (r.data.take (r.index+1)).map T1Frame.data) ++
      ((r.data.drop (r.index+1)).map T1Frame.data ++
        [T1Frame.output false]) ++ [T1Frame.finish, T1Frame.blank] =
      t1SpentFrames r false := by
    rw [t1tSpent_split_scan r false]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [h6tape, ← hT1def] at h6
  -- Step 7: turn around; Step 8: write the output frame.
  have h7 := t1CS_outTurn_step (encodeT1 r).length (t1OutputBase r + 4)
    (by simp only [hobase]; omega) (by have := t1tOutputBase_safe r; omega)
    T1 v
  simp only [show t1OutputBase r + 4 - 1 = t1OutputBase r + 3 from by
    simp only [hobase]; omega] at h7
  have h8 := t1CS_outWriteOut_frame (encodeT1 r).length (t1OutputBase r)
    (by simp only [hobase]; omega) (t1tOutputBase_safe r) T1 v
  have hT2 : t1WriteFrame (t1OutputBase r) (T1Frame.output v).bits T1 =
      t1ListTape ((t1SpentFrames r v).flatMap T1Frame.bits) := by
    have hw := t1ListTape_write_frame (n := (encodeT1 r).length)
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.spent ++
        [T1Frame.separator] ++ r.data.map T1Frame.data)
      [T1Frame.finish, T1Frame.blank] (T1Frame.output false)
      (T1Frame.output v)
    simp only [List.length_append, List.length_replicate,
      List.length_singleton, List.length_map,
      show 1 + r.index + 1 + r.data.length =
        r.index + r.data.length + 2 from by omega] at hw
    rw [← t1tSpent_split_output r false, ← t1tSpent_split_output r v] at hw
    rw [← hT1def, ← hobase] at hw
    exact hw.symm
  rw [hT2] at h8
  -- assemble the eight phases
  have hsteps : t1OutputSteps r =
      1 + (4 + (4 * (2 * r.index + 2) + (4 + (4 +
        (4 * (r.data.length - r.index) + (1 + 4)))))) := by
    simp only [t1OutputSteps]
    omega
  rw [hsteps, runConfig_add, runConfig_add, runConfig_add, runConfig_add,
    runConfig_add, runConfig_add, runConfig_add]
  rw [h1, h2]
  simp only [Nat.zero_add] at h3 ⊢
  rw [h3, h4, h5]
  simp only [show 4 * (2 * r.index + 2) + 4 = 4 * (2 * r.index + 3) from by
    omega]
  rw [h6, h7, h8]

/-! ## The three terminal theorems -/

/-- Cost of the success arm: output phase plus the repair pass over the
`r.index` spent markers, `r.data.length + 1` frames skipped on the way. -/
def t1SuccessTerminalSteps (r : T1Request) : Nat :=
  17 * r.index + 8 * r.data.length + 35

/-- Cost of both out-of-bounds arms: the `oobStart` dispatch plus the repair
pass.  At `r.data = []` the second summand vanishes and the formula
degenerates to `4 * r.index + 14`. -/
def t1OobTerminalSteps (r : T1Request) : Nat :=
  4 * r.index + 13 * r.data.length + 14

/-- The terminal cost, selected by `r.data[r.index]?`, exactly as
`t1DecideSteps` selects the decision cost. -/
def t1TerminalSteps (r : T1Request) : Nat :=
  match r.data[r.index]? with
  | some _ => t1SuccessTerminalSteps r
  | none => t1OobTerminalSteps r

theorem t1TerminalSteps_some (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    t1TerminalSteps r = t1SuccessTerminalSteps r := by
  unfold t1TerminalSteps; rw [hv]

theorem t1TerminalSteps_none (r : T1Request) (hv : r.data[r.index]? = none) :
    t1TerminalSteps r = t1OobTerminalSteps r := by
  unfold t1TerminalSteps; rw [hv]

/-- **The success terminal theorem.**  From the *exact* `successStart`
configuration produced by `t1CS_runConfig_decide_success_exact`, the machine
reaches the literal accept state — `t1CS.acceptState`, every scratch bit and
the latch cleared — with the head on cell `0`, in exactly
`t1SuccessTerminalSteps r` genuine steps.

The final tape is `t1OutputFrames r v`: the input tape with the single cell
`t1OutputPosition r` overwritten by the selected bit `v`
(`t1CS_success_final_tape_eq`), the cursor slot restored to `data v`, and the
index field repaired to `index^(r.index)` with no `spent` marker left
(`t1OutputFrames_count_spent`, `t1OutputFrames_count_index`). -/
theorem t1CS_terminal_success_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = some v) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length 0
          (t1_lt_tapeLength _ _ (Nat.zero_le _))
          (t1ListTape ((t1LoopFrames r r.index).flatMap T1Frame.bits))
          .successStart .p0 false false false v)
        (t1SuccessTerminalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r v).flatMap T1Frame.bits))
        .accept .p0 false false false false := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  have hout := t1CS_output_write_exact r v hv
  have hmidLen : ([T1Frame.separator] ++ r.data.map T1Frame.data).length =
      r.data.length + 1 := by
    simp only [List.length_append, List.length_singleton, List.length_map]
    omega
  have hmid : ∀ f ∈ ([T1Frame.separator] ++ r.data.map T1Frame.data),
      f = .index ∨ f = .separator ∨ f = .finish ∨
        (∃ w, f = .data w) ∨ ∃ w, f = .output w := by
    intro f hf
    rcases List.mem_append.1 hf with h | h
    · exact Or.inr (Or.inl (by simpa using h))
    · rcases List.mem_map.1 h with ⟨w, _, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, rfl⟩)))
  have hrep := t1CS_repair_pass_exact (encodeT1 r).length 0 r.index
    ([T1Frame.separator] ++ r.data.map T1Frame.data)
    [T1Frame.output v, T1Frame.finish, T1Frame.blank] hmid
    (by simp only [hmidLen]; omega) true
  have hstart : ([T1Frame.bof] ++ List.replicate 0 T1Frame.index ++
      List.replicate r.index T1Frame.spent ++
      ([T1Frame.separator] ++ r.data.map T1Frame.data) ++
      [T1Frame.output v, T1Frame.finish, T1Frame.blank]) =
      t1SpentFrames r v := by
    simp [t1SpentFrames, List.append_assoc]
  have hend : ([T1Frame.bof] ++ List.replicate (0 + r.index) T1Frame.index ++
      ([T1Frame.separator] ++ r.data.map T1Frame.data) ++
      [T1Frame.output v, T1Frame.finish, T1Frame.blank]) =
      t1OutputFrames r v := by
    simp [t1OutputFrames, List.append_assoc]
  simp only [hmidLen, hstart, hend,
    show 4 * (1 + 0 + r.index + (r.data.length + 1)) - 1 =
      t1OutputBase r - 1 from by simp only [t1OutputBase]; omega,
    cond_true] at hrep
  have hsplit : t1SuccessTerminalSteps r =
      t1OutputSteps r + t1RepairSteps 0 r.index (r.data.length + 1) := by
    simp only [t1SuccessTerminalSteps, t1OutputSteps, t1RepairSteps]
    omega
  rw [hsplit, runConfig_add, hout, hrep]

/-- **The out-of-bounds terminal theorem, nonempty data.**  From the *exact*
`oobStart` configuration produced by `t1CS_runConfig_decide_oob_exact`, the
machine reaches the literal reject state with the head on cell `0` in exactly
`t1OobTerminalSteps r` genuine steps.

The final tape is `t1OutputFrames r false = t1ValidationFrames r`, i.e.
**bit-for-bit the input tape** (`t1CS_oob_final_tape_eq`): every `spent`
marker is restored to an `index` frame, the data field is untouched, and the
observable output frame still reads `output false`. -/
theorem t1CS_terminal_oob_exact (r : T1Request) (v : Bool)
    (hv : r.data[r.index]? = none) (hne : 0 < r.data.length) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length
          (4 * (r.index + (r.data.length - 1) + 3) + 3) (t1dOobHead_safe r)
          (t1ListTape
            ((t1LoopFramesRestored r (r.data.length - 1)).flatMap
              T1Frame.bits))
          .oobStart .p0 false false false v)
        (t1OobTerminalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape ((t1OutputFrames r false).flatMap T1Frame.bits))
        .reject .p0 false false false false := by
  have hlen : r.data.length ≤ r.index := (t1Selected_none_iff r).1 hv
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  have hstart : ([T1Frame.bof] ++
      List.replicate (r.index - r.data.length) T1Frame.index ++
      List.replicate r.data.length T1Frame.spent ++
      ([T1Frame.separator] ++ r.data.map T1Frame.data ++
        [T1Frame.output false]) ++ [T1Frame.finish, T1Frame.blank]) =
      t1LoopFramesRestored r (r.data.length - 1) := by
    simp only [t1LoopFramesRestored,
      show r.index - (r.data.length - 1) - 1 = r.index - r.data.length
        from by omega,
      show r.data.length - 1 + 1 = r.data.length from by omega]
    simp [List.append_assoc]
  have hend : ([T1Frame.bof] ++
      List.replicate (r.index - r.data.length + r.data.length) T1Frame.index ++
      ([T1Frame.separator] ++ r.data.map T1Frame.data ++
        [T1Frame.output false]) ++ [T1Frame.finish, T1Frame.blank]) =
      t1OutputFrames r false := by
    simp only [show r.index - r.data.length + r.data.length = r.index
      from by omega, t1OutputFrames]
    simp [List.append_assoc]
  have hmidLen : ([T1Frame.separator] ++ r.data.map T1Frame.data ++
      [T1Frame.output false]).length = r.data.length + 2 := by
    simp only [List.length_append, List.length_singleton, List.length_map]
    omega
  have hmid : ∀ f ∈ ([T1Frame.separator] ++ r.data.map T1Frame.data ++
      [T1Frame.output false]),
      f = .index ∨ f = .separator ∨ f = .finish ∨
        (∃ w, f = .data w) ∨ ∃ w, f = .output w := by
    intro f hf
    simp only [List.append_assoc, List.mem_append, List.mem_singleton] at hf
    rcases hf with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases List.mem_map.1 h with ⟨w, _, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨false, h⟩)))
  have hrep := t1CS_repair_pass_exact (encodeT1 r).length
    (r.index - r.data.length) r.data.length
    ([T1Frame.separator] ++ r.data.map T1Frame.data ++ [T1Frame.output false])
    [T1Frame.finish, T1Frame.blank] hmid
    (by simp only [hmidLen]; omega) false
  simp only [hmidLen, hstart, hend,
    show 4 * (1 + (r.index - r.data.length) + r.data.length +
      (r.data.length + 2)) - 1 =
      4 * (r.index + (r.data.length - 1) + 3) + 3 from by omega,
    cond_false] at hrep
  have hdisp := t1CS_oobStart_dispatch (encodeT1 r).length
    (4 * (r.index + (r.data.length - 1) + 3) + 3) (t1dOobHead_safe r)
    (t1ListTape ((t1LoopFramesRestored r (r.data.length - 1)).flatMap
      T1Frame.bits)) v
  have hsplit : t1OobTerminalSteps r =
      1 + t1RepairSteps (r.index - r.data.length) r.data.length
        (r.data.length + 2) := by
    simp only [t1OobTerminalSteps, t1RepairSteps]
    omega
  rw [hsplit, runConfig_add, hdisp, hrep]

/-- **The out-of-bounds terminal theorem, empty data.**  From the *exact*
`oobStart` configuration produced by
`t1CS_runConfig_decide_oob_empty_exact`, whose tape is still the untouched
input tape, the machine reaches the literal reject state with the head on
cell `0` in exactly `t1OobTerminalSteps r = 4 * r.index + 14` genuine steps,
leaving the tape unchanged. -/
theorem t1CS_terminal_oob_empty_exact (r : T1Request) (hdata : r.data = []) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
          (t1dEmptyOobHead_safe r)
          (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
          false false false false)
        (t1OobTerminalSteps r) =
      t1AlignedConfig (encodeT1 r).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .reject .p0 false false false false := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  have hL : r.data.length = 0 := by rw [hdata]; rfl
  have hlist : ([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
      List.replicate 0 T1Frame.spent ++
      ([T1Frame.separator] ++ [T1Frame.output false]) ++
      [T1Frame.finish, T1Frame.blank]) = t1OutputFrames r false := by
    simp [t1OutputFrames, hdata, List.append_assoc]
  have hlist' : ([T1Frame.bof] ++ List.replicate (r.index + 0) T1Frame.index ++
      ([T1Frame.separator] ++ [T1Frame.output false]) ++
      [T1Frame.finish, T1Frame.blank]) = t1OutputFrames r false := by
    simp [t1OutputFrames, hdata, List.append_assoc]
  have htape : t1ListTape (n := (encodeT1 r).length)
      ((t1OutputFrames r false).flatMap T1Frame.bits) =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape :=
    t1CS_oob_final_tape_eq r
  have hmid : ∀ f ∈ ([T1Frame.separator] ++ [T1Frame.output false]),
      f = .index ∨ f = .separator ∨ f = .finish ∨
        (∃ w, f = .data w) ∨ ∃ w, f = .output w := by
    intro f hf
    simp only [List.mem_append, List.mem_singleton] at hf
    rcases hf with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨false, h⟩)))
  have hmidLen : ([T1Frame.separator] ++
      [T1Frame.output false]).length = 2 := rfl
  have hrep := t1CS_repair_pass_exact (encodeT1 r).length r.index 0
    ([T1Frame.separator] ++ [T1Frame.output false])
    [T1Frame.finish, T1Frame.blank] hmid
    (by simp only [hmidLen]; omega) false
  simp only [hmidLen, hlist, hlist', htape,
    show 4 * (1 + r.index + 0 + 2) - 1 = 4 * (r.index + 2) + 3 from by omega,
    cond_false] at hrep
  have hdisp := t1CS_oobStart_dispatch (encodeT1 r).length
    (4 * (r.index + 2) + 3) (t1dEmptyOobHead_safe r)
    (T1M.initialConfig (t1Point (encodeT1 r))).tape false
  have hsplit : t1OobTerminalSteps r = 1 + t1RepairSteps r.index 0 2 := by
    simp only [t1OobTerminalSteps, t1RepairSteps, hL]
    omega
  rw [hsplit, runConfig_add, hdisp, hrep]

end Pnp3.Internal.PsubsetPpoly.TM
