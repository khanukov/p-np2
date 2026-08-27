import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutation

/-!
# T1b-B: the genuine destructive seek loop

This module closes one round of the T1 mutation loop with real `TM.runConfig`
theorems.  It adds no machine, control state, clock or frame code; its derived
layouts and configuration use the canonical vocabulary T1b-A introduced:
every `TM.stepConfig` fact still comes from the atomic macro-step theorems of
`TrueUniformSeekMutation.lean`, which in turn come from the standalone
transition-table lemmas through the generic step bridge.  The control table is
never unfolded here.

## The canonical loop configuration

`t1MutationConfig r j hj value` is the exact configuration

```text
tape  = t1MutationTape n r j
      = bof · index^(k-j) · spent^j · separator
          · data(b₀)…data(b_{j-1}) · cursor · data(b_{j+1})… · output(false)
          · finish · blank
head  = t1CursorBase r j - 1        (before the cursor when j ≤ k)
state = seekIndexBack.p3, latch = value
```

with `k = r.index`.  It is the state the genuine installation run of T1b-A
reaches at `j = 0` (`t1CS_mutationConfig_zero`).

## Results proved in this module

* `t1CS_scan_back_skip` — the backward multi-frame scan: `seekIndexBack`
  crosses a whole run of `spent`, `separator` and data frames in four genuine
  steps per frame, tape and latch untouched.  Its inductive step uses T1b-A's
  `t1CS_seekIndexBack_frame_skip`; the empty skipped run is the base case.
* `t1CS_mutationConfig_zero` — T1b-A's installation capstone lands exactly on
  `Σ(0)`.
* `t1CS_loop_iteration_exact` — the **one-iteration theorem**: for
  `j < r.index` and `j+1 < r.data.length`, in exactly `16 * j + 37` genuine
  steps `Σ(j)` becomes `Σ(j+1)`.  Because both sides are the canonical layout
  at their own `j`, the theorem *is* the conservation statement: the index
  field loses exactly one `index` frame and gains exactly one `spent` frame
  (`index^(k-j) · spent^j` becomes `index^(k-j-1) · spent^(j+1)`), the cursor
  is the unique cursor frame and moves from data slot `j` to data slot `j+1`,
  slot `j` is restored to `data r.data[j]`, the new cursor sits where
  `data r.data[j+1]` was, and every other frame — the whole tail, the
  observable output frame, the `bof` anchor and the separator — is unchanged.
* `t1CS_loop_oob_exact` — the **one-iteration out-of-bounds theorem**: for
  `j < r.index` and `j+1 = r.data.length`, in exactly `16 * j + 32` steps the
  machine reaches the `oobStart` boundary on the *precisely documented*
  intermediate tape `t1LoopFramesRestored r j`: the data field is fully
  restored and carries no cursor, but the index field is **not** restored — it
  holds `j+1` `spent` markers and `r.index - j - 1` unconsumed `index`
  frames.  No repair claim is made, and the head is left on the last cell of
  the output frame.

## Deliberately *not* claimed here

The iteration over `j` (`Σ(0) → Σ(min (r.index) (r.data.length - 1))`), the
`successStart` tail at `j = r.index`, and the terminal dichotomy driven by
`r.data[r.index]?` are **not** proved in this module: they are the next
slice.  Nothing below claims acceptance, output writing, or repair of the
consumed index field; this module stops *at* `successStart` and `oobStart` and
says nothing about the terminal arms T1c-1 activated behind them.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## List helpers -/

private theorem t1Drop_cons (d : List Bool) (j : Nat) (hj : j < d.length) :
    d.drop j = d[j] :: d.drop (j+1) := by
  induction d generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => exact ih j (by simpa using hj)

private theorem t1Replicate_split (m : Nat) (hm : 0 < m) (f : T1Frame) :
    List.replicate m f = List.replicate (m-1) f ++ [f] := by
  obtain ⟨m, rfl⟩ : ∃ t, m = t + 1 := ⟨m-1, by omega⟩
  simp [List.replicate_succ']

/-- Every frame of the run the backward scan and the forward cursor search
skip over is a `spent`, `separator` or data frame. -/
private theorem t1SkipRun_mem (j : Nat) (d : List Bool) :
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

/-! ## Base-explicit wrappers

Both wrappers only move an arithmetic side condition out of a dependent
position, so that the loop proof can name physical cell indices in one fixed
normal form. -/

private theorem t1BitsAt_split (n : Nat) (pre suffix : List T1Frame)
    (frame : T1Frame) (base : Nat) (hbase : 4 * pre.length = base)
    (hsafe : base + 4 < T1M.tapeLength n) :
    t1PhysicalBitsAt hsafe
        (t1ListTape (n := n) ((pre ++ frame :: suffix).flatMap T1Frame.bits)) =
      frame.bits := by
  subst hbase
  exact t1PhysicalBitsAt_flatMap n pre suffix frame hsafe

private theorem t1ListTape_write_frame' (n : Nat) (pre suf : List T1Frame)
    (f f' : T1Frame) (base : Nat) (hbase : 4 * pre.length = base) :
    t1ListTape (n := n) ((pre ++ f' :: suf).flatMap T1Frame.bits) =
      t1WriteFrame base f'.bits
        (t1ListTape (n := n) ((pre ++ f :: suf).flatMap T1Frame.bits)) := by
  subst hbase
  exact t1ListTape_write_frame n pre suf f f'

/-! ## The backward scan across a run of skipped frames -/

/-- **Backward multi-frame scan.**  `seekIndexBack` crosses a whole run of
`spent`, `separator` and data frames in exactly four genuine steps per frame,
leaving the tape and the latch untouched.  This is the only genuinely new
execution lemma of T1b-B; the empty skipped run is the base case, and the
inductive step uses T1b-A's `t1CS_seekIndexBack_frame_skip`. -/
theorem t1CS_scan_back_skip (n : Nat) (pre skipped suffix : List T1Frame)
    (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, f = .spent ∨ f = .separator ∨ ∃ v, f = .data v)
    (hsafe : 4 * (pre.length + skipped.length) < T1M.tapeLength n)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (pre.length + skipped.length) - 1) (by omega)
          (t1ListTape ((pre ++ skipped ++ suffix).flatMap T1Frame.bits))
          .seekIndexBack .p3 false false false latch)
        (4 * skipped.length) =
      t1AlignedConfig n (4 * pre.length - 1) (by omega)
        (t1ListTape ((pre ++ skipped ++ suffix).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false latch := by
  induction skipped generalizing pre with
  | nil => simp
  | cons f rest ih =>
      have hf : f = .spent ∨ f = .separator ∨ ∃ v, f = .data v := hskip f (by simp)
      have hrest : ∀ g ∈ rest, g = .spent ∨ g = .separator ∨ ∃ v, g = .data v :=
        fun g hg => hskip g (by simp [hg])
      have hlen : (pre ++ [f]).length = pre.length + 1 := by simp
      have hsafe' : 4 * ((pre ++ [f]).length + rest.length) < T1M.tapeLength n := by
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
          (t1ListTape (n := n) ((pre ++ f :: (rest ++ suffix)).flatMap T1Frame.bits)) =
          f.bits :=
        t1BitsAt_split n pre (rest ++ suffix) f (4 * pre.length) rfl hbase
      have hstep := t1CS_seekIndexBack_frame_skip n (4 * pre.length) (by omega) hbase
        (t1ListTape (n := n) ((pre ++ f :: (rest ++ suffix)).flatMap T1Frame.bits))
        latch f hf hbits
      rw [show 4 * (f :: rest).length = 4 * rest.length + 4 by simp; omega,
        runConfig_add]
      simp only [List.length_cons, List.append_assoc, List.cons_append]
      rw [hIH, hstep]

/-! ## Forward cursor search: grammar path -/

private theorem t1SeekCursorFwd_path : ∀ (frames : List T1Frame),
    (∀ f ∈ frames, f = .spent ∨ f = .separator ∨ ∃ v, f = .data v) →
    T1ValidPath .seekCursorFwd (frames ++ [T1Frame.cursor]) := by
  intro frames
  induction frames with
  | nil => intro _; exact ⟨trivial, by simp [t1Advance], trivial⟩
  | cons f rest ih =>
      intro h
      have hf := h f (by simp)
      have hrest := ih (fun g hg => h g (by simp [hg]))
      rcases hf with rfl | rfl | ⟨v, rfl⟩ <;>
        exact ⟨trivial, by simp [t1Advance], hrest⟩

private theorem t1SeekCursorFwd_advance : ∀ (frames : List T1Frame),
    (∀ f ∈ frames, f = .spent ∨ f = .separator ∨ ∃ v, f = .data v) →
    t1AdvanceList .seekCursorFwd (frames ++ [T1Frame.cursor]) = .backupCursor := by
  intro frames
  induction frames with
  | nil => intro _; rfl
  | cons f rest ih =>
      intro h
      have hf := h f (by simp)
      have hrest := ih (fun g hg => h g (by simp [hg]))
      rcases hf with rfl | rfl | ⟨v, rfl⟩ <;>
        simpa [t1AdvanceList, t1Advance] using hrest

/-! ## The three canonical loop layouts -/

/-- The canonical mutation layout after `j` decrements, with the observable
blank frame appended: the frame list backing `t1MutationTape`. -/
def t1LoopFrames (r : T1Request) (j : Nat) : List T1Frame :=
  t1MutationFrames r j ++ [T1Frame.blank]

/-- The layout *between* the on-tape decrement and the cursor restore: one
more `spent` marker than `t1LoopFrames r j`, cursor still in data slot `j`. -/
def t1LoopFramesMarked (r : T1Request) (j : Nat) : List T1Frame :=
  [T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
    List.replicate (j+1) T1Frame.spent ++ [T1Frame.separator] ++
    (r.data.take j).map T1Frame.data ++ [T1Frame.cursor] ++
    (r.data.drop (j+1)).map T1Frame.data ++
    [T1Frame.output false, T1Frame.finish, T1Frame.blank]

/-- The layout *after* the cursor restore and before the next probe: the data
field is completely restored and carries no cursor, while the index field
holds `j+1` `spent` markers.  This is exactly the tape the out-of-bounds
boundary is reached on. -/
def t1LoopFramesRestored (r : T1Request) (j : Nat) : List T1Frame :=
  [T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
    List.replicate (j+1) T1Frame.spent ++ [T1Frame.separator] ++
    r.data.map T1Frame.data ++
    [T1Frame.output false, T1Frame.finish, T1Frame.blank]

theorem t1MutationTape_eq_listTape (n : Nat) (r : T1Request) (j : Nat) :
    t1MutationTape n r j =
      t1ListTape (n := n) ((t1LoopFrames r j).flatMap T1Frame.bits) := rfl

/-! ### Layout splits

Each split is a pure re-association of the layout definitions; no execution
claim is involved. -/

private theorem t1LoopFrames_split_scan (r : T1Request) (j : Nat) :
    t1LoopFrames r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j) T1Frame.index) ++
        (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take j).map T1Frame.data) ++
        (T1Frame.cursor :: ((r.data.drop (j+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank])) := by
  simp [t1LoopFrames, t1MutationFrames, List.append_assoc]

private theorem t1LoopFrames_split_mark (r : T1Request) (j : Nat)
    (hjk : j < r.index) :
    t1LoopFrames r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index) ++
        T1Frame.index :: (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take j).map T1Frame.data ++
          T1Frame.cursor :: ((r.data.drop (j+1)).map T1Frame.data ++
            [T1Frame.output false, T1Frame.finish, T1Frame.blank])) := by
  rw [t1LoopFrames, t1MutationFrames,
    t1Replicate_split (r.index - j) (by omega) T1Frame.index]
  simp [List.append_assoc]

private theorem t1LoopFramesMarked_split_mark (r : T1Request) (j : Nat) :
    t1LoopFramesMarked r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index) ++
        T1Frame.spent :: (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take j).map T1Frame.data ++
          T1Frame.cursor :: ((r.data.drop (j+1)).map T1Frame.data ++
            [T1Frame.output false, T1Frame.finish, T1Frame.blank])) := by
  rw [t1LoopFramesMarked, List.replicate_succ]
  simp [List.append_assoc]

private theorem t1LoopFramesMarked_split_fwd (r : T1Request) (j : Nat) :
    t1LoopFramesMarked r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
          [T1Frame.spent]) ++
        (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take j).map T1Frame.data ++ [T1Frame.cursor]) ++
        ((r.data.drop (j+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  rw [t1LoopFramesMarked, List.replicate_succ]
  simp [List.append_assoc]

private theorem t1LoopFramesMarked_split_cursor (r : T1Request) (j : Nat) :
    t1LoopFramesMarked r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
          [T1Frame.spent] ++ List.replicate j T1Frame.spent ++
          [T1Frame.separator] ++ (r.data.take j).map T1Frame.data) ++
        T1Frame.cursor :: ((r.data.drop (j+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  rw [t1LoopFramesMarked, List.replicate_succ]
  simp [List.append_assoc]

private theorem t1LoopFramesRestored_split_cursor (r : T1Request) (j : Nat)
    (v : Bool) (hj : j < r.data.length) (hv : r.data[j] = v) :
    t1LoopFramesRestored r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
          [T1Frame.spent] ++ List.replicate j T1Frame.spent ++
          [T1Frame.separator] ++ (r.data.take j).map T1Frame.data) ++
        T1Frame.data v :: ((r.data.drop (j+1)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  have hd : r.data.map T1Frame.data =
      (r.data.take j).map T1Frame.data ++
        T1Frame.data v :: (r.data.drop (j+1)).map T1Frame.data := by
    conv_lhs => rw [← List.take_append_drop j r.data]
    rw [List.map_append, t1Drop_cons r.data j hj, hv]
    simp
  rw [t1LoopFramesRestored, hd, List.replicate_succ]
  simp [List.append_assoc]

private theorem t1LoopFramesRestored_split_probe (r : T1Request) (j : Nat)
    (v' : Bool) (hj1 : j + 1 < r.data.length) (hv' : r.data[j+1] = v') :
    t1LoopFramesRestored r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
          List.replicate (j+1) T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take (j+1)).map T1Frame.data) ++
        T1Frame.data v' :: ((r.data.drop (j+2)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  have hd : r.data.map T1Frame.data =
      (r.data.take (j+1)).map T1Frame.data ++
        T1Frame.data v' :: (r.data.drop (j+2)).map T1Frame.data := by
    conv_lhs => rw [← List.take_append_drop (j+1) r.data]
    rw [List.map_append, t1Drop_cons r.data (j+1) hj1, hv']
    simp
  rw [t1LoopFramesRestored, hd]
  simp [List.append_assoc]

private theorem t1LoopFramesRestored_split_oob (r : T1Request) (j : Nat)
    (hj1 : j + 1 = r.data.length) :
    t1LoopFramesRestored r j =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
          List.replicate (j+1) T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take (j+1)).map T1Frame.data) ++
        T1Frame.output false :: [T1Frame.finish, T1Frame.blank] := by
  have htake : r.data.take (j+1) = r.data := by
    rw [hj1]; simp
  rw [t1LoopFramesRestored, htake]

private theorem t1LoopFrames_succ_eq (r : T1Request) (j : Nat) :
    t1LoopFrames r (j+1) =
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
          List.replicate (j+1) T1Frame.spent ++ [T1Frame.separator] ++
          (r.data.take (j+1)).map T1Frame.data) ++
        T1Frame.cursor :: ((r.data.drop (j+2)).map T1Frame.data ++
          [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
  have hsub : r.index - (j+1) = r.index - j - 1 := by omega
  rw [t1LoopFrames, t1MutationFrames, hsub]
  simp [List.append_assoc]

/-! ### Layout lengths -/

private theorem t1IdxPre_length (r : T1Request) (j : Nat) :
    ([T1Frame.bof] ++ List.replicate (r.index - j) T1Frame.index).length =
      r.index - j + 1 := by
  simp

private theorem t1SkipRun_length (r : T1Request) (j : Nat)
    (hj : j ≤ r.data.length) :
    (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
      (r.data.take j).map T1Frame.data).length = 2 * j + 1 := by
  simp
  omega

/-! ## The canonical loop configuration -/

theorem t1CursorBase_safe (r : T1Request) (j : Nat) (hj : j < r.data.length) :
    t1CursorBase r j + 4 < T1M.tapeLength (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hb : t1CursorBase r j + 4 ≤ (encodeT1 r).length := by
    simp only [t1CursorBase, t1CursorFrameIndex, hN]
    omega
  exact t1_lt_tapeLength _ _ hb

/-- **Σ(r, j, value): the canonical mutation loop configuration.**  The tape is
the derived layout at stage `j`; under the loop theorems' bound `j ≤ r.index`,
the head sits on the last cell before the cursor frame.  The control is in the
backward index scan and the latch carries `value`. -/
def t1MutationConfig (r : T1Request) (j : Nat) (hj : j < r.data.length)
    (value : Bool) : Configuration (M := T1M) (encodeT1 r).length :=
  t1AlignedConfig (encodeT1 r).length (t1CursorBase r j - 1)
    (by have := t1CursorBase_safe r j hj; omega)
    (t1MutationTape (encodeT1 r).length r j) .seekIndexBack .p3
    false false false value

@[simp] theorem t1MutationConfig_tape (r : T1Request) (j : Nat)
    (hj : j < r.data.length) (value : Bool) :
    (t1MutationConfig r j hj value).tape = t1MutationTape (encodeT1 r).length r j := rfl

@[simp] theorem t1MutationConfig_head (r : T1Request) (j : Nat)
    (hj : j < r.data.length) (value : Bool) :
    ((t1MutationConfig r j hj value).head : Nat) = t1CursorBase r j - 1 := rfl

/-- **The installation capstone lands exactly on Σ(0).** -/
theorem t1CS_mutationConfig_zero (r : T1Request) (b : Bool) (rest : List Bool)
    (hdata : r.data = b :: rest) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length 0
          (t1_lt_tapeLength _ _ (by omega))
          (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation)
        (4 * r.index + 17) =
      t1MutationConfig r 0 (by simp [hdata]) b := by
  have hcap := t1CS_install_first_cursor_exact r b rest hdata
  have htape : t1MutationTape (encodeT1 r).length r 0 =
      t1WriteFrame (4 * (r.index + 2)) T1Frame.cursor.bits
        (T1M.initialConfig (t1Point (encodeT1 r))).tape :=
    t1MutationTape_zero r b rest hdata
  have hhead : t1CursorBase r 0 - 1 = 4 * (r.index + 2) - 1 := by
    simp [t1CursorBase, t1CursorFrameIndex]
  rw [hcap, t1MutationConfig]
  simp only [htape, hhead]


/-! ## Layout lengths used by the loop proof -/

private theorem t1MarkPre_length (r : T1Request) (j : Nat) (hjk : j < r.index) :
    ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index).length =
      r.index - j := by
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate]
  omega

private theorem t1FwdPre_length (r : T1Request) (j : Nat) (hjk : j < r.index) :
    ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
      [T1Frame.spent]).length = r.index - j + 1 := by
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate]
  omega

private theorem t1FwdRun_length (r : T1Request) (j : Nat) (hjd : j < r.data.length) :
    (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
      (r.data.take j).map T1Frame.data ++ [T1Frame.cursor]).length = 2 * j + 2 := by
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, List.length_map, List.length_take]
  omega

private theorem t1CursorPre_length (r : T1Request) (j : Nat) (hjk : j < r.index)
    (hjd : j < r.data.length) :
    ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
      [T1Frame.spent] ++ List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
      (r.data.take j).map T1Frame.data).length = r.index + j + 2 := by
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, List.length_map, List.length_take]
  omega

private theorem t1ProbePre_length (r : T1Request) (j : Nat) (hjk : j < r.index)
    (hjd : j < r.data.length) :
    ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
      List.replicate (j+1) T1Frame.spent ++ [T1Frame.separator] ++
      (r.data.take (j+1)).map T1Frame.data).length = r.index + j + 3 := by
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, List.length_map, List.length_take]
  omega

/-- Every physical cell the loop iteration touches is inside the tape. -/
theorem t1LoopProbe_safe (r : T1Request) (j : Nat) (hjd : j < r.data.length) :
    4 * (r.index + j + 3) + 4 < T1M.tapeLength (encodeT1 r).length := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  omega

/-! ## The shared prefix of the loop iteration

Phases A–F: the backward index scan, the on-tape decrement, the forward
cursor search, the turnaround and the cursor restore.  They are identical for
the data outcome and for the out-of-bounds outcome, which differ only in the
frame the following probe reads. -/

private theorem t1CS_loop_prefix_exact (r : T1Request) (j : Nat)
    (hjk : j < r.index) (hjd : j < r.data.length) (v : Bool) (hv : r.data[j] = v) :
    TM.runConfig (M := T1M) (t1MutationConfig r j hjd v) (16 * j + 28) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3))
        (by have := t1LoopProbe_safe r j hjd; omega)
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .probeData .p0 false false false v := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  have hcb : t1CursorBase r j = 4 * (r.index + j + 2) := by
    unfold t1CursorBase t1CursorFrameIndex
    omega
  have hL1 := t1IdxPre_length r j
  have hLS := t1SkipRun_length r j (by omega)
  have hL2 := t1MarkPre_length r j hjk
  have hL3 := t1FwdPre_length r j hjk
  have hLSC := t1FwdRun_length r j hjd
  have hL4 := t1CursorPre_length r j hjk hjd
  have hsafeB : 4 * (r.index - j) + 4 < T1M.tapeLength (encodeT1 r).length := by omega
  have hsafeE : 4 * (r.index + j + 2) + 4 < T1M.tapeLength (encodeT1 r).length := by omega
  -- Phase A: the backward index scan crosses `spent^j · separator · data^j`.
  have hA : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 2) - 1) (by omega)
        (t1ListTape ((t1LoopFrames r j).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false v)
      (4 * (2 * j + 1)) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index - j) + 3) (by omega)
        (t1ListTape ((t1LoopFrames r j).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false v := by
    have hscan := t1CS_scan_back_skip (encodeT1 r).length
      ([T1Frame.bof] ++ List.replicate (r.index - j) T1Frame.index)
      (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
        (r.data.take j).map T1Frame.data)
      (T1Frame.cursor :: ((r.data.drop (j+1)).map T1Frame.data ++
        [T1Frame.output false, T1Frame.finish, T1Frame.blank]))
      (by rw [hL1]; omega) (t1SkipRun_mem j r.data)
      (by rw [hL1, hLS]; omega) v
    rw [← t1LoopFrames_split_scan r j] at hscan
    simp only [hL1, hLS,
      show 4 * (r.index - j + 1 + (2 * j + 1)) - 1 = 4 * (r.index + j + 2) - 1 from by omega,
      show 4 * (r.index - j + 1) - 1 = 4 * (r.index - j) + 3 from by omega] at hscan
    exact hscan
  -- Phase B: the rightmost unconsumed `index` frame is located.
  have hB : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index - j) + 3) (by omega)
        (t1ListTape ((t1LoopFrames r j).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false v) 4 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index - j)) (by omega)
        (t1ListTape ((t1LoopFrames r j).flatMap T1Frame.bits))
        .markSpent .p0 false false false v := by
    have hbits : t1PhysicalBitsAt hsafeB
        (t1ListTape (n := (encodeT1 r).length)
          ((t1LoopFrames r j).flatMap T1Frame.bits)) = T1Frame.index.bits := by
      rw [t1LoopFrames_split_mark r j hjk]
      exact t1BitsAt_split _ _ _ T1Frame.index (4 * (r.index - j)) (by rw [hL2]) hsafeB
    exact t1CS_seekIndexBack_frame_mark _ (4 * (r.index - j)) hsafeB _ v hbits
  -- Phase C: the on-tape decrement.
  have hC : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index - j)) (by omega)
        (t1ListTape ((t1LoopFrames r j).flatMap T1Frame.bits))
        .markSpent .p0 false false false v) 4 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index - j) + 4) hsafeB
        (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits))
        .seekCursorFwd .p0 false false false v := by
    have htape : t1ListTape (n := (encodeT1 r).length)
        ((t1LoopFramesMarked r j).flatMap T1Frame.bits) =
        t1WriteFrame (4 * (r.index - j)) T1Frame.spent.bits
          (t1ListTape ((t1LoopFrames r j).flatMap T1Frame.bits)) := by
      rw [t1LoopFramesMarked_split_mark r j, t1LoopFrames_split_mark r j hjk]
      exact t1ListTape_write_frame' _ _ _ T1Frame.index T1Frame.spent _ (by rw [hL2])
    rw [htape]
    exact t1CS_markSpent_frame _ (4 * (r.index - j)) hsafeB _ v
  -- Phase D: the forward cursor search.
  have hD : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index - j) + 4) hsafeB
        (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits))
        .seekCursorFwd .p0 false false false v) (4 * (2 * j + 2)) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 2) + 4) hsafeE
        (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits))
        .backupCursor .p0 false false false v := by
    have hscan := t1CS_scan_frames (encodeT1 r).length
      ([T1Frame.bof] ++ List.replicate (r.index - j - 1) T1Frame.index ++
        [T1Frame.spent])
      (List.replicate j T1Frame.spent ++ [T1Frame.separator] ++
        (r.data.take j).map T1Frame.data ++ [T1Frame.cursor])
      ((r.data.drop (j+1)).map T1Frame.data ++
        [T1Frame.output false, T1Frame.finish, T1Frame.blank])
      .seekCursorFwd (t1SeekCursorFwd_path _ (t1SkipRun_mem j r.data))
      (by rw [hL3, hLSC]; omega) v
    rw [← t1LoopFramesMarked_split_fwd r j,
      t1SeekCursorFwd_advance _ (t1SkipRun_mem j r.data)] at hscan
    simp only [hL3, hLSC,
      show 4 * (r.index - j + 1) = 4 * (r.index - j) + 4 from by omega,
      show 4 * (r.index - j + 1 + (2 * j + 2)) = 4 * (r.index + j + 2) + 4 from by omega]
      at hscan
    exact hscan
  -- Phase E: the turnaround onto the cursor frame.
  have hE : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 2) + 4) hsafeE
        (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits))
        .backupCursor .p0 false false false v) 4 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 2)) (by omega)
        (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits))
        .writeData .p0 false false false v :=
    t1CS_backupCursor_walk _ (4 * (r.index + j + 2)) hsafeE _ v
  -- Phase F: the cursor restore, `cursor ↦ data r.data[j]`.
  have hF : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 2)) (by omega)
        (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits))
        .writeData .p0 false false false v) 4 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3)) (by omega)
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .probeData .p0 false false false v := by
    have htape : t1ListTape (n := (encodeT1 r).length)
        ((t1LoopFramesRestored r j).flatMap T1Frame.bits) =
        t1WriteFrame (4 * (r.index + j + 2)) (T1Frame.data v).bits
          (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits)) := by
      rw [t1LoopFramesRestored_split_cursor r j v hjd hv,
        t1LoopFramesMarked_split_cursor r j]
      exact t1ListTape_write_frame' _ _ _ T1Frame.cursor (T1Frame.data v) _ (by rw [hL4])
    have hstep := t1CS_writeData_frame (encodeT1 r).length (4 * (r.index + j + 2)) hsafeE
      (t1ListTape ((t1LoopFramesMarked r j).flatMap T1Frame.bits)) v
    rw [← htape] at hstep
    simpa only [show 4 * (r.index + j + 2) + 4 = 4 * (r.index + j + 3) from by omega]
      using hstep
  simp only [t1MutationConfig, t1MutationTape_eq_listTape, hcb]
  rw [show 16 * j + 28 =
      4 * (2 * j + 1) + (4 + (4 + (4 * (2 * j + 2) + (4 + 4)))) from by omega,
    runConfig_add, hA, runConfig_add, hB, runConfig_add, hC, runConfig_add, hD,
    runConfig_add, hE, hF]

/-! ## The one-iteration theorems -/

/-- **The genuine loop step.**  For `j < r.index` (an index unit is still
unconsumed) and `j + 1 < r.data.length` (the data field has a next slot), the
machine runs from `Σ(r, j, r.data[j])` to `Σ(r, j+1, r.data[j+1])` in exactly
`16 * j + 37` genuine `TM.runConfig` steps.

Both configurations are the canonical layout at their own `j`, so the
statement pins down the whole tape: `index^(k-j) · spent^j` becomes
`index^(k-j-1) · spent^(j+1)` (one on-tape decrement, no other index-field
change), the cursor frame — the unique one — moves from data slot `j` to data
slot `j+1`, slot `j` is restored to `data r.data[j]`, and the `bof` anchor,
the separator, the untouched data slots, the output frame, the finish frame
and the blank frame are all unchanged.  The head returns to the last cell
before the new cursor frame and the latch carries `r.data[j+1]`. -/
theorem t1CS_loop_iteration_exact (r : T1Request) (j : Nat)
    (hjk : j < r.index) (hj1 : j + 1 < r.data.length)
    (v v' : Bool) (hv : r.data[j]? = some v) (hv' : r.data[j+1]? = some v') :
    TM.runConfig (M := T1M) (t1MutationConfig r j (by omega) v) (16 * j + 37) =
      t1MutationConfig r (j+1) hj1 v' := by
  have hN : (encodeT1 r).length = 4 * (r.index + r.data.length + 4) :=
    encodeT1_length r
  have hTL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (le_refl _)
  have hdv : r.data[j] = v := by
    rw [List.getElem?_eq_getElem (show j < r.data.length by omega)] at hv
    exact Option.some.inj hv
  have hdv' : r.data[j+1] = v' := by
    rw [List.getElem?_eq_getElem hj1] at hv'
    exact Option.some.inj hv'
  have hcb' : t1CursorBase r (j+1) = 4 * (r.index + j + 3) := by
    unfold t1CursorBase t1CursorFrameIndex
    omega
  have hL5 := t1ProbePre_length r j hjk (by omega)
  have hsafeG : 4 * (r.index + j + 3) + 4 < T1M.tapeLength (encodeT1 r).length :=
    t1LoopProbe_safe r j (by omega)
  -- Phase G: the probe of the next data frame latches `r.data[j+1]`.
  have hG : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3)) (by omega)
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .probeData .p0 false false false v) 4 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3) + 4) hsafeG
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .turnInstall .p0 false false false v' := by
    have hbits : t1PhysicalBitsAt hsafeG
        (t1ListTape (n := (encodeT1 r).length)
          ((t1LoopFramesRestored r j).flatMap T1Frame.bits)) =
        (T1Frame.data v').bits := by
      rw [t1LoopFramesRestored_split_probe r j v' hj1 hdv']
      exact t1BitsAt_split _ _ _ (T1Frame.data v') (4 * (r.index + j + 3))
        (by rw [hL5]) hsafeG
    exact t1CS_probeData_frame_data _ (4 * (r.index + j + 3)) hsafeG _ v v' hbits
  -- Phase H: the turnaround onto the new cursor position.
  have hH : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3) + 4) hsafeG
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .turnInstall .p0 false false false v') 1 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3) + 3) (by omega)
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .writeCursor .p3 false false false v' := by
    simpa only [show 4 * (r.index + j + 3) + 4 - 1 = 4 * (r.index + j + 3) + 3 from by omega]
      using t1CS_turnInstall_step (encodeT1 r).length (4 * (r.index + j + 3) + 4)
        (by omega) hsafeG _ v'
  -- Phase I: the new cursor is installed.
  have hI : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3) + 3) (by omega)
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .writeCursor .p3 false false false v') 4 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3) - 1) (by omega)
        (t1ListTape ((t1LoopFrames r (j+1)).flatMap T1Frame.bits))
        .seekIndexBack .p3 false false false v' := by
    have htape : t1ListTape (n := (encodeT1 r).length)
        ((t1LoopFrames r (j+1)).flatMap T1Frame.bits) =
        t1WriteFrame (4 * (r.index + j + 3)) T1Frame.cursor.bits
          (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits)) := by
      rw [t1LoopFrames_succ_eq r j, t1LoopFramesRestored_split_probe r j v' hj1 hdv']
      exact t1ListTape_write_frame' _ _ _ (T1Frame.data v') T1Frame.cursor _
        (by rw [hL5])
    rw [htape]
    exact t1CS_writeCursor_frame _ (4 * (r.index + j + 3)) (by omega) hsafeG _ v'
  rw [show 16 * j + 37 = (16 * j + 28) + (4 + (1 + 4)) from by omega, runConfig_add,
    t1CS_loop_prefix_exact r j hjk (by omega) v hdv, runConfig_add, hG,
    runConfig_add, hH, hI]
  simp only [t1MutationConfig, t1MutationTape_eq_listTape, hcb']

/-- **The genuine out-of-bounds loop step.**  For `j < r.index` (an index unit
is still unconsumed) but `j + 1 = r.data.length` (the data field has no next
slot), the machine runs from `Σ(r, j, r.data[j])` to the `oobStart`
boundary in exactly `16 * j + 32` genuine steps.

The final tape is stated exactly, as `t1LoopFramesRestored r j`:

```text
bof · index^(k-j-1) · spent^(j+1) · separator · data(b₀)…data(b_{L-1})
    · output(false) · finish · blank
```

so the *data field is fully restored and carries no cursor frame*, while the
*index field is not restored*: `j+1` units have been consumed and only
`k-j-1` remain.  This is an intermediate state, not a repaired one; no claim
is made that any later phase restores the index field, and reaching `oobStart`
is not a rejection: this theorem stops at the boundary.  The head is left on
the last cell of the output frame and the latch still carries `r.data[j]`. -/
theorem t1CS_loop_oob_exact (r : T1Request) (j : Nat)
    (hjk : j < r.index) (hj1 : j + 1 = r.data.length)
    (v : Bool) (hv : r.data[j]? = some v) :
    TM.runConfig (M := T1M) (t1MutationConfig r j (by omega) v) (16 * j + 32) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + j + 3) + 3)
        (by have := t1LoopProbe_safe r j (by omega); omega)
        (t1ListTape ((t1LoopFramesRestored r j).flatMap T1Frame.bits))
        .oobStart .p0 false false false v := by
  have hdv : r.data[j] = v := by
    rw [List.getElem?_eq_getElem (show j < r.data.length by omega)] at hv
    exact Option.some.inj hv
  have hL5 := t1ProbePre_length r j hjk (by omega)
  have hsafeG : 4 * (r.index + j + 3) + 4 < T1M.tapeLength (encodeT1 r).length :=
    t1LoopProbe_safe r j (by omega)
  have hbits : t1PhysicalBitsAt hsafeG
      (t1ListTape (n := (encodeT1 r).length)
        ((t1LoopFramesRestored r j).flatMap T1Frame.bits)) =
      (T1Frame.output false).bits := by
    rw [t1LoopFramesRestored_split_oob r j hj1]
    exact t1BitsAt_split _ _ _ (T1Frame.output false) (4 * (r.index + j + 3))
      (by rw [hL5]) hsafeG
  rw [show 16 * j + 32 = (16 * j + 28) + 4 from by omega, runConfig_add,
    t1CS_loop_prefix_exact r j hjk (by omega) v hdv]
  exact t1CS_probeData_frame_oob _ (4 * (r.index + j + 3)) hsafeG _ v hbits

end Pnp3.Internal.PsubsetPpoly.TM
