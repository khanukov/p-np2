import Complexity.TMVerifier.TuringToolkit.GateOneWalkKernel

/-!
# G1 cursor walk: the tape invariant `Σ(j)` and its real installation

**Progress classification: Infrastructure.**

PR3a.  The merged atomic macros hold on **arbitrary** frame lists; this module
pins the **one canonical frame list** the cursor walk runs on and reaches it
from the **real initial configuration** `G1M.initialConfig`.  It stops exactly
there: **no round is executed here**.

## `Σ(j)`: the invariant vocabulary

Write `u = r.tag.units`, `a1 = r.arg1`, `a2 = r.arg2`, `m = r.vals.length`.  For
`j ≤ a2` and `j < m` the frame list is `g1WalkFrames r j`:

```text
bof · tag^u · argSep · index^a1 · argSep          -- g1FieldRouteFrames r
    · index^(a2-j) · spent^j · separator
    · data(vals.take j) · cursor · data(vals.drop (j+1))
    · output false · finish · blank
```

`g1WalkConfig r j _ _ v _` is that list as a tape, head on the **last cell of the
frame preceding the cursor** (`4 * g1WalkCursor r j - 1`, with
`g1WalkCursor r j = u + a1 + a2 + j + 4` the cursor's frame ordinal), control
`bSeek .p3` with an empty frame buffer, and context `g1Ctx0.withVB v`, i.e.
`pass = crossed = false` and the latched operand bit `vB = v`.  Both numeric
guards and `vals[j]? = some v` are explicit arguments, so the configuration
cannot be formed outside the invariant's range or with the wrong hidden bit.

Every structural side condition the merged macros take as a *hypothesis* is
**proved here** from the numeric guards, never assumed:

* `g1WalkFrames_length_eq_validation` — the invariant word is exactly as long as
  the real tape word `encodeG1Frames r ++ [.blank]`, so no frame is invented or
  lost;
* `g1WalkFrames_count_index/_count_spent/_count_cursor` — `a2 - j` unspent
  units, `j` spent ones, and the cursor is **unique**;
* `g1WalkOperand2_spent_suffix` — `spent^j` is the *right* suffix of the
  operand-2 field, so the reverse seek's stopping `index` is the one immediately
  left of the spent run;
* `g1WalkSkipRun_mem` / `g1WalkSkipRun_no_index` — the run both scans of a round
  cross is `spent^j · separator · data^j`, which contains **no** `index` frame;
  this is why the forward scan `bFwd`, which has no `index` row, never stalls,
  and it is a theorem about the layout, not a semantic hypothesis;
* `g1WalkCursor_safe` — every physical cell a round touches is inside the tape
  on the invariant domain `j ≤ arg2` and `j < m`.

`g1WalkFramesMarked` and `g1WalkFramesRestored` name the two other layouts a
round passes through.  `g1WalkFramesRestored` carries the counts above;
`g1WalkFramesMarked` is pure vocabulary for PR3b and no statement here uses it.

## What is executed here

Only the **installation**, and only from `G1M.initialConfig`:

* `g1CS_walk_install_exact` — for a canonical `and`/`or` request with `a2 > 0`
  and `vals[0]? = some v`, exactly `g1WalkInstallSteps r = g1InstallScanSteps r
  + 9` genuine steps reach `Σ(r, 0, v)`: the read-only installation scan, the
  probe/latch of `vals[0]` (`5`) and the leftward cursor install (`4`).  Exactly
  **one** frame is written, `data vals[0] ↦ cursor`.
* `g1CS_walk_install_oob_exact` — the **empty-data** branch: with `vals = []`
  the same read-only scan's probe meets the `output false` destination and
  `g1WalkEmptyOOBSteps r = g1InstallScanSteps r + 4` steps end in the stable
  `bOOB` boundary with the tape **bit-for-bit the initial tape**.
* `g1CS_walk_oob_ne_invariant` — those two endpoints are different boundaries.

Both counts stay inside the unchanged public clock `g1Clock`; no new `Nat`,
index, width, offset or request field is introduced anywhere.  The two capstones
are composed from the merged `GateOneInstallScan` and `GateOneProbeInstall`
atoms only, with the transition table never unfolded.  `GateOneWalkKernel` is
imported for exactly one name, `G1WalkSkip`, in whose terms the two pure
skip-run facts above are stated; no macro of that module is used below.

## Explicit deferrals (PR3b and later)

`Σ(0)` is *reached*; nothing here moves off it.  There is **no** one-round
iteration theorem (`Σ(j) → Σ(j+1)`), **no** normal-round or out-of-range
preservation theorem on `Σ(j)`, no induction over `j`, no loop, driver or
cumulative clock, no successful terminal at `j = a2`, no aggregation of the two
out-of-range branches, no addressing and **no positive-index operand-value
theorem**: nothing below claims the machine resolves `r.vals[r.arg2]?` for
`a2 > 0`.  Also absent: the `spent ↦ index` repair sweep, pass A, combine, the
output write, `TM.accepts`, gate-semantics correctness, a full-clock theorem and
non-canonical or physically padded tapes.  As everywhere in this development,
every execution statement is scoped to the exact tape `encodeG1 r`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## List helpers -/

private theorem g1Replicate_split (m : Nat) (hm : 0 < m) (f : G1Frame) :
    List.replicate m f = List.replicate (m - 1) f ++ [f] := by
  obtain ⟨m, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  simp [List.replicate_succ']

private theorem g1Vals_cons {l : List Bool} {v : Bool} (h : l[0]? = some v) :
    ∃ rest : List Bool, l = v :: rest := by
  cases l with
  | nil => exact absurd h (by simp)
  | cons c cs =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨cs, by rw [h]⟩

private theorem g1Length_pos_of_get {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) : j < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact Option.noConfusion h

/-! ## The two structural facts the walk's scans depend on

Both are statements about the *layout*, proved here; the merged atomic macros
take them as hypotheses. -/

/-- **The run both scans of a round cross is skippable.**  Between the marked
`index` and the cursor the layout holds only `spent`, the `separator` and data
frames. -/
theorem g1WalkSkipRun_mem (j : Nat) (vals : List Bool) :
    ∀ f ∈ (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
        (vals.take j).map G1Frame.data), G1WalkSkip f := by
  intro f hf
  rcases List.mem_append.1 hf with h1 | h2
  · rcases List.mem_append.1 h1 with h | h
    · have hs : f = G1Frame.spent := List.eq_of_mem_replicate h
      rw [hs]; exact trivial
    · have hs : f = G1Frame.separator := by simpa using h
      rw [hs]; exact trivial
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 h2
    exact trivial

/-- **The forward scan never meets an unspent `index`.**  `bFwd` has no `index`
row at all, so this is exactly the fact that keeps the forward pass of a round
inside its skip class; it is a corollary of the layout, not an assumption. -/
theorem g1WalkSkipRun_no_index (j : Nat) (vals : List Bool) :
    G1Frame.index ∉ (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
      (vals.take j).map G1Frame.data) := by
  intro h
  exact (g1WalkSkipRun_mem j vals _ h : G1WalkSkip G1Frame.index)

/-- **`spent^j` is the right suffix of the operand-2 field.**  Consequently the
rightmost unspent `index` is the frame immediately left of the spent run, which
is the frame the reverse seek stops on. -/
theorem g1WalkOperand2_spent_suffix (a2 j : Nat) (hj : j < a2) :
    List.replicate (a2 - j) G1Frame.index ++ List.replicate j G1Frame.spent =
      (List.replicate (a2 - j - 1) G1Frame.index ++ [G1Frame.index]) ++
        List.replicate j G1Frame.spent := by
  rw [g1Replicate_split (a2 - j) (by omega) G1Frame.index]

/-! ## The three canonical layouts of a round -/

/-- **`Σ(j)`'s frame list.**  The canonical word with the operand-2 field split
into `index^(arg2-j) · spent^j`, the cursor hiding data slot `j`, and the
observable blank frame appended. -/
def g1WalkFrames (r : G1Request) (j : Nat) : List G1Frame :=
  g1FieldRouteFrames r ++ List.replicate (r.arg2 - j) G1Frame.index ++
    List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
    (r.vals.take j).map G1Frame.data ++ [G1Frame.cursor] ++
    (r.vals.drop (j + 1)).map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The layout *between* the `index ↦ spent` write and the cursor restore: one
more `spent` marker, cursor still on data slot `j`.  Vocabulary only — no
statement in this module mentions it, and nothing here writes it. -/
def g1WalkFramesMarked (r : G1Request) (j : Nat) : List G1Frame :=
  g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
    List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
    (r.vals.take j).map G1Frame.data ++ [G1Frame.cursor] ++
    (r.vals.drop (j + 1)).map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The layout *after* the cursor restore and before the next probe: the data
region is exactly `vals` and carries no cursor, while the operand-2 field is
partially spent, `index^(arg2-j-1) · spent^(j+1)`.  Vocabulary only: the round
that produces it is PR3b. -/
def g1WalkFramesRestored (r : G1Request) (j : Nat) : List G1Frame :=
  g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
    List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
    r.vals.map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The frame ordinal of the cursor in `Σ(j)`. -/
def g1WalkCursor (r : G1Request) (j : Nat) : Nat :=
  r.tag.units + r.arg1 + r.arg2 + j + 4

/-! ### Lengths, counts and uniqueness -/

theorem g1WalkFrames_length (r : G1Request) (j : Nat)
    (hj2 : j ≤ r.arg2) (hj : j < r.vals.length) :
    (g1WalkFrames r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp only [g1WalkFrames, List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_map, List.length_take, List.length_drop,
    List.length_cons, List.length_nil]
  omega

/-- **The invariant word is exactly the real tape word's length.**  No frame is
invented and none is lost by the walk. -/
theorem g1WalkFrames_length_eq_validation (r : G1Request) (j : Nat)
    (hj2 : j ≤ r.arg2) (hj : j < r.vals.length) :
    (g1WalkFrames r j).length = (encodeG1Frames r ++ [G1Frame.blank]).length := by
  rw [g1WalkFrames_length r j hj2 hj]
  simp only [List.length_append, encodeG1Frames_length, List.length_cons,
    List.length_nil]

private theorem g1Count_replicate_ne (f g : G1Frame) (m : Nat) (h : f ≠ g) :
    (List.replicate m g).count f = 0 :=
  List.count_eq_zero.2 (fun hmem => h (List.eq_of_mem_replicate hmem))

/-- A frame that is no `data` frame does not occur in a run of data frames. -/
private theorem g1Count_data_run (f : G1Frame) (l : List G1Frame)
    (hl : ∀ g ∈ l, ∃ v : Bool, g = G1Frame.data v)
    (hf : ∀ v : Bool, f ≠ G1Frame.data v) : l.count f = 0 :=
  List.count_eq_zero.2 (fun hmem =>
    match hl f hmem with | ⟨v, hv⟩ => hf v hv)

private theorem g1Data_run_map (l : List Bool) :
    ∀ g ∈ l.map G1Frame.data, ∃ v : Bool, g = G1Frame.data v := by
  intro g hg
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hg
  exact ⟨v, rfl⟩

private theorem g1Data_run_take (l : List Bool) (k : Nat) :
    ∀ g ∈ List.take k (l.map G1Frame.data), ∃ v : Bool, g = G1Frame.data v :=
  fun g hg => g1Data_run_map l g (List.mem_of_mem_take hg)

private theorem g1Data_run_drop (l : List Bool) (k : Nat) :
    ∀ g ∈ List.drop k (l.map G1Frame.data), ∃ v : Bool, g = G1Frame.data v :=
  fun g hg => g1Data_run_map l g (List.mem_of_mem_drop hg)

private theorem g1FieldRoute_count_spent (r : G1Request) :
    (g1FieldRouteFrames r).count G1Frame.spent = 0 := by
  simp [g1FieldRouteFrames, List.count_append,
    g1Count_replicate_ne G1Frame.spent G1Frame.tag r.tag.units (by decide),
    g1Count_replicate_ne G1Frame.spent G1Frame.index r.arg1 (by decide)]

private theorem g1FieldRoute_count_cursor (r : G1Request) :
    (g1FieldRouteFrames r).count G1Frame.cursor = 0 := by
  simp [g1FieldRouteFrames, List.count_append,
    g1Count_replicate_ne G1Frame.cursor G1Frame.tag r.tag.units (by decide),
    g1Count_replicate_ne G1Frame.cursor G1Frame.index r.arg1 (by decide)]

private theorem g1FieldRoute_count_index (r : G1Request) :
    (g1FieldRouteFrames r).count G1Frame.index = r.arg1 := by
  simp [g1FieldRouteFrames, List.count_append,
    g1Count_replicate_ne G1Frame.index G1Frame.tag r.tag.units (by decide)]

/-- **Exactly `arg2 - j` operand-2 units are still unspent.** -/
theorem g1WalkFrames_count_index (r : G1Request) (j : Nat) :
    (g1WalkFrames r j).count G1Frame.index = r.arg1 + (r.arg2 - j) := by
  simp [g1WalkFrames, List.count_append, g1FieldRoute_count_index,
    g1Count_replicate_ne G1Frame.index G1Frame.spent j (by decide),
    g1Count_data_run G1Frame.index _ (g1Data_run_take r.vals j) (by decide),
    g1Count_data_run G1Frame.index _ (g1Data_run_drop r.vals (j + 1))
      (by decide)]

/-- **Exactly `j` operand-2 units are spent.** -/
theorem g1WalkFrames_count_spent (r : G1Request) (j : Nat) :
    (g1WalkFrames r j).count G1Frame.spent = j := by
  simp [g1WalkFrames, List.count_append, g1FieldRoute_count_spent,
    g1Count_replicate_ne G1Frame.spent G1Frame.index (r.arg2 - j) (by decide),
    g1Count_data_run G1Frame.spent _ (g1Data_run_take r.vals j) (by decide),
    g1Count_data_run G1Frame.spent _ (g1Data_run_drop r.vals (j + 1))
      (by decide)]

/-- **The cursor is unique.**  There is exactly one `cursor` frame in `Σ(j)`. -/
theorem g1WalkFrames_count_cursor (r : G1Request) (j : Nat) :
    (g1WalkFrames r j).count G1Frame.cursor = 1 := by
  simp [g1WalkFrames, List.count_append, g1FieldRoute_count_cursor,
    g1Count_replicate_ne G1Frame.cursor G1Frame.index (r.arg2 - j) (by decide),
    g1Count_replicate_ne G1Frame.cursor G1Frame.spent j (by decide),
    g1Count_data_run G1Frame.cursor _ (g1Data_run_take r.vals j) (by decide),
    g1Count_data_run G1Frame.cursor _ (g1Data_run_drop r.vals (j + 1))
      (by decide)]

theorem g1WalkFramesMarked_length (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj : j < r.vals.length) :
    (g1WalkFramesMarked r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp only [g1WalkFramesMarked, List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_map, List.length_take, List.length_drop,
    List.length_cons, List.length_nil]
  omega

theorem g1WalkFramesMarked_count_cursor (r : G1Request) (j : Nat) :
    (g1WalkFramesMarked r j).count G1Frame.cursor = 1 := by
  simp [g1WalkFramesMarked, List.count_append, g1FieldRoute_count_cursor,
    g1Count_replicate_ne G1Frame.cursor G1Frame.index (r.arg2 - j - 1)
      (by decide),
    g1Count_replicate_ne G1Frame.cursor G1Frame.spent (j + 1) (by decide),
    g1Count_data_run G1Frame.cursor _ (g1Data_run_take r.vals j) (by decide),
    g1Count_data_run G1Frame.cursor _ (g1Data_run_drop r.vals (j + 1))
      (by decide)]

theorem g1WalkFramesMarked_count_spent (r : G1Request) (j : Nat) :
    (g1WalkFramesMarked r j).count G1Frame.spent = j + 1 := by
  simp [g1WalkFramesMarked, List.count_append, g1FieldRoute_count_spent,
    g1Count_replicate_ne G1Frame.spent G1Frame.index (r.arg2 - j - 1)
      (by decide),
    g1Count_data_run G1Frame.spent _ (g1Data_run_take r.vals j) (by decide),
    g1Count_data_run G1Frame.spent _ (g1Data_run_drop r.vals (j + 1))
      (by decide)]

theorem g1WalkFramesMarked_count_index (r : G1Request) (j : Nat) :
    (g1WalkFramesMarked r j).count G1Frame.index =
      r.arg1 + (r.arg2 - j - 1) := by
  simp [g1WalkFramesMarked, List.count_append, g1FieldRoute_count_index,
    g1Count_replicate_ne G1Frame.index G1Frame.spent (j + 1) (by decide),
    g1Count_data_run G1Frame.index _ (g1Data_run_take r.vals j) (by decide),
    g1Count_data_run G1Frame.index _ (g1Data_run_drop r.vals (j + 1))
      (by decide)]

/-- **The restored layout carries no cursor at all.** -/
theorem g1WalkFramesRestored_count_cursor (r : G1Request) (j : Nat) :
    (g1WalkFramesRestored r j).count G1Frame.cursor = 0 := by
  simp [g1WalkFramesRestored, List.count_append, g1FieldRoute_count_cursor,
    g1Count_replicate_ne G1Frame.cursor G1Frame.index (r.arg2 - j - 1)
      (by decide),
    g1Count_replicate_ne G1Frame.cursor G1Frame.spent (j + 1) (by decide),
    g1Count_data_run G1Frame.cursor _ (g1Data_run_map r.vals) (by decide)]

/-- **The restored layout is partially spent**: `j + 1` consumed units. -/
theorem g1WalkFramesRestored_count_spent (r : G1Request) (j : Nat) :
    (g1WalkFramesRestored r j).count G1Frame.spent = j + 1 := by
  simp [g1WalkFramesRestored, List.count_append, g1FieldRoute_count_spent,
    g1Count_replicate_ne G1Frame.spent G1Frame.index (r.arg2 - j - 1)
      (by decide),
    g1Count_data_run G1Frame.spent _ (g1Data_run_map r.vals) (by decide)]

/-- **The restored layout is not repaired**: `arg2 - j - 1` units remain. -/
theorem g1WalkFramesRestored_count_index (r : G1Request) (j : Nat) :
    (g1WalkFramesRestored r j).count G1Frame.index =
      r.arg1 + (r.arg2 - j - 1) := by
  simp [g1WalkFramesRestored, List.count_append, g1FieldRoute_count_index,
    g1Count_replicate_ne G1Frame.index G1Frame.spent (j + 1) (by decide),
    g1Count_data_run G1Frame.index _ (g1Data_run_map r.vals) (by decide)]

/-! ### Head safety, on the invariant domain -/

/-- **Every cell a round touches is inside the tape.**  The furthest physical
cell any macro of a round reaches is `4 * (g1WalkCursor r j + 2)`, the frame
boundary just past the probed frame.  The guard `j ≤ arg2` makes
`g1WalkCursor r j` the actual cursor ordinal of `g1WalkFrames r j`. -/
theorem g1WalkCursor_safe (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) :
    4 * (g1WalkCursor r j + 2) < G1M.tapeLength (encodeG1 r).length :=
  g1_route_lt_tapeLength r _ (by simp only [g1WalkCursor]; omega)

/-! ## `Σ(j)`: the canonical walk configuration -/

set_option linter.unusedVariables false in
/-- **`Σ(r, j, v)`: the cursor-walk invariant configuration.**  The tape is
`g1WalkFrames r j`, the head is on the last cell of the frame preceding the
cursor, the control is the reverse seek `bSeek .p3` with an empty frame buffer,
and the context is `g1Ctx0.withVB v`: `pass = crossed = false` and the latched
operand bit `vB = v`.  The two numeric guards and the hidden-bit relation
`vals[j]? = some v` are explicit arguments, so the configuration cannot be
formed outside the invariant's range or with a latch inconsistent with the
cursor-hidden data frame. -/
def g1WalkConfig (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r j - 1)
    (by have := g1WalkCursor_safe r j hj2 hj; omega)
    (g1ListTape ((g1WalkFrames r j).flatMap G1Frame.bits))
    .bSeek .p3 false false false (g1Ctx0.withVB v)

@[simp] theorem g1WalkConfig_tape (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    (g1WalkConfig r j hj2 hj v hv).tape =
      g1ListTape ((g1WalkFrames r j).flatMap G1Frame.bits) := rfl

@[simp] theorem g1WalkConfig_head (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    ((g1WalkConfig r j hj2 hj v hv).head : Nat) =
      4 * g1WalkCursor r j - 1 := rfl

@[simp] theorem g1WalkConfig_state (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    (g1WalkConfig r j hj2 hj v hv).state.snd =
      g1State .bSeek .p3 false false false (g1Ctx0.withVB v) := rfl

/-- **The latched bit is the one the cursor is hiding.** -/
theorem g1WalkConfig_vB (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    (g1WalkConfig r j hj2 hj v hv).state.snd.ctx.vB = v := rfl

/-- **The invariant records the data bit hidden by the cursor.** -/
theorem g1WalkConfig_hidden (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    r.vals[j]? = some v := hv

/-! ## Installation: from the real initial configuration into `Σ(0)`

The installation is the merged read-only scan of `GateOneInstallScan` followed
by the probe/latch of `vals[0]` and the leftward cursor install of
`GateOneProbeInstall`: nine more genuine steps.  It writes exactly one frame,
`data vals[0] ↦ cursor`. -/

/-- Steps from `initialConfig` to `Σ(0)`: the installation scan, the probe and
latch of `vals[0]` (`5`) and the cursor install (`4`). -/
def g1WalkInstallSteps (r : G1Request) : Nat := g1InstallScanSteps r + 9

/-- Steps from `initialConfig` to the **empty-data** out-of-range boundary: the
installation scan and the probe that meets the `output` destination. -/
def g1WalkEmptyOOBSteps (r : G1Request) : Nat := g1InstallScanSteps r + 4

theorem g1WalkInstallSteps_eq (r : G1Request) :
    g1WalkInstallSteps r = g1FieldRouteSteps r + 4 * (r.arg2 + 1) + 9 := by
  simp only [g1WalkInstallSteps, g1InstallScanSteps_eq]

theorem g1WalkEmptyOOBSteps_eq (r : G1Request) :
    g1WalkEmptyOOBSteps r =
      g1FieldRouteSteps r + 4 * (r.arg2 + 1) + 4 := by
  simp only [g1WalkEmptyOOBSteps, g1InstallScanSteps_eq]

/-- **The installation fits the unchanged public clock**; `g1Clock` is not
widened. -/
theorem g1WalkInstallSteps_le_clock (r : G1Request) :
    g1WalkInstallSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + r.arg1 + r.arg2 + 6)
    (by omega)
  simp only [g1WalkInstallSteps, g1InstallScanSteps]
  omega

theorem g1WalkEmptyOOBSteps_le_clock (r : G1Request) :
    g1WalkEmptyOOBSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + r.arg1 + r.arg2 + 5)
    (by omega)
  simp only [g1WalkEmptyOOBSteps, g1InstallScanSteps]
  omega

private theorem g1InstallSplit_probe (r : G1Request) (v : Bool)
    (rest : List Bool) (hv : r.vals = v :: rest) :
    g1InstallRouteFrames r ++ G1Frame.data v :: (rest.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      encodeG1Frames r ++ [G1Frame.blank] := by
  rw [← g1InstallRoute_split r, g1InstallRouteRest, hv]
  simp

private theorem g1InstallSplit_oob (r : G1Request) (hv : r.vals = []) :
    g1InstallRouteFrames r ++
        G1Frame.output false :: [G1Frame.finish, G1Frame.blank] =
      encodeG1Frames r ++ [G1Frame.blank] := by
  rw [← g1InstallRoute_split r, g1InstallRouteRest, hv]
  simp

private theorem g1InstallSplit_zero (r : G1Request) (v : Bool)
    (rest : List Bool) (hv : r.vals = v :: rest) :
    g1InstallRouteFrames r ++ G1Frame.cursor :: (rest.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1WalkFrames r 0 := by
  rw [g1WalkFrames, g1InstallRouteFrames, hv]
  simp [List.append_assoc]

private theorem g1WalkCursor_zero (r : G1Request) :
    r.tag.units + r.arg1 + r.arg2 + 4 = g1WalkCursor r 0 := by
  simp only [g1WalkCursor]

private theorem g1InstallPre_length (r : G1Request) :
    (g1InstallRouteFrames r).length = g1WalkCursor r 0 := by
  rw [g1InstallRouteFrames_length]
  simp only [g1WalkCursor]

private theorem g1WalkInit_tape (r : G1Request) :
    (G1M.initialConfig (g1Point (encodeG1 r))).tape =
      g1ListTape (n := (encodeG1 r).length)
        ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits) := by
  rw [← g1ListTape_validation_eq_initial r]; rfl

/-- **From the real initial configuration into `Σ(0)`, exactly.**  For a
canonical `and`/`or` request with a non-empty operand-2 field (`arg2 = k + 1`)
and a non-empty data region (`vals[0]? = some v`), exactly
`g1WalkInstallSteps r` genuine steps validate the word, rewind, physically
rescan the tag, skip both operand fields, cross the `separator`, probe the first
data frame, latch its bit into `G1Ctx.vB` and install the cursor over it —
landing exactly on the walk invariant `Σ(r, 0, v)`.

Only one frame is written: `data vals[0] ↦ cursor`.  The run stops **on**
`Σ(0)`: no round is executed, and nothing here claims which data frame the
operand selects. -/
theorem g1CS_walk_install_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r) =
      g1WalkConfig r 0 (by omega) (g1Length_pos_of_get hv) v hv := by
  have hm : 0 < r.vals.length := g1Length_pos_of_get hv
  have hTL := g1WalkCursor_safe r 0 (Nat.zero_le _) hm
  have hLpre := g1InstallPre_length r
  obtain ⟨rest, hvals⟩ := g1Vals_cons hv
  -- The installation scan, from `initialConfig`, in list-backed form.
  have hA : TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1InstallScanSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r 0) (by omega)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.data v ::
            (rest.map G1Frame.data ++
              [G1Frame.output false, G1Frame.finish, G1Frame.blank])).flatMap
            G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0 := by
    have h := g1CS_readB_install_scan_exact r hc ht k h2
    rw [g1WalkInit_tape r, ← g1InstallSplit_probe r v rest hvals] at h
    simpa only [g1WalkCursor_zero r] using h
  -- Probe and latch of `vals[0]`.
  have hB : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r 0) (by omega)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.data v ::
            (rest.map G1Frame.data ++
              [G1Frame.output false, G1Frame.finish, G1Frame.blank])).flatMap
            G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 5 =
      g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r 0 + 3)
        (by omega)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.data v ::
            (rest.map G1Frame.data ++
              [G1Frame.output false, G1Frame.finish, G1Frame.blank])).flatMap
            G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_probe_latch (encodeG1 r).length
      (g1InstallRouteFrames r)
      (rest.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      v g1Ctx0 (by rw [hLpre]; omega)
    simp only [hLpre] at h
    exact h
  -- The cursor install, leftward, onto data slot `0`.
  have hC : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r 0 + 3)
        (by omega)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.data v ::
            (rest.map G1Frame.data ++
              [G1Frame.output false, G1Frame.finish, G1Frame.blank])).flatMap
            G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB v)) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r 0 - 1) (by omega)
        (g1ListTape ((g1WalkFrames r 0).flatMap G1Frame.bits))
        .bSeek .p3 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_install_cursor (encodeG1 r).length
      (g1InstallRouteFrames r)
      (rest.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      (G1Frame.data v) (g1Ctx0.withVB v)
      (by rw [hLpre]; simp only [g1WalkCursor]; omega)
      (by rw [hLpre]; omega)
    rw [g1InstallSplit_zero r v rest hvals] at h
    simp only [hLpre] at h
    exact h
  simp only [g1WalkInstallSteps]
  rw [show g1InstallScanSteps r + 9 = g1InstallScanSteps r + (5 + 4) from by omega,
    runConfig_add, hA, runConfig_add, hB, hC, g1WalkConfig]

/-- **The empty-data out-of-range branch, from the real initial
configuration.**  For a canonical `and`/`or` request with `arg2 = k + 1` and an
**empty** data region, the installation scan reaches the walk probe and finds
the `output false` destination frame instead of a data frame: after exactly
`g1WalkEmptyOOBSteps r` genuine steps the machine sits in the stable
out-of-range boundary `bOOB`, head `4 * (g1WalkCursor r 0 + 1)`, and the tape is
**bit-for-bit the initial tape** — the whole branch is read-only, so no `spent`
marker and no `cursor` is left anywhere.  Nothing is stored in `vB`. -/
theorem g1CS_walk_install_oob_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r 0 + 1))
        (g1_route_lt_tapeLength r _ (by simp only [g1WalkCursor]; omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bOOB .p0 false false false g1Ctx0 := by
  have hTL : 4 * (g1WalkCursor r 0 + 1) < G1M.tapeLength (encodeG1 r).length :=
    g1_route_lt_tapeLength r _ (by simp only [g1WalkCursor]; omega)
  have hLpre := g1InstallPre_length r
  have hA : TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1InstallScanSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r 0) (by omega)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.output false ::
            [G1Frame.finish, G1Frame.blank]).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0 := by
    have h := g1CS_readB_install_scan_exact r hc ht k h2
    rw [g1WalkInit_tape r, ← g1InstallSplit_oob r hv] at h
    simpa only [g1WalkCursor_zero r] using h
  have hB : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r 0) (by omega)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.output false ::
            [G1Frame.finish, G1Frame.blank]).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r 0 + 1))
        (by omega)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.output false ::
            [G1Frame.finish, G1Frame.blank]).flatMap G1Frame.bits))
        .bOOB .p0 false false false g1Ctx0 := by
    have h := g1CS_walk_probe_oob (encodeG1 r).length (g1InstallRouteFrames r)
      [G1Frame.finish, G1Frame.blank] g1Ctx0 (by rw [hLpre]; omega)
    simp only [hLpre,
      show 4 * g1WalkCursor r 0 + 4 = 4 * (g1WalkCursor r 0 + 1) from
        by omega] at h
    exact h
  simp only [g1WalkEmptyOOBSteps]
  rw [runConfig_add, hA, hB, g1InstallSplit_oob r hv, ← g1WalkInit_tape r]

/-- **The empty-data out-of-range boundary is stable.** -/
theorem g1CS_walk_install_oob_stable (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) (n : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r + n) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r 0 + 1))
        (g1_route_lt_tapeLength r _ (by simp only [g1WalkCursor]; omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bOOB .p0 false false false g1Ctx0 := by
  rw [runConfig_add, g1CS_walk_install_oob_exact r hc ht k h2 hv]
  exact g1CS_runConfig_oob_sink _ _ _ _ _ n

/-- **The empty-data branch is non-destructive.**  Not a single tape cell
changes. -/
theorem g1CS_walk_install_oob_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_walk_install_oob_exact r hc ht k h2 hv]; rfl

theorem g1CS_walk_install_oob_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r)).head : Nat) = 4 * (g1WalkCursor r 0 + 1) := by
  rw [g1CS_walk_install_oob_exact r hc ht k h2 hv]; rfl

theorem g1CS_walk_install_oob_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r)).state.snd = g1OOBState g1Ctx0 := by
  rw [g1CS_walk_install_oob_exact r hc ht k h2 hv]; rfl

/-! ### Projections of the installation capstone -/

theorem g1CS_walk_install_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).head : Nat) = 4 * g1WalkCursor r 0 - 1 := by
  rw [g1CS_walk_install_exact r hc ht k h2 v hv]; rfl

theorem g1CS_walk_install_vB (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).state.snd.ctx.vB = v := by
  rw [g1CS_walk_install_exact r hc ht k h2 v hv]; rfl

theorem g1CS_walk_install_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).tape =
      g1ListTape ((g1WalkFrames r 0).flatMap G1Frame.bits) := by
  rw [g1CS_walk_install_exact r hc ht k h2 v hv]; rfl

theorem g1CS_walk_install_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).state.snd =
      g1State .bSeek .p3 false false false (g1Ctx0.withVB v) := by
  rw [g1CS_walk_install_exact r hc ht k h2 v hv]; rfl

/-- **Success and out-of-range are different boundaries.**  The empty-data
branch ends in `bOOB`, which is not the reverse-seek entry of `Σ(0)`. -/
theorem g1CS_walk_oob_ne_invariant (ctx ctx' : G1Ctx) :
    g1OOBState ctx ≠ g1State .bSeek .p3 false false false ctx' := by
  intro h
  have hmode : G1Mode.bOOB = G1Mode.bSeek := congrArg G1State.mode h
  exact absurd hmode (by decide)

end Pnp3.Internal.PsubsetPpoly.TM
