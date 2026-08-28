import Complexity.TMVerifier.TuringToolkit.GateOneWalkKernel

/-!
# G1 cursor walk: the tape invariant `Σ(j)` and its real installation

**Progress classification: Infrastructure.**

PR3a.  The merged atomic macros hold on **arbitrary** frame lists; this module
pins the **one canonical frame list** the cursor walk runs on and reaches it
from the **real initial configuration** `G1M.initialConfig`.

PR3b adds **exactly one round** on that frame list, in both of its outcomes —
the normal step `Σ(j) → Σ(j+1)` and the out-of-range abort at the last data
slot — and nothing beyond it **in this module**.  The induction, driver and
loop clock are supplied separately by `GateOneWalkDriver`.

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
round passes through.  Both carry exact length/count facts, and PR3b's round
theorems below really do write them: the marked word is the tape between the
`index ↦ spent` write and the cursor restore, the restored word the tape from
the restore onwards.

## What is executed here

The **installation** from `G1M.initialConfig`, and **one round** on `Σ(j)`.

One round, from a caller-supplied `Σ(j)` (no run below reaches `Σ(j)` for
`j > 0` from `initialConfig`; that composition needs the induction, which is
deferred):

* `g1CS_walk_iteration_exact` — for `j < a2` and `j + 1 < m`, exactly
  `16 * j + 37` genuine steps take `Σ(r, j, v)` to `Σ(r, j+1, v')`, where the
  hidden-bit proofs `vals[j]? = some v` and `vals[j+1]? = some v'` are
  **arguments of the two configurations**: the relation is explicit at the start
  and re-established at the endpoint.  One on-tape decrement
  (`index^(a2-j) · spent^j ↦ index^(a2-j-1) · spent^(j+1)`), the unique cursor
  moves one data slot right, slot `j` is restored to `data vals[j]`, everything
  else is unchanged.
* `g1CS_walk_oob_exact` / `g1CS_walk_oob_stable` — for `j < a2` but
  `j + 1 = m`, exactly `16 * j + 32` steps reach the **stable** `bOOB` boundary
  on `g1WalkFramesRestored r j`: the data region is exactly `vals` and
  cursor-free, while operand 2 is **partially spent and unrepaired**
  (`spent^(j+1)`, `index^(a2-j-1)` left).  This is an intermediate tape and
  **not** a rejection: no output write, verdict or `TM.accepts` result is claimed.

Only the **installation** starts from `G1M.initialConfig`:

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

Both installation counts stay inside the unchanged public clock `g1Clock`; no
new `Nat`, index, width, offset or request field is introduced anywhere.  The
installation capstones are composed from the merged `GateOneInstallScan` and
`GateOneProbeInstall` atoms, and the round from the merged `GateOneWalkKernel`
and `GateOneProbeInstall` atoms; the transition table is never unfolded.
`GateOneWalkKernel` also supplies the single name `G1WalkSkip`, in whose terms
the two pure skip-run facts above are stated.

## Scope of this module

Exactly **one** round is executed, and only from a `Σ(j)` the caller hands in.
There is **no** induction over `j`, no driver, no loop and **no cumulative or
per-round clock bound** — `16 * j + 37` and `16 * j + 32` are stated but never
summed or compared against `g1Clock`.  There is no successful terminal at
`j = a2` (the `bExh`/`bRet`/`bTurnFin`/`bFin` path into `readAResetStart`), no
aggregation of the two out-of-range branches, no addressing and **no
positive-index operand-value theorem**: nothing below claims the machine
resolves `r.vals[r.arg2]?` for `a2 > 0`.  All five are `GateOneWalkDriver`
(PR3c), which composes exactly the capstones above and adds no new machine
fact.  Absent everywhere: the `spent ↦ index`
repair sweep, pass A, combine, the output write, `TM.accepts`, gate-semantics
correctness, a full-clock theorem and non-canonical or physically padded tapes.
As everywhere in this development, every execution statement is scoped to the
exact tape `encodeG1 r`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## List helpers -/

private theorem g1Drop_cons (l : List Bool) (j : Nat) (hj : j < l.length) :
    l.drop j = l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => exact ih j (by simpa using hj)

private theorem g1Replicate_split (m : Nat) (hm : 0 < m) (f : G1Frame) :
    List.replicate m f = List.replicate (m - 1) f ++ [f] := by
  obtain ⟨m, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  simp [List.replicate_succ']

/-- The hidden-bit relation `vals[j]? = some v` in `getElem` form.  Everything
below reads the invariant's latch through this equation, so the bit written back
by a round's restore is the bit the cursor was hiding. -/
private theorem g1Getn {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) (hj : j < l.length) : l[j] = v := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

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
more `spent` marker, cursor still on data slot `j`.  The private round prefix
passes through this tape, but no public capstone exposes it as a final endpoint. -/
def g1WalkFramesMarked (r : G1Request) (j : Nat) : List G1Frame :=
  g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
    List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
    (r.vals.take j).map G1Frame.data ++ [G1Frame.cursor] ++
    (r.vals.drop (j + 1)).map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The layout *after* the cursor restore and before the next probe: the data
region is exactly `vals` and carries no cursor, while the operand-2 field is
partially spent, `index^(arg2-j-1) · spent^(j+1)`.  The private round prefix
reaches this tape after restore, and the public OOB capstone ends on it. -/
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

theorem g1WalkFramesRestored_length (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) :
    (g1WalkFramesRestored r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp only [g1WalkFramesRestored, List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_map, List.length_cons, List.length_nil]
  omega

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

/-! ### Layout splits

Each split is a pure re-association of the three layout definitions above, in
exactly the shape one atomic macro of `GateOneWalkKernel` or
`GateOneProbeInstall` consumes.  No execution claim is involved, and no
transition row is unfolded. -/

private theorem g1WalkSplit_mark (r : G1Request) (j : Nat) (hj2 : j < r.arg2) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index) ++
        G1Frame.index :: (List.replicate j G1Frame.spent ++
          [G1Frame.separator] ++ (r.vals.take j).map G1Frame.data) ++
        (G1Frame.cursor :: ((r.vals.drop (j + 1)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank])) =
      g1WalkFrames r j := by
  rw [g1WalkFrames, g1Replicate_split (r.arg2 - j) (by omega) G1Frame.index]
  simp [List.append_assoc]

private theorem g1WalkSplit_marked_mark (r : G1Request) (j : Nat) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index) ++
        G1Frame.spent :: (List.replicate j G1Frame.spent ++
          [G1Frame.separator] ++ (r.vals.take j).map G1Frame.data) ++
        (G1Frame.cursor :: ((r.vals.drop (j + 1)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank])) =
      g1WalkFramesMarked r j := by
  rw [g1WalkFramesMarked, List.replicate_succ]
  simp [List.append_assoc]

private theorem g1WalkSplit_marked_fwd (r : G1Request) (j : Nat) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        [G1Frame.spent]) ++
        (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
          (r.vals.take j).map G1Frame.data) ++
        G1Frame.cursor :: ((r.vals.drop (j + 1)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1WalkFramesMarked r j := by
  rw [g1WalkFramesMarked, List.replicate_succ]
  simp [List.append_assoc]

private theorem g1WalkSplit_marked_cursor (r : G1Request) (j : Nat) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take j).map G1Frame.data) ++
        G1Frame.cursor :: ((r.vals.drop (j + 1)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1WalkFramesMarked r j := by
  simp [g1WalkFramesMarked, List.append_assoc]

/-- **The restore writes back exactly the hidden bit.**  The `data v` frame the
round puts at ordinal `g1WalkCursor r j` re-creates the data region `vals`
precisely because `v` is `vals[j]`; this is where the invariant's hidden-bit
relation is consumed. -/
private theorem g1WalkSplit_restored_cursor (r : G1Request) (j : Nat) (v : Bool)
    (hj : j < r.vals.length) (hv : r.vals[j] = v) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take j).map G1Frame.data) ++
        G1Frame.data v :: ((r.vals.drop (j + 1)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1WalkFramesRestored r j := by
  have hd : r.vals.map G1Frame.data =
      (r.vals.take j).map G1Frame.data ++
        G1Frame.data v :: (r.vals.drop (j + 1)).map G1Frame.data := by
    conv_lhs => rw [← List.take_append_drop j r.vals]
    rw [List.map_append, g1Drop_cons r.vals j hj, hv]
    simp
  rw [g1WalkFramesRestored, hd]
  simp [List.append_assoc]

/-- **The next probe reads exactly `vals[j+1]`.**  The same restored word, split
one frame further right; this is where the *next* round's hidden-bit relation is
produced. -/
private theorem g1WalkSplit_restored_probe (r : G1Request) (j : Nat) (v' : Bool)
    (hj1 : j + 1 < r.vals.length) (hv' : r.vals[j + 1] = v') :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take (j + 1)).map G1Frame.data) ++
        G1Frame.data v' :: ((r.vals.drop (j + 2)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1WalkFramesRestored r j := by
  have hd : r.vals.map G1Frame.data =
      (r.vals.take (j + 1)).map G1Frame.data ++
        G1Frame.data v' :: (r.vals.drop (j + 2)).map G1Frame.data := by
    conv_lhs => rw [← List.take_append_drop (j + 1) r.vals]
    rw [List.map_append, g1Drop_cons r.vals (j + 1) hj1, hv']
    simp
  rw [g1WalkFramesRestored, hd]
  simp [List.append_assoc]

/-- **The out-of-range split.**  When slot `j` was the last one, the frame the
next probe meets is the `output false` destination, not a data frame. -/
private theorem g1WalkSplit_restored_oob (r : G1Request) (j : Nat)
    (hj1 : j + 1 = r.vals.length) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take (j + 1)).map G1Frame.data) ++
        G1Frame.output false :: [G1Frame.finish, G1Frame.blank] =
      g1WalkFramesRestored r j := by
  have htake : r.vals.take (j + 1) = r.vals := by rw [hj1]; simp
  rw [g1WalkFramesRestored, htake]

private theorem g1WalkSplit_succ (r : G1Request) (j : Nat) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take (j + 1)).map G1Frame.data) ++
        G1Frame.cursor :: ((r.vals.drop (j + 2)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1WalkFrames r (j + 1) := by
  rw [g1WalkFrames, show r.arg2 - (j + 1) = r.arg2 - j - 1 from by omega]
  simp [List.append_assoc]

/-! ### Layout lengths used by the round proof

Each pins the frame ordinal a macro's `pre` ends at, so the head positions the
macros produce are the invariant's own, not free parameters. -/

private theorem g1MarkPre_length (r : G1Request) (j : Nat) :
    (g1FieldRouteFrames r ++
      List.replicate (r.arg2 - j - 1) G1Frame.index).length =
      r.tag.units + r.arg1 + 3 + (r.arg2 - j - 1) := by
  simp only [List.length_append, g1FieldRouteFrames_length,
    List.length_replicate]

private theorem g1SkipRun_length (r : G1Request) (j : Nat)
    (hj : j ≤ r.vals.length) :
    (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
      (r.vals.take j).map G1Frame.data).length = 2 * j + 1 := by
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.length_map, List.length_take]
  omega

private theorem g1FwdPre_length (r : G1Request) (j : Nat) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
      [G1Frame.spent]).length = r.tag.units + r.arg1 + 4 + (r.arg2 - j - 1) := by
  simp only [List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem g1CursorPre_length (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj : j < r.vals.length) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
      List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
      (r.vals.take j).map G1Frame.data).length = g1WalkCursor r j := by
  simp only [List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_cons, List.length_nil, List.length_map,
    List.length_take, g1WalkCursor]
  omega

private theorem g1ProbePre_length (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj1 : j + 1 ≤ r.vals.length) :
    (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
      List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
      (r.vals.take (j + 1)).map G1Frame.data).length =
      g1WalkCursor r j + 1 := by
  simp only [List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_cons, List.length_nil, List.length_map,
    List.length_take, g1WalkCursor]
  omega

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

private theorem g1Ctx0_withVB_withVB (v v' : Bool) :
    (g1Ctx0.withVB v).withVB v' = g1Ctx0.withVB v' := rfl

/-! ## The shared prefix of a round

Phases A–D: the reverse seek with its `index ↦ spent` write, the forward scan
back to the cursor, the turn and the cursor restore.  They are identical for the
data outcome and for the out-of-range outcome, which differ only in the frame
the following probe reads.  Every hypothesis the merged macros take is supplied
from the structural theorems above — `g1WalkSkipRun_mem` for both scans, the
`g1*_length` splits for the head positions, `g1WalkCursor_safe` for the tape
bound — and the hidden-bit relation of `Σ(j)` is what makes the restored word
`g1WalkFramesRestored r j` rather than an arbitrary one. -/

set_option maxHeartbeats 1000000 in
private theorem g1CS_walk_prefix_exact (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    TM.runConfig (M := G1M) (g1WalkConfig r j (by omega) hj v hv)
        (16 * j + 28) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1))
        (by have := g1WalkCursor_safe r j (by omega) hj; omega)
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false (g1Ctx0.withVB v) := by
  have hdv : r.vals[j] = v := g1Getn hv hj
  have hTL := g1WalkCursor_safe r j (by omega) hj
  have hTLe : 4 * (r.tag.units + r.arg1 + r.arg2 + j + 6) <
      G1M.tapeLength (encodeG1 r).length := by
    simpa only [g1WalkCursor] using hTL
  have hLmark := g1MarkPre_length r j
  have hLskip := g1SkipRun_length r j (by omega)
  have hLfwd := g1FwdPre_length r j
  have hLcur := g1CursorPre_length r j hj2 hj
  -- Phase A: reverse seek across `spent^j · separator · data^j`, then the
  -- `index ↦ spent` write of the rightmost unspent unit.
  have hA : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r j - 1)
        (by omega) (g1ListTape ((g1WalkFrames r j).flatMap G1Frame.bits))
        .bSeek .p3 false false false (g1Ctx0.withVB v)) (8 * j + 12) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + 4 + (r.arg2 - j - 1))) (by omega)
        (g1ListTape ((g1WalkFramesMarked r j).flatMap G1Frame.bits))
        .bFwd .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_seek_mark (encodeG1 r).length
      (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index)
      (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take j).map G1Frame.data)
      (G1Frame.cursor :: ((r.vals.drop (j + 1)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank]))
      (g1Ctx0.withVB v) (g1WalkSkipRun_mem j r.vals)
      (by rw [hLmark, hLskip]; simp only [g1WalkCursor] at hTL; omega)
    rw [g1WalkSplit_mark r j hj2, g1WalkSplit_marked_mark r j] at h
    simp only [hLmark, hLskip,
      show 4 * (r.tag.units + r.arg1 + 3 + (r.arg2 - j - 1) + (2 * j + 1)) + 3 =
        4 * g1WalkCursor r j - 1 from by simp only [g1WalkCursor]; omega,
      show 4 * (r.tag.units + r.arg1 + 3 + (r.arg2 - j - 1)) + 4 =
        4 * (r.tag.units + r.arg1 + 4 + (r.arg2 - j - 1)) from by omega,
      show 4 * (2 * j + 1) + 8 = 8 * j + 12 from by omega] at h
    exact h
  -- Phase B: the forward scan back to the cursor.
  have hB : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + 4 + (r.arg2 - j - 1))) (by omega)
        (g1ListTape ((g1WalkFramesMarked r j).flatMap G1Frame.bits))
        .bFwd .p0 false false false (g1Ctx0.withVB v)) (8 * j + 8) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1))
        (by omega)
        (g1ListTape ((g1WalkFramesMarked r j).flatMap G1Frame.bits))
        .bTurn .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_fwd_to_cursor (encodeG1 r).length
      (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        [G1Frame.spent])
      (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take j).map G1Frame.data)
      ((r.vals.drop (j + 1)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      (g1Ctx0.withVB v) (g1WalkSkipRun_mem j r.vals)
      (by rw [hLfwd, hLskip]; simp only [g1WalkCursor] at hTL; omega)
    rw [g1WalkSplit_marked_fwd r j] at h
    simp only [hLfwd, hLskip,
      show r.tag.units + r.arg1 + 4 + (r.arg2 - j - 1) + (2 * j + 1 + 1) =
        g1WalkCursor r j + 1 from by simp only [g1WalkCursor]; omega,
      show 4 * (2 * j + 1 + 1) = 8 * j + 8 from by omega] at h
    exact h
  -- Phase C: the turn back onto the cursor frame.
  have hC : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1))
        (by omega)
        (g1ListTape ((g1WalkFramesMarked r j).flatMap G1Frame.bits))
        .bTurn .p0 false false false (g1Ctx0.withVB v)) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r j) (by omega)
        (g1ListTape ((g1WalkFramesMarked r j).flatMap G1Frame.bits))
        (g1RestoreMode v) .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_turn (encodeG1 r).length (4 * g1WalkCursor r j)
      (by omega)
      (g1ListTape (n := (encodeG1 r).length)
        ((g1WalkFramesMarked r j).flatMap G1Frame.bits)) (g1Ctx0.withVB v)
    simpa only [show 4 * g1WalkCursor r j + 4 = 4 * (g1WalkCursor r j + 1) from
      by omega, G1Ctx.withVB_vB] using h
  -- Phase D: the cursor restore, `cursor ↦ data vals[j]`.
  have hD : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r j) (by omega)
        (g1ListTape ((g1WalkFramesMarked r j).flatMap G1Frame.bits))
        (g1RestoreMode v) .p0 false false false (g1Ctx0.withVB v)) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1))
        (by omega)
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_restore (encodeG1 r).length
      (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take j).map G1Frame.data)
      ((r.vals.drop (j + 1)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      v (g1Ctx0.withVB v)
      (by rw [hLcur]; omega)
    rw [g1WalkSplit_marked_cursor r j,
      g1WalkSplit_restored_cursor r j v hj hdv] at h
    simp only [hLcur,
      show 4 * g1WalkCursor r j + 4 = 4 * (g1WalkCursor r j + 1) from
        by omega] at h
    exact h
  simp only [g1WalkConfig]
  rw [show 16 * j + 28 = (8 * j + 12) + ((8 * j + 8) + (4 + 4)) from by omega,
    runConfig_add, hA, runConfig_add, hB, runConfig_add, hC, hD]

/-! ## The one-round theorems

Exactly **one** round, in both of its outcomes.  Nothing below iterates, sums a
loop clock or reaches a successful terminal. -/

/-- **One genuine round of the cursor walk.**  For `j < arg2` (an operand-2 unit
is still unspent) and `j + 1 < vals.length` (the data region has a next slot),
the machine runs from `Σ(r, j, v)` with `vals[j]? = some v` to `Σ(r, j+1, v')`
with `vals[j+1]? = some v'` in exactly `16 * j + 37` genuine `TM.runConfig`
steps.  Both hidden-bit proofs are **arguments of the two configurations**, so
the invariant's latch relation is explicit at the start *and* at the endpoint:
the round re-establishes it rather than assuming it away.

Both sides are the canonical layout at their own `j`, so the statement pins the
*whole* tape: the operand-2 field's `index^(arg2-j) · spent^j` becomes
`index^(arg2-j-1) · spent^(j+1)` — one on-tape decrement and no other change —
the cursor, which is unique (`g1WalkFrames_count_cursor`), moves from data slot
`j` to data slot `j+1`, slot `j` is restored to `data vals[j]`, and the `bof`
anchor, the tag run, the whole operand-1 field, the `argSep`s, the `separator`,
the untouched data slots, the `output` frame, the `finish` frame and the blank
frame are all unchanged.  The head returns to the last cell before the new
cursor and the context is `g1Ctx0.withVB vals[j+1]`.

The six atomic macros composed are `g1CS_walk_seek_mark` (`8j + 12`),
`g1CS_walk_fwd_to_cursor` (`8j + 8`), `g1CS_walk_turn` (`4`),
`g1CS_walk_restore` (`4`), `g1CS_walk_probe_latch` (`5`) and
`g1CS_walk_install_cursor` (`4`); the transition table is never unfolded.  This
is one round only: there is no induction over `j` and no driver here. -/
theorem g1CS_walk_iteration_exact (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj1 : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    TM.runConfig (M := G1M)
        (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 37) =
      g1WalkConfig r (j + 1) (by omega) hj1 v' hv' := by
  have hj : j < r.vals.length := by omega
  have hdv' : r.vals[j + 1] = v' := g1Getn hv' hj1
  have hTL := g1WalkCursor_safe r j (by omega) hj
  have hTL' := g1WalkCursor_safe r (j + 1) (by omega) hj1
  have hLprobe := g1ProbePre_length r j hj2 (by omega)
  have hCsucc : g1WalkCursor r (j + 1) = g1WalkCursor r j + 1 := by
    simp only [g1WalkCursor]; omega
  -- Phase E: the probe of the next data frame latches `vals[j+1]`.
  have hE : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1))
        (by omega)
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false (g1Ctx0.withVB v)) 5 =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1) + 3)
        (by omega)
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB v') := by
    have h := g1CS_walk_probe_latch (encodeG1 r).length
      (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take (j + 1)).map G1Frame.data)
      ((r.vals.drop (j + 2)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      v' (g1Ctx0.withVB v)
      (by rw [hLprobe]; omega)
    rw [g1WalkSplit_restored_probe r j v' hj1 hdv'] at h
    simp only [hLprobe, g1Ctx0_withVB_withVB] at h
    exact h
  -- Phase F: the new cursor is installed, leftward, over data slot `j + 1`.
  have hF : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1) + 3)
        (by omega)
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB v')) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1) - 1)
        (by omega)
        (g1ListTape ((g1WalkFrames r (j + 1)).flatMap G1Frame.bits))
        .bSeek .p3 false false false (g1Ctx0.withVB v') := by
    have h := g1CS_walk_install_cursor (encodeG1 r).length
      (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take (j + 1)).map G1Frame.data)
      ((r.vals.drop (j + 2)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      (G1Frame.data v') (g1Ctx0.withVB v')
      (by rw [hLprobe]; omega) (by rw [hLprobe]; omega)
    rw [g1WalkSplit_restored_probe r j v' hj1 hdv', g1WalkSplit_succ r j] at h
    simp only [hLprobe] at h
    exact h
  rw [show 16 * j + 37 = (16 * j + 28) + (5 + 4) from by omega, runConfig_add,
    g1CS_walk_prefix_exact r j hj2 hj v hv, runConfig_add, hE, hF]
  simp only [g1WalkConfig, hCsucc]

/-- **The genuine out-of-range round.**  For `j < arg2` but `j + 1 = vals.length`
(the cursor is on the *last* data frame while an operand-2 unit is still
unspent), the machine runs from `Σ(r, j, v)` with `vals[j]? = some v` to the
explicit **stable** out-of-range boundary `bOOB` in exactly `16 * j + 32`
genuine steps.

The final tape is stated exactly, as `g1WalkFramesRestored r j`:

```text
bof · tag^u · argSep · index^a1 · argSep
    · index^(a2-j-1) · spent^(j+1) · separator
    · data(vals) · output false · finish · blank
```

so the *data region is fully restored to `vals` and carries no `cursor` frame*
(`g1WalkFramesRestored_count_cursor`), while the *operand-2 field is not
repaired*: `j + 1` units are spent and `arg2 - j - 1` remain
(`g1WalkFramesRestored_count_spent`, `_count_index`).  This is an
**intermediate, unrepaired** tape, not a repaired one, and reaching `bOOB` is
**not** a rejection theorem: nothing here claims an output write, verdict or
`TM.accepts` result.  The head is left on the frame boundary just past the
`output` destination and the context still carries `vB = vals[j]`. -/
theorem g1CS_walk_oob_exact (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj1 : j + 1 = r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    TM.runConfig (M := G1M)
        (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 32) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 2))
        (g1WalkCursor_safe r j (by omega) (by omega))
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1Ctx0.withVB v) := by
  have hj : j < r.vals.length := by omega
  have hTL := g1WalkCursor_safe r j (by omega) hj
  have hLprobe := g1ProbePre_length r j hj2 (by omega)
  have hE : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 1))
        (by omega)
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false (g1Ctx0.withVB v)) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 2))
        (by omega)
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_probe_oob (encodeG1 r).length
      (g1FieldRouteFrames r ++ List.replicate (r.arg2 - j - 1) G1Frame.index ++
        List.replicate (j + 1) G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take (j + 1)).map G1Frame.data)
      [G1Frame.finish, G1Frame.blank] (g1Ctx0.withVB v)
      (by rw [hLprobe]; omega)
    rw [g1WalkSplit_restored_oob r j hj1] at h
    simp only [hLprobe,
      show 4 * (g1WalkCursor r j + 1) + 4 = 4 * (g1WalkCursor r j + 2) from
        by omega] at h
    exact h
  rw [show 16 * j + 32 = (16 * j + 28) + 4 from by omega, runConfig_add,
    g1CS_walk_prefix_exact r j hj2 hj v hv, hE]

/-- **The out-of-range boundary of a round is stable.**  Every further step
leaves the same configuration, on the same unrepaired tape; still no verdict is
claimed. -/
theorem g1CS_walk_oob_stable (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj1 : j + 1 = r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 32 + k) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r j + 2))
        (g1WalkCursor_safe r j (by omega) (by omega))
        (g1ListTape ((g1WalkFramesRestored r j).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1Ctx0.withVB v) := by
  rw [runConfig_add, g1CS_walk_oob_exact r j hj2 hj1 v hv]
  exact g1CS_runConfig_oob_sink _ _ _ _ _ k

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
