import Complexity.TMVerifier.TuringToolkit.GateOneAWalkKernel

/-!
# S5 operand-A post-install invariant foundation (2026-08-29)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

This module defines the exact canonical operand-A walk layout \`Σᴬ(j)\` for the
current frame ABI and reject-aware control.  With \`u = tag.units\`,
\`a1 = arg1\` and \`a2 = arg2\`, its frame word is

\`\`\`text
bof · tag^u · argSep
    · index^(a1-j) · spent^j
    · argSep · index^a2 · separator
    · data(vals.take j) · cursor · data(vals.drop (j+1))
    · output false · finish · blank
\`\`\`

The designated cursor is unique and is located at frame ordinal
\`u + a1 + a2 + j + 4\`.  The head is on the preceding frame's final physical
cell, control is exactly \`aSeekOut .p3\`, and the context is

\`\`\`text
((g1Ctx0.withVB bB).withRes (g1Residual r.tag bB)).withVB bA
\`\`\`

so the residual and operand-A latch are both pinned.  The configuration also
requires \`r.vals[j]? = some bA\`; empty data therefore cannot inhabit
\`Σᴬ(0)\`.

The pure API proves field and whole-word index/spent/data counts, cursor
uniqueness and location, canonical splits/reconstruction, list-tape equality
and conditional extensionality, head safety, exact encoded-word physical
length and separate machine capacity.  Cursor claims are only about this
canonical word.  No property of an arbitrary caller pre/suffix or tape is
inferred without an explicit equality hypothesis.

S5 takes no new machine step.  It re-identifies merged S4's completed writer
endpoint as \`Σᴬ(0)\`, then transports the inherited real-initial unary and
successful-binary capstones, step counts and clock bounds.  Empty unary data
continues to S4's distinct OOB endpoint, while the successful binary premise
remains explicitly nonempty.

There is no round theorem, induction, driver, terminal execution, operand-A
repair, result computation, output write or acceptance theorem here.  The
marked/restored layouts and exact atomic-macro splits are pure S6 inputs only.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## List helpers -/

private theorem g1ADrop_cons (l : List Bool) (j : Nat) (hj : j < l.length) :
    l.drop j = l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => exact ih j (by simpa using hj)

private theorem g1AReplicate_split (m : Nat) (hm : 0 < m) (f : G1Frame) :
    List.replicate m f = List.replicate (m - 1) f ++ [f] := by
  obtain ⟨m, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  simp [List.replicate_succ']

theorem g1AGetn {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) (hj : j < l.length) : l[j] = v := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem g1ALength_pos_of_get {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) : j < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact Option.noConfusion h

private theorem g1AWalkConfigCongr (n h h' : Nat)
    (hh : h < G1M.tapeLength n) (hh' : h' < G1M.tapeLength n) (heq : h = h')
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode)
    (position : G1FramePosition) (b0 b1 b2 : Bool) (ctx : G1Ctx) :
    g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx =
      g1AlignedConfig n h' hh' tape mode position b0 b1 b2 ctx := by
  subst heq; rfl

/-! ## The two operand fields, named separately

The operand-1 field is the one the walk consumes; the operand-2 field is the one
the T2b-4a repair sweep already restored.  They are *both* runs of `index`
frames, so every count statement below is stated **per field**: a global `index`
count cannot distinguish them and is never used to. -/

/-- **The operand-1 field of `Σᴬ(j)`**: `a1 - j` unspent units followed by the
`j` units the walk has already consumed. -/
def g1AWalkOperand1 (r : G1Request) (j : Nat) : List G1Frame :=
  List.replicate (r.arg1 - j) G1Frame.index ++ List.replicate j G1Frame.spent

/-- **The operand-2 field**: `index^a2`, exactly as the repair sweep left it.
No layout of the operand-1 walk changes it. -/
def g1AWalkOperand2 (r : G1Request) : List G1Frame :=
  List.replicate r.arg2 G1Frame.index

/-- The frames right of the cursor: the untouched data suffix, the destination
frame, the terminator and the observable blank frame. -/
def g1AWalkTail (r : G1Request) (j : Nat) : List G1Frame :=
  (r.vals.drop (j + 1)).map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-! ## The three canonical layouts of a round -/

/-- **`Σᴬ(j)`'s frame list.**  The canonical word with the operand-1 field split
into `index^(a1-j) · spent^j`, the cursor hiding data slot `j`, the operand-2
field intact, and the observable blank frame appended. -/
def g1AWalkFrames (r : G1Request) (j : Nat) : List G1Frame :=
  g1TagRouteFrames r ++ g1AWalkOperand1 r j ++ [G1Frame.argSep] ++
    g1AWalkOperand2 r ++ [G1Frame.separator] ++
    (r.vals.take j).map G1Frame.data ++ [G1Frame.cursor] ++
    (r.vals.drop (j + 1)).map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The layout *between* the operand-1 `index ↦ spent` write and the cursor
restore: one more consumed unit, cursor still on data slot `j`. -/
def g1AWalkFramesMarked (r : G1Request) (j : Nat) : List G1Frame :=
  g1TagRouteFrames r ++ g1AWalkOperand1 r (j + 1) ++ [G1Frame.argSep] ++
    g1AWalkOperand2 r ++ [G1Frame.separator] ++
    (r.vals.take j).map G1Frame.data ++ [G1Frame.cursor] ++
    (r.vals.drop (j + 1)).map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The layout *after* the cursor restore and before the next probe: the data
region is exactly `vals` and carries no cursor, while the operand-1 field is
partially consumed, `index^(a1-j-1) · spent^(j+1)`.  This is the tape the
non-empty out-of-range boundary is reached on. -/
def g1AWalkFramesRestored (r : G1Request) (j : Nat) : List G1Frame :=
  g1TagRouteFrames r ++ g1AWalkOperand1 r (j + 1) ++ [G1Frame.argSep] ++
    g1AWalkOperand2 r ++ [G1Frame.separator] ++
    r.vals.map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The frame ordinal of the cursor in `Σᴬ(j)`. -/
def g1AWalkCursor (r : G1Request) (j : Nat) : Nat :=
  r.tag.units + r.arg1 + r.arg2 + j + 4

/-- The canonical data frames that remain visible around the designated
cursor.  This is a definition about `Σᴬ(j)`, not about an arbitrary caller
tape. -/
def g1AWalkDataFrames (r : G1Request) (j : Nat) : List G1Frame :=
  (r.vals.take j).map G1Frame.data ++
    (r.vals.drop (j + 1)).map G1Frame.data

/-- The canonical prefix ending immediately before the designated cursor. -/
def g1AWalkInvariantCursorPre (r : G1Request) (j : Nat) : List G1Frame :=
  g1TagRouteFrames r ++ g1AWalkOperand1 r j ++ [G1Frame.argSep] ++
    g1AWalkOperand2 r ++ [G1Frame.separator] ++
    (r.vals.take j).map G1Frame.data

/-- **The context every round of the operand-1 walk carries.**  The gate's
residual `g1Residual r.tag b` in the two spare bits `pass`/`crossed`, and the
operand-1 data latch in `vB`.  It is *not* `g1Ctx0.withVB v`: the residual is
the only record of which gate is being evaluated, and a round that reset the
spare bits would typecheck while destroying it. -/
def g1AWalkCtx (r : G1Request) (b v : Bool) : G1Ctx :=
  ((g1Ctx0.withVB b).withRes (g1Residual r.tag b)).withVB v

@[simp] theorem g1AWalkCtx_vB (r : G1Request) (b v : Bool) :
    (g1AWalkCtx r b v).vB = v := rfl

/-- **The residual is recoverable from the carried context.** -/
@[simp] theorem g1AWalkCtx_res (r : G1Request) (b v : Bool) :
    (g1AWalkCtx r b v).res = g1Residual r.tag b := by simp [g1AWalkCtx]

/-- **Re-latching the data bit leaves the residual bits alone.**  This is the
step of a round that could silently lose the residual, and it does not. -/
@[simp] theorem g1AWalkCtx_withVB (r : G1Request) (b v v' : Bool) :
    (g1AWalkCtx r b v).withVB v' = g1AWalkCtx r b v' := rfl

/-- **The field decomposition of `Σᴬ(j)`, spelled out.**  The two `index` runs
of the word are the two *named* fields; nothing below ever conflates them. -/
theorem g1AWalkFrames_fields (r : G1Request) (j : Nat) :
    g1AWalkFrames r j =
      g1TagRouteFrames r ++ g1AWalkOperand1 r j ++ [G1Frame.argSep] ++
        g1AWalkOperand2 r ++ [G1Frame.separator] ++
        (r.vals.take j).map G1Frame.data ++ [G1Frame.cursor] ++
        (r.vals.drop (j + 1)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] := rfl

/-- The operand-2 field is literally `index^a2`. -/
theorem g1AWalkOperand2_eq (r : G1Request) :
    g1AWalkOperand2 r = List.replicate r.arg2 G1Frame.index := rfl

/-! ### Per-field counts and lengths -/

private theorem g1ACount_replicate_ne (f g : G1Frame) (m : Nat) (h : f ≠ g) :
    (List.replicate m g).count f = 0 :=
  List.count_eq_zero.2 (fun hmem => h (List.eq_of_mem_replicate hmem))

/-- **Exactly `a1 - j` operand-1 units are still unspent.** -/
@[simp] theorem g1AWalkOperand1_count_index (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r j).count G1Frame.index = r.arg1 - j := by
  simp [g1AWalkOperand1, List.count_append,
    g1ACount_replicate_ne G1Frame.index G1Frame.spent j (by decide)]

/-- **Exactly `j` operand-1 units are spent.** -/
@[simp] theorem g1AWalkOperand1_count_spent (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r j).count G1Frame.spent = j := by
  simp [g1AWalkOperand1, List.count_append,
    g1ACount_replicate_ne G1Frame.spent G1Frame.index (r.arg1 - j) (by decide)]

/-- **The operand-1 field never holds a cursor.** -/
@[simp] theorem g1AWalkOperand1_count_cursor (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r j).count G1Frame.cursor = 0 := by
  simp [g1AWalkOperand1, List.count_append,
    g1ACount_replicate_ne G1Frame.cursor G1Frame.index (r.arg1 - j) (by decide),
    g1ACount_replicate_ne G1Frame.cursor G1Frame.spent j (by decide)]

/-- **The operand-1 field keeps its width**: consuming a unit rewrites it, it
does not delete it. -/
@[simp] theorem g1AWalkOperand1_length (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) : (g1AWalkOperand1 r j).length = r.arg1 := by
  simp only [g1AWalkOperand1, List.length_append, List.length_replicate]
  omega

/-- **The operand-2 field is exactly `index^a2`.** -/
@[simp] theorem g1AWalkOperand2_count_index (r : G1Request) :
    (g1AWalkOperand2 r).count G1Frame.index = r.arg2 := by
  simp [g1AWalkOperand2]

/-- **The operand-2 field holds no consumed unit.**  The operand-1 walk writes
no cell of it. -/
@[simp] theorem g1AWalkOperand2_count_spent (r : G1Request) :
    (g1AWalkOperand2 r).count G1Frame.spent = 0 :=
  g1ACount_replicate_ne G1Frame.spent G1Frame.index r.arg2 (by decide)

@[simp] theorem g1AWalkOperand2_count_cursor (r : G1Request) :
    (g1AWalkOperand2 r).count G1Frame.cursor = 0 :=
  g1ACount_replicate_ne G1Frame.cursor G1Frame.index r.arg2 (by decide)

@[simp] theorem g1AWalkOperand2_length (r : G1Request) :
    (g1AWalkOperand2 r).length = r.arg2 := by simp [g1AWalkOperand2]

/-! ### Whole-word counts

The counts below are over the **whole** word.  For `index` that is a sum across
*two* fields; on its own it says nothing about how far the operand-1 walk has
got, and no proof in this family uses it for that.  The per-field lemmas above
are what pin the operand-1 progress. -/

private theorem g1ACount_data_run (f : G1Frame) (l : List G1Frame)
    (hl : ∀ g ∈ l, ∃ v : Bool, g = G1Frame.data v)
    (hf : ∀ v : Bool, f ≠ G1Frame.data v) : l.count f = 0 :=
  List.count_eq_zero.2 (fun hmem =>
    match hl f hmem with | ⟨v, hv⟩ => hf v hv)

private theorem g1AData_run_map (l : List Bool) :
    ∀ g ∈ l.map G1Frame.data, ∃ v : Bool, g = G1Frame.data v := by
  intro g hg
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hg
  exact ⟨v, rfl⟩

private theorem g1AData_run_take (l : List Bool) (k : Nat) :
    ∀ g ∈ List.take k (l.map G1Frame.data), ∃ v : Bool, g = G1Frame.data v :=
  fun g hg => g1AData_run_map l g (List.mem_of_mem_take hg)

private theorem g1AData_run_drop (l : List Bool) (k : Nat) :
    ∀ g ∈ List.drop k (l.map G1Frame.data), ∃ v : Bool, g = G1Frame.data v :=
  fun g hg => g1AData_run_map l g (List.mem_of_mem_drop hg)

private theorem g1ATagRoute_count_index (r : G1Request) :
    (g1TagRouteFrames r).count G1Frame.index = 0 := by
  simp [g1TagRouteFrames, List.count_append,
    g1ACount_replicate_ne G1Frame.index G1Frame.tag r.tag.units (by decide)]

private theorem g1ATagRoute_count_spent (r : G1Request) :
    (g1TagRouteFrames r).count G1Frame.spent = 0 := by
  simp [g1TagRouteFrames, List.count_append,
    g1ACount_replicate_ne G1Frame.spent G1Frame.tag r.tag.units (by decide)]

private theorem g1ATagRoute_count_cursor (r : G1Request) :
    (g1TagRouteFrames r).count G1Frame.cursor = 0 := by
  simp [g1TagRouteFrames, List.count_append,
    g1ACount_replicate_ne G1Frame.cursor G1Frame.tag r.tag.units (by decide)]

/-- **The cursor is unique.**  There is exactly one `cursor` frame in `Σᴬ(j)`. -/
theorem g1AWalkFrames_count_cursor (r : G1Request) (j : Nat) :
    (g1AWalkFrames r j).count G1Frame.cursor = 1 := by
  simp [g1AWalkFrames, List.count_append, g1ATagRoute_count_cursor,
    g1ACount_data_run G1Frame.cursor _ (g1AData_run_take r.vals j) (by decide),
    g1ACount_data_run G1Frame.cursor _ (g1AData_run_drop r.vals (j + 1))
      (by decide)]

/-- The whole-word `spent` count of `Σᴬ(j)` is the operand-1 field's: no other
field holds a consumed unit. -/
theorem g1AWalkFrames_count_spent (r : G1Request) (j : Nat) :
    (g1AWalkFrames r j).count G1Frame.spent = j := by
  simp [g1AWalkFrames, List.count_append, g1ATagRoute_count_spent,
    g1ACount_data_run G1Frame.spent _ (g1AData_run_take r.vals j) (by decide),
    g1ACount_data_run G1Frame.spent _ (g1AData_run_drop r.vals (j + 1))
      (by decide)]

/-- The whole-word `index` count of `Σᴬ(j)`, **as a sum of the two fields**:
`a1 - j` from operand 1 and `a2` from operand 2.  Use
`g1AWalkOperand1_count_index` to talk about the walk's progress. -/
theorem g1AWalkFrames_count_index (r : G1Request) (j : Nat) :
    (g1AWalkFrames r j).count G1Frame.index = (r.arg1 - j) + r.arg2 := by
  simp [g1AWalkFrames, List.count_append, g1ATagRoute_count_index,
    g1ACount_data_run G1Frame.index _ (g1AData_run_take r.vals j) (by decide),
    g1ACount_data_run G1Frame.index _ (g1AData_run_drop r.vals (j + 1))
      (by decide)]

/-- The visible data region has exactly one fewer frame than `vals`: slot `j`
is occupied by the unique cursor. -/
@[simp] theorem g1AWalkDataFrames_length (r : G1Request) (j : Nat)
    (hj : j < r.vals.length) :
    (g1AWalkDataFrames r j).length = r.vals.length - 1 := by
  simp only [g1AWalkDataFrames, List.length_append, List.length_map,
    List.length_take, List.length_drop]
  omega

/-- Exact per-bit data-frame count in the visible prefix and suffix. -/
private theorem g1ACount_data_map (xs : List Bool) (v : Bool) :
    (xs.map G1Frame.data).count (.data v) = xs.count v := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> cases v <;> simp_all

theorem g1AWalkDataFrames_count (r : G1Request) (j : Nat) (v : Bool) :
    (g1AWalkDataFrames r j).count (.data v) =
      (r.vals.take j).count v + (r.vals.drop (j + 1)).count v := by
  rw [g1AWalkDataFrames, List.count_append, g1ACount_data_map,
    g1ACount_data_map]

/-- **The restored layout carries no cursor at all.** -/
theorem g1AWalkFramesRestored_count_cursor (r : G1Request) (j : Nat) :
    (g1AWalkFramesRestored r j).count G1Frame.cursor = 0 := by
  simp [g1AWalkFramesRestored, List.count_append, g1ATagRoute_count_cursor,
    g1ACount_data_run G1Frame.cursor _ (g1AData_run_map r.vals) (by decide)]

/-- **The restored layout's data region is exactly `vals`.** -/
theorem g1AWalkFramesRestored_data (r : G1Request) (j : Nat) :
    g1AWalkFramesRestored r j =
      g1TagRouteFrames r ++ g1AWalkOperand1 r (j + 1) ++ [G1Frame.argSep] ++
        g1AWalkOperand2 r ++ [G1Frame.separator] ++
        r.vals.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] := rfl

/-- **The restored layout's operand-1 field is `index^(a1-j-1) · spent^(j+1)`**:
one more unit consumed, and nothing else. -/
theorem g1AWalkFramesRestored_count_spent (r : G1Request) (j : Nat) :
    (g1AWalkFramesRestored r j).count G1Frame.spent = j + 1 := by
  simp [g1AWalkFramesRestored, List.count_append, g1ATagRoute_count_spent,
    g1ACount_data_run G1Frame.spent _ (g1AData_run_map r.vals) (by decide)]

theorem g1AWalkFramesRestored_count_index (r : G1Request) (j : Nat) :
    (g1AWalkFramesRestored r j).count G1Frame.index =
      (r.arg1 - j - 1) + r.arg2 := by
  simp [g1AWalkFramesRestored, List.count_append, g1ATagRoute_count_index,
    g1ACount_data_run G1Frame.index _ (g1AData_run_map r.vals) (by decide),
    Nat.sub_sub]

/-- **Per-field restored count.**  The operand-1 field alone has exactly
`arg1 - j - 1` unspent units; unlike the whole-word count above, this statement
does not include the intact operand-2 `index^arg2` run. -/
@[simp] theorem g1AWalkFramesRestored_operand1_count_index
    (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r (j + 1)).count G1Frame.index = r.arg1 - j - 1 := by
  rw [g1AWalkOperand1_count_index]
  omega

/-! ### Lengths -/

theorem g1AWalkFrames_length (r : G1Request) (j : Nat) (hj1 : j ≤ r.arg1)
    (hj : j < r.vals.length) :
    (g1AWalkFrames r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp only [g1AWalkFrames, List.length_append, g1TagRouteFrames_length,
    g1AWalkOperand1_length r j hj1, g1AWalkOperand2_length, List.length_map,
    List.length_take, List.length_drop, List.length_cons, List.length_nil]
  omega

/-- **The invariant word is exactly the real tape word's length.**  No frame is
invented and none is lost by the operand-1 walk. -/
theorem g1AWalkFrames_length_eq_validation (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    (g1AWalkFrames r j).length =
      (encodeG1Frames r ++ [G1Frame.blank]).length := by
  rw [g1AWalkFrames_length r j hj1 hj]
  simp only [List.length_append, encodeG1Frames_length, List.length_cons,
    List.length_nil]

/-- Reconstruction of the canonical word from its exact prefix, designated
cursor and exact data/output/finish/blank tail. -/
theorem g1AWalkFrames_cursor_split (r : G1Request) (j : Nat) :
    g1AWalkInvariantCursorPre r j ++
        G1Frame.cursor :: g1AWalkTail r j = g1AWalkFrames r j := by
  simp [g1AWalkInvariantCursorPre, g1AWalkTail, g1AWalkFrames,
    List.append_assoc]

/-- The designated cursor's canonical prefix has exactly its stated frame
ordinal. -/
theorem g1AWalkInvariantCursorPre_length (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    (g1AWalkInvariantCursorPre r j).length = g1AWalkCursor r j := by
  simp only [g1AWalkInvariantCursorPre, List.length_append,
    g1TagRouteFrames_length, g1AWalkOperand1_length r j hj1,
    g1AWalkOperand2_length, List.length_map, List.length_take,
    List.length_cons, List.length_nil, g1AWalkCursor]
  omega

/-- The unique cursor is physically located at frame ordinal
`g1AWalkCursor r j` in the canonical invariant word. -/
theorem g1AWalkFrames_cursor_at (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    (g1AWalkFrames r j)[g1AWalkCursor r j]? = some G1Frame.cursor := by
  rw [← g1AWalkFrames_cursor_split r j,
    ← g1AWalkInvariantCursorPre_length r j hj1 hj]
  simp

/-- The explicit blank frame makes the invariant's physical word four cells
longer than the encoded input.  This is an encoded-length fact, not a machine
capacity equation. -/
theorem g1AWalkFrames_physical_length (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    ((g1AWalkFrames r j).flatMap G1Frame.bits).length =
      (encodeG1 r).length + 4 := by
  rw [G1Frame.flatMap_bits_length,
    g1AWalkFrames_length r j hj1 hj, encodeG1_length]
  omega

/-- The exact invariant word, including its explicit blank frame, fits inside
the compiled machine's physical tape capacity. -/
theorem g1AWalkFrames_physical_length_lt_capacity (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    ((g1AWalkFrames r j).flatMap G1Frame.bits).length <
      G1M.tapeLength (encodeG1 r).length := by
  rw [g1AWalkFrames_physical_length r j hj1 hj]
  exact g1_lt_tapeLength (by omega)

/-- Extensionality for comparison with a caller-provided physical tape.  The
caller must prove every cell agrees with the canonical invariant tape; no
cursor-freedom property is inferred for arbitrary tape fragments. -/
theorem g1AWalkTape_ext (r : G1Request) (j : Nat)
    (tape : Fin (G1M.tapeLength (encodeG1 r).length) → Bool)
    (hcell : ∀ i, tape i =
      g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) i) :
    tape = g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) :=
  funext hcell

/-- Equal canonical frame words induce equal physical tapes. -/
theorem g1AWalkTape_eq_of_frames_eq (r : G1Request) (j : Nat)
    (frames : List G1Frame) (hframes : frames = g1AWalkFrames r j) :
    g1ListTape (n := (encodeG1 r).length) (frames.flatMap G1Frame.bits) =
      g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) := by
  rw [hframes]

theorem g1AWalkFramesRestored_length (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    (g1AWalkFramesRestored r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp only [g1AWalkFramesRestored, List.length_append, g1TagRouteFrames_length,
    g1AWalkOperand1_length r (j + 1) (by omega), g1AWalkOperand2_length,
    List.length_map, List.length_cons, List.length_nil]
  omega

/-! ## The three runs a round crosses, and why nothing stops them early

Each run is a list built from the layout; each `_skip` lemma discharges the
hypothesis of the matching atomic macro of `GateOneAWalkKernel`, and each `_no_`
lemma is the exclusion half — the frame that *does* stop the pass is provably
outside the run it crosses. -/

/-- The run the **outer** seek crosses, right to left: the data prefix, the
`separator` and the whole operand-2 field. -/
def g1AWalkOuterRun (r : G1Request) (j : Nat) : List G1Frame :=
  g1AWalkOperand2 r ++ [G1Frame.separator] ++ (r.vals.take j).map G1Frame.data

/-- The run the **inner** seek crosses: the consumed suffix of the operand-1
field, and nothing else. -/
def g1AWalkInnerRun (j : Nat) : List G1Frame := List.replicate j G1Frame.spent

/-- The run the forward return crosses, left to right: the consumed operand-1
suffix, the `argSep` between the fields, the operand-2 field, the `separator`
and the data prefix. -/
def g1AWalkFwdRun (r : G1Request) (j : Nat) : List G1Frame :=
  g1AWalkInnerRun j ++ [G1Frame.argSep] ++ g1AWalkOuterRun r j

theorem g1AWalkOuterRun_skip (r : G1Request) (j : Nat) :
    ∀ f ∈ g1AWalkOuterRun r j, G1ASeekOutSkip f := by
  intro f hf
  rcases List.mem_append.1 hf with h1 | h2
  · rcases List.mem_append.1 h1 with h | h
    · rw [List.eq_of_mem_replicate h]; exact trivial
    · rw [show f = G1Frame.separator from by simpa using h]; exact trivial
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 h2
    exact trivial

/-- **The outer seek reaches the `argSep` between the two fields.**  Its run
holds no `argSep`, so it cannot turn earlier — in particular it never turns
inside the operand-2 field or on the `separator`. -/
theorem g1AWalkOuterRun_no_argSep (r : G1Request) (j : Nat) :
    G1Frame.argSep ∉ g1AWalkOuterRun r j := fun h =>
  G1ASeekOutSkip_ne_argSep (g1AWalkOuterRun_skip r j _ h) rfl

theorem g1AWalkInnerRun_skip (j : Nat) :
    ∀ f ∈ g1AWalkInnerRun j, G1ASeekInSkip f := by
  intro f hf
  rw [List.eq_of_mem_replicate hf]; exact trivial

/-- **The inner seek stops on the operand-1 `index` adjacent to the spent
run.**  Its run holds no `index`, so the first one it meets is the rightmost
unspent unit — which `g1AWalkSplit_seek` places immediately left of the run. -/
theorem g1AWalkInnerRun_no_index (j : Nat) :
    G1Frame.index ∉ g1AWalkInnerRun j := fun h =>
  G1ASeekInSkip_ne_index (g1AWalkInnerRun_skip j _ h) rfl

/-- **The inner seek stops on the `argSep` opening the operand-1 field** when
that field is exhausted.  This is the confinement statement of the operand-1
pass: it reads nothing to the left of its own field. -/
theorem g1AWalkInnerRun_no_argSep (j : Nat) :
    G1Frame.argSep ∉ g1AWalkInnerRun j := fun h =>
  G1ASeekInSkip_ne_argSep (g1AWalkInnerRun_skip j _ h) rfl

/-- The forward skip class contains the inner seek's. -/
private theorem g1AWalkSkip_of_seekIn {f : G1Frame} (h : G1ASeekInSkip f) :
    G1AWalkSkip f := by
  cases f <;> trivial

/-- The forward skip class contains the outer seek's. -/
private theorem g1AWalkSkip_of_seekOut {f : G1Frame} (h : G1ASeekOutSkip f) :
    G1AWalkSkip f := by
  cases f <;> trivial

theorem g1AWalkFwdRun_skip (r : G1Request) (j : Nat) :
    ∀ f ∈ g1AWalkFwdRun r j, G1AWalkSkip f := by
  intro f hf
  rcases List.mem_append.1 hf with h1 | h2
  · rcases List.mem_append.1 h1 with h | h
    · exact g1AWalkSkip_of_seekIn (g1AWalkInnerRun_skip j f h)
    · rw [show f = G1Frame.argSep from by simpa using h]; exact trivial
  · exact g1AWalkSkip_of_seekOut (g1AWalkOuterRun_skip r j f h2)

/-- **The forward return reaches the cursor.**  Its run holds no `cursor`, so
the first one it meets is the one `Σᴬ(j)` installed. -/
theorem g1AWalkFwdRun_no_cursor (r : G1Request) (j : Nat) :
    G1Frame.cursor ∉ g1AWalkFwdRun r j := fun h =>
  by
    have hs := g1AWalkFwdRun_skip r j _ h
    simp [G1AWalkSkip] at hs

theorem g1AWalkInnerRun_length (j : Nat) : (g1AWalkInnerRun j).length = j := by
  simp [g1AWalkInnerRun]

theorem g1AWalkOuterRun_length (r : G1Request) (j : Nat)
    (hj : j ≤ r.vals.length) :
    (g1AWalkOuterRun r j).length = r.arg2 + j + 1 := by
  simp only [g1AWalkOuterRun, List.length_append, g1AWalkOperand2_length,
    List.length_map, List.length_take, List.length_cons, List.length_nil]
  omega

theorem g1AWalkFwdRun_length (r : G1Request) (j : Nat)
    (hj : j ≤ r.vals.length) :
    (g1AWalkFwdRun r j).length = 2 * j + r.arg2 + 2 := by
  simp only [g1AWalkFwdRun, List.length_append, g1AWalkInnerRun_length,
    g1AWalkOuterRun_length r j hj, List.length_cons, List.length_nil]
  omega

/-! ## Layout splits

Each split is a pure re-association of the three definitions above, in exactly
the shape one atomic macro of `GateOneAWalkKernel` consumes.  No execution claim
is involved. -/

/-- **The mixed-seek shape.**  For `j < a1` the word is
`(tagRoute · index^(a1-j-1)) · index · spent^j · argSep · outerRun · cursor · tail`:
the marker `index` the inner seek stops on sits immediately left of the spent
run, and the boundary `argSep` the outer seek turns on is the one *between* the
two operand fields. -/
theorem g1AWalkSplit_seek (r : G1Request) (j : Nat) (hj1 : j < r.arg1) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) G1Frame.index) ++
        G1Frame.index :: g1AWalkInnerRun j ++
        G1Frame.argSep :: g1AWalkOuterRun r j ++
        (G1Frame.cursor :: g1AWalkTail r j) =
      g1AWalkFrames r j := by
  rw [g1AWalkFrames, g1AWalkOperand1,
    g1AReplicate_split (r.arg1 - j) (by omega) G1Frame.index]
  simp [g1AWalkInnerRun, g1AWalkOuterRun, g1AWalkTail, List.append_assoc]

/-- The same word, in the `pre ++ index :: suffix` shape the `index ↦ spent`
writer consumes. -/
theorem g1AWalkSplit_mark (r : G1Request) (j : Nat) (hj1 : j < r.arg1) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) G1Frame.index) ++
        G1Frame.index :: (g1AWalkInnerRun j ++ G1Frame.argSep ::
          (g1AWalkOuterRun r j ++ G1Frame.cursor :: g1AWalkTail r j)) =
      g1AWalkFrames r j := by
  rw [g1AWalkFrames, g1AWalkOperand1,
    g1AReplicate_split (r.arg1 - j) (by omega) G1Frame.index]
  simp [g1AWalkInnerRun, g1AWalkOuterRun, g1AWalkTail, List.append_assoc]

/-- The marked layout, in the same shape: the marker cell now holds `spent`. -/
theorem g1AWalkSplit_marked (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) G1Frame.index) ++
        G1Frame.spent :: (g1AWalkInnerRun j ++ G1Frame.argSep ::
          (g1AWalkOuterRun r j ++ G1Frame.cursor :: g1AWalkTail r j)) =
      g1AWalkFramesMarked r j := by
  rw [g1AWalkFramesMarked, g1AWalkOperand1, Nat.sub_sub, List.replicate_succ]
  simp [g1AWalkInnerRun, g1AWalkOuterRun, g1AWalkTail, List.append_assoc]

/-- The marked layout, in the shape the forward return consumes. -/
theorem g1AWalkSplit_marked_fwd (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) G1Frame.index ++
        [G1Frame.spent]) ++ g1AWalkFwdRun r j ++
        G1Frame.cursor :: g1AWalkTail r j =
      g1AWalkFramesMarked r j := by
  rw [g1AWalkFramesMarked, g1AWalkOperand1, Nat.sub_sub, List.replicate_succ]
  simp [g1AWalkFwdRun, g1AWalkInnerRun, g1AWalkOuterRun, g1AWalkTail,
    List.append_assoc]

/-- The prefix of the marked layout up to the cursor. -/
def g1AWalkCursorPre (r : G1Request) (j : Nat) : List G1Frame :=
  g1TagRouteFrames r ++ g1AWalkOperand1 r (j + 1) ++ [G1Frame.argSep] ++
    g1AWalkOperand2 r ++ [G1Frame.separator] ++
    (r.vals.take j).map G1Frame.data

theorem g1AWalkSplit_marked_cursor (r : G1Request) (j : Nat) :
    g1AWalkCursorPre r j ++ G1Frame.cursor :: g1AWalkTail r j =
      g1AWalkFramesMarked r j := by
  simp [g1AWalkCursorPre, g1AWalkFramesMarked, g1AWalkTail, List.append_assoc]

/-- The cursor restore, `cursor ↦ data vals[j]`, lands on the restored
layout. -/
theorem g1AWalkSplit_restored_cursor (r : G1Request) (j : Nat) (v : Bool)
    (hj : j < r.vals.length) (hv : r.vals[j] = v) :
    g1AWalkCursorPre r j ++ G1Frame.data v :: g1AWalkTail r j =
      g1AWalkFramesRestored r j := by
  have hd : r.vals.map G1Frame.data =
      (r.vals.take j).map G1Frame.data ++
        G1Frame.data v :: (r.vals.drop (j + 1)).map G1Frame.data := by
    conv_lhs => rw [← List.take_append_drop j r.vals]
    rw [List.map_append, g1ADrop_cons r.vals j hj, hv]
    simp
  rw [g1AWalkFramesRestored, hd]
  simp [g1AWalkCursorPre, g1AWalkTail, List.append_assoc]

/-- The prefix of the restored layout up to data slot `j + 1`. -/
def g1AWalkProbePre (r : G1Request) (j : Nat) : List G1Frame :=
  g1TagRouteFrames r ++ g1AWalkOperand1 r (j + 1) ++ [G1Frame.argSep] ++
    g1AWalkOperand2 r ++ [G1Frame.separator] ++
    (r.vals.take (j + 1)).map G1Frame.data

/-- The restored layout, in the shape the next probe consumes. -/
theorem g1AWalkSplit_restored_probe (r : G1Request) (j : Nat) (v' : Bool)
    (hj1 : j + 1 < r.vals.length) (hv' : r.vals[j + 1] = v') :
    g1AWalkProbePre r j ++ G1Frame.data v' :: ((r.vals.drop (j + 2)).map
        G1Frame.data ++ [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1AWalkFramesRestored r j := by
  have hd : r.vals.map G1Frame.data =
      (r.vals.take (j + 1)).map G1Frame.data ++
        G1Frame.data v' :: (r.vals.drop (j + 2)).map G1Frame.data := by
    conv_lhs => rw [← List.take_append_drop (j + 1) r.vals]
    rw [List.map_append, g1ADrop_cons r.vals (j + 1) hj1, hv']
    simp
  rw [g1AWalkFramesRestored, hd]
  simp [g1AWalkProbePre, List.append_assoc]

/-- The restored layout, in the shape the **out-of-range** probe consumes: with
`j + 1 = m` the frame behind the last data slot is the `output` destination. -/
theorem g1AWalkSplit_restored_oob (r : G1Request) (j : Nat)
    (hj1 : j + 1 = r.vals.length) :
    g1AWalkProbePre r j ++
        G1Frame.output false :: [G1Frame.finish, G1Frame.blank] =
      g1AWalkFramesRestored r j := by
  have htake : r.vals.take (j + 1) = r.vals := by rw [hj1]; simp
  rw [g1AWalkFramesRestored, g1AWalkProbePre, htake]

/-- Installing the next cursor lands on `Σᴬ(j+1)`. -/
theorem g1AWalkSplit_succ (r : G1Request) (j : Nat) :
    g1AWalkProbePre r j ++ G1Frame.cursor :: ((r.vals.drop (j + 2)).map
        G1Frame.data ++ [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1AWalkFrames r (j + 1) := by
  rw [g1AWalkFrames, g1AWalkProbePre]
  simp [List.append_assoc]

/-! ### Layout lengths used by the round proof -/

theorem g1AWalkMarkPre_length (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++
      List.replicate (r.arg1 - j - 1) G1Frame.index).length =
      r.tag.units + 2 + (r.arg1 - j - 1) := by
  simp only [List.length_append, g1TagRouteFrames_length, List.length_replicate]

theorem g1AWalkFwdPre_length (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) G1Frame.index ++
      [G1Frame.spent]).length = r.tag.units + 3 + (r.arg1 - j - 1) := by
  simp only [List.length_append, g1TagRouteFrames_length, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem g1AWalkCursorPre_length (r : G1Request) (j : Nat) (hj1 : j < r.arg1)
    (hj : j < r.vals.length) :
    (g1AWalkCursorPre r j).length = g1AWalkCursor r j := by
  simp only [g1AWalkCursorPre, List.length_append, g1TagRouteFrames_length,
    g1AWalkOperand1_length r (j + 1) (by omega), g1AWalkOperand2_length,
    List.length_map, List.length_take, List.length_cons, List.length_nil,
    g1AWalkCursor]
  omega

theorem g1AWalkProbePre_length (r : G1Request) (j : Nat) (hj1 : j < r.arg1)
    (hj : j + 1 ≤ r.vals.length) :
    (g1AWalkProbePre r j).length = g1AWalkCursor r j + 1 := by
  simp only [g1AWalkProbePre, List.length_append, g1TagRouteFrames_length,
    g1AWalkOperand1_length r (j + 1) (by omega), g1AWalkOperand2_length,
    List.length_map, List.length_take, List.length_cons, List.length_nil,
    g1AWalkCursor]
  omega

/-! ### Head safety, from `j < vals.length` alone -/

/-- **Every cell a round touches is inside the tape.**  The furthest physical
cell any macro of a round reaches is `4 * (g1AWalkCursor r j + 2)`, the frame
boundary just past the probed frame. -/
theorem g1AWalkCursor_safe (r : G1Request) (j : Nat) (hj : j < r.vals.length) :
    4 * (g1AWalkCursor r j + 2) < G1M.tapeLength (encodeG1 r).length :=
  g1_route_lt_tapeLength r _ (by simp only [g1AWalkCursor]; omega)

/-! ## `Σᴬ(j)`: the canonical operand-1 walk configuration -/

set_option linter.unusedVariables false in
/-- **`Σᴬ(r, b, j, v)`: the operand-1 cursor-walk invariant.**  The tape is
`g1AWalkFrames r j`, the head is on the last cell of the frame preceding the
cursor, the control is the **outer** reverse seek `aSeekOut .p3` with an empty
frame buffer, and the context is
`((g1Ctx0.withVB b).withRes (g1Residual r.tag b)).withVB v`: the gate's residual
still latched in `pass`/`crossed`, and the operand-1 data latch `vB = v`.  With
`hv : r.vals[j]? = some v` the latch carries exactly `vals[j]`, the bit the
cursor is hiding.

The two numeric conditions of the invariant are explicit arguments; `hj1` is
carried as a proof obligation rather than used by the head bound, so the
configuration cannot be formed outside the invariant's range and the saturated
subtraction `a1 - j` never silently clamps. -/
def g1AWalkConfig (r : G1Request) (b : Bool) (j : Nat) (hj1 : j ≤ r.arg1)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length (4 * g1AWalkCursor r j - 1)
    (by have := g1AWalkCursor_safe r j hj; omega)
    (g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits))
    .aSeekOut .p3 false false false (g1AWalkCtx r b v)

@[simp] theorem g1AWalkConfig_tape (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).tape =
      g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) := rfl

@[simp] theorem g1AWalkConfig_head (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    ((g1AWalkConfig r b j hj1 hj v hv).head : Nat) =
      4 * g1AWalkCursor r j - 1 :=
  rfl

@[simp] theorem g1AWalkConfig_state (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).state.snd =
      g1State .aSeekOut .p3 false false false (g1AWalkCtx r b v) := rfl

/-- **The latched bit is the one the cursor is hiding.** -/
@[simp] theorem g1AWalkConfig_vB (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).state.snd.ctx.vB = v := rfl

/-- **The gate's residual survives every round.**  It lives in `pass`/`crossed`,
which the data latch does not touch; a `g1Ctx0`-shaped invariant would destroy
it silently. -/
@[simp] theorem g1AWalkConfig_res (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).state.snd.ctx.res =
      g1Residual r.tag b := by
  simp [g1AWalkConfig, g1AlignedConfig, g1AlignedConfigQ, g1State]

/-- **`Σᴬ(j)` is inside the current operand-A walk family**, solely because its
exact boundary mode is `aSeekOut`.  This is a state classification, not an
execution or exit claim. -/
theorem g1AWalkConfig_walkMode (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    G1AWalkMode (g1AWalkConfig r b j hj1 hj v hv).state.snd.mode := trivial

/-! ## S5 installation: merged S4 endpoint is \`Σᴬ(0)\`

This section takes no machine step beyond S4.  It re-identifies the completed
writer's exact \`aSeekOut .p3\` endpoint as the invariant, then transports S4's
real-initial unary and successful-binary capstones.  Empty unary data stays on
the separate S4 OOB endpoint; successful binary data remains explicitly
nonempty.
-/

/-- S4's canonical first-cursor word is exactly \`Σᴬ(0)\`. -/
theorem g1AFirstCursorFrames_eq_sigma0 (r : G1Request) (v : Bool)
    (rest : List Bool) (hv : r.vals = v :: rest) :
    g1AFirstCursorFrames r = g1AWalkFrames r 0 := by
  rw [g1AFirstCursorFrames, g1AWalkFrames, g1InstallRouteFrames,
    g1FieldRouteFrames, g1TagRouteFrames, g1AWalkOperand1, g1AWalkOperand2, hv]
  simp [List.append_assoc]

/-- The completed S4 writer endpoint is the exact invariant configuration at
\`j = 0\`, including the residual and operand-A latch. -/
theorem g1APostWriterConfig_eq_sigma0 (r : G1Request) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    g1APostWriterConfig r bA bB =
      g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
        (by rw [hv]; simp) := by
  rw [g1APostWriterConfig, g1AWalkConfig,
    g1AFirstCursorFrames_eq_sigma0 r bA rest hv]
  exact g1AWalkConfigCongr _ _ _ _ _ (by simp [g1AWalkCursor])
    _ _ _ _ _ _ _

/-- From S4's residual-latched handoff to \`Σᴬ(0)\`, with S4's exact steps. -/
theorem g1CS_aWalk_sigma0_exact (r : G1Request) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (g1AInstallConfig r bB)
        (g1ALiveInstallSteps r) =
      g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
        (by rw [hv]; simp) := by
  rw [g1CS_aInstall_success_exact r bA bB rest hv]
  exact g1APostWriterConfig_eq_sigma0 r bA bB rest hv

/-- Every real-initial unary success reaches \`Σᴬ(0)\` at the inherited S4
step count. -/
theorem g1CS_readA_sigma0_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (v : Bool) (rest : List Bool)
    (hv : r.vals = v :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r) =
      g1AWalkConfig r false 0 (Nat.zero_le _) (by rw [hv]; simp) v
        (by rw [hv]; simp) := by
  rw [g1CS_aCursor_unary_initial_exact r hc ht v rest hv]
  exact g1APostWriterConfig_eq_sigma0 r v false rest hv

/-- Every successful real-initial binary route reaches \`Σᴬ(0)\`; the physical
operand-B read and the nonempty operand-A data premise remain explicit. -/
theorem g1CS_readA_sigma0_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (bA bB : Bool) (rest : List Bool)
    (hB : r.vals[r.arg2]? = some bB) (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r) =
      g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
        (by rw [hv]; simp) := by
  rw [g1CS_aCursor_binary_initial_exact r hc ht bA bB rest hB hv]
  exact g1APostWriterConfig_eq_sigma0 r bA bB rest hv

/-- The inherited S4 unary-success budget stays inside the unchanged clock. -/
theorem g1AWalk_unary_sigma0_steps_le_clock (r : G1Request) :
    g1AUnaryCursorSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AUnaryCursorSteps_le_clock r

/-- The inherited S4 binary-success budget stays inside the unchanged clock. -/
theorem g1AWalk_binary_sigma0_steps_le_clock (r : G1Request) :
    g1ABinaryCursorSteps r ≤ g1Clock (encodeG1 r).length :=
  g1ABinaryCursorSteps_le_clock r

/-! ### Honest empty-data/OOB separation -/

/-- Empty data has no value proof with which an exact \`Σᴬ(0)\` configuration
can be inhabited. -/
theorem g1AWalk_sigma0_no_success_of_empty (r : G1Request)
    (hempty : r.vals = []) : ¬ ∃ v : Bool, r.vals[0]? = some v := by
  rw [hempty]
  simp

/-- A successful binary read entails nonempty data; S5 does not weaken or hide
that premise. -/
theorem g1AWalk_binary_success_not_empty (r : G1Request) (b : Bool)
    (hB : r.vals[r.arg2]? = some b) : r.vals ≠ [] :=
  g1A_binary_success_not_empty r b hB

/-- Empty unary input follows S4's OOB capstone, not a success invariant. -/
theorem g1CS_readA_sigma0_unary_oob_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (hempty : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryOOBSteps r) = g1AInstallOOBConfig r false :=
  g1CS_aInstall_unary_oob_initial_exact r hc ht hempty

/-- The S4 OOB endpoint is distinct from every well-formed \`Σᴬ(0)\` endpoint. -/
theorem g1AInstallOOBConfig_ne_sigma0 (r : G1Request) (bB v : Bool)
    (h0 : 0 < r.vals.length) (hv : r.vals[0]? = some v) :
    g1AInstallOOBConfig r bB ≠
      g1AWalkConfig r bB 0 (Nat.zero_le _) h0 v hv := by
  intro h
  have hm := congrArg (fun c => c.state.snd.mode) h
  simp [g1AInstallOOBConfig, g1AWalkConfig, g1AlignedConfig,
    g1AlignedConfigQ, g1State] at hm

/-- The inherited empty-unary OOB budget stays inside the unchanged clock. -/
theorem g1AWalk_unary_oob_steps_le_clock (r : G1Request) :
    g1AUnaryOOBSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AUnaryOOBSteps_le_clock r

/-! ### Literal real-initial representatives -/

namespace G1AWalkInvariantExamples

/-- Literal unary representative: S4's 131-step input-false run inhabits
\`Σᴬ(0)\`. -/
theorem input_false_sigma0_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqInputFalse))) 131 =
      g1AWalkConfig G1ALiveInstallExamples.reqInputFalse false 0
        (by decide) (by decide) false (by decide) := by
  rw [G1ALiveInstallExamples.input_false_cursor_exact]
  exact g1APostWriterConfig_eq_sigma0
    G1ALiveInstallExamples.reqInputFalse false false [] rfl

/-- Literal successful binary representative: S4's 236-step or-true run
inhabits \`Σᴬ(0)\` with the true residual payload. -/
theorem or_true_sigma0_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqOrTrue))) 236 =
      g1AWalkConfig G1ALiveInstallExamples.reqOrTrue true 0
        (by decide) (by decide) true (by decide) := by
  rw [G1ALiveInstallExamples.or_true_cursor_exact]
  exact g1APostWriterConfig_eq_sigma0
    G1ALiveInstallExamples.reqOrTrue true true [] rfl

/-- Literal empty unary representative stays at the distinct OOB boundary. -/
theorem input_empty_oob_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqInputOOB))) 118 =
      g1AInstallOOBConfig G1ALiveInstallExamples.reqInputOOB false :=
  G1ALiveInstallExamples.input_empty_oob_exact

/-- The literal empty unary request has no \`Σᴬ(0)\` value witness. -/
theorem input_empty_no_sigma0_success :
    ¬ ∃ v : Bool, G1ALiveInstallExamples.reqInputOOB.vals[0]? = some v :=
  g1AWalk_sigma0_no_success_of_empty
    G1ALiveInstallExamples.reqInputOOB rfl

end G1AWalkInvariantExamples

end Pnp3.Internal.PsubsetPpoly.TM
