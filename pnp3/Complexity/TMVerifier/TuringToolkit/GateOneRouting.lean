import Complexity.TMVerifier.TuringToolkit.GateOneControl

/-!
# G1 pass-B routing, at frame level

**Progress classification: Infrastructure.**  The frame-level content of the
pass-B rescan: which prefix of the canonical word the fixed control reads from
`readBStart`, that the prefix is a grammar-valid path, and which mode the fold
of the forward table lands in.  Nothing here mentions a Turing machine; the
exact `TM.runConfig` statements built on these routes are `GateOneReadB`.

Five route prefixes are defined, all of them *prefixes of the canonical word
itself* — no producer annotation, no scratch region, no marker:

```text
g1TagRouteFrames    r   = bof · tag^units · argSep
g1FieldRouteFrames  r   = bof · tag^units · argSep · index^arg1 · argSep
g1ReadBRouteFrames  r b = g1FieldRouteFrames r · separator · data b
g1ReadBOOBFrames    r   = g1FieldRouteFrames r · separator · output false
g1InstallRouteFrames r  = g1FieldRouteFrames r · index^arg2 · separator
```

and the corresponding split lemmas say each prefix, followed by the rest of the
word, is literally `encodeG1Frames r ++ [.blank]`, the frame word the machine's
initial tape holds.

The routing itself is decided by the *physically rescanned* unary tag run:
`g1RouteMode` is the mode the closing `argSep` selects, and it is a function of
the tag only because the tag run on the tape determines it — no tag is carried
across the T2a rewind, and none is a parameter of the machine.

**Scope.**  The two `g1ReadB*` routes are the `arg2 = 0` case of the operand-2
read: the probe finds the selected data frame (or the `output` destination)
immediately after the `separator`.  For `arg2 > 0` the forward table sends
`bScan` into `bInsSeek`, the installation scan (`g1_bScan_index_install`), and
`g1InstallRouteFrames` is the resulting fifth route prefix —
`g1FieldRouteFrames r · index^arg2 · separator` — whose fold ends at `bProbe2`.
The executed capstone is
`GateOneInstallScan.g1CS_readB_install_scan_exact`.  `bProbe2` is where this
slice stops (`g1_bProbe2_stuck`); the latch, the cursor install and the walk
round are PR2.

The older bridge `bRoundStart` is now unreachable from the forward table
(`g1_bRoundStart_unreachable`) and reads no frame at all
(`g1_bRoundStart_stuck`), so nothing in this development claims that repeating
the thirteen-step rewrite cycle addresses an operand-2 value.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Valid-path plumbing

Three general lemmas about `G1ValidPath`/`g1AdvanceList`: one forced frame, a
self-looping unary run, and concatenation.  Each is the exact shape the route
assembly below needs. -/

/-- One forced forward frame extends a valid path. -/
theorem g1ValidPath_cons {mode next : G1Mode} (hmode : G1ForwardMode mode)
    {frame : G1Frame} (hstep : g1Advance mode frame = next)
    (hnext : next ≠ .reject) {rest : List G1Frame}
    (hrest : G1ValidPath next rest) : G1ValidPath mode (frame :: rest) :=
  ⟨hmode, by rw [hstep]; exact hnext, by rw [hstep]; exact hrest⟩

/-- A unary run of a self-looping frame extends a valid path. -/
theorem g1ValidPath_run {mode : G1Mode} (hmode : G1ForwardMode mode)
    {unit : G1Frame} (hloop : g1Advance mode unit = mode) (k : Nat)
    {rest : List G1Frame} (hrest : G1ValidPath mode rest) :
    G1ValidPath mode (List.replicate k unit ++ rest) := by
  induction k with
  | zero => simpa using hrest
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      exact g1ValidPath_cons hmode hloop
        (fun h => G1ForwardMode.not_reject (h ▸ hmode)) ih

/-- The fold skips a unary run of a self-looping frame. -/
theorem g1AdvanceList_run {mode : G1Mode} {unit : G1Frame}
    (hloop : g1Advance mode unit = mode) (k : Nat) (rest : List G1Frame) :
    g1AdvanceList mode (List.replicate k unit ++ rest) =
      g1AdvanceList mode rest := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, g1AdvanceList_cons, hloop, ih]

/-- Valid paths concatenate. -/
theorem g1ValidPath_append : ∀ {mode : G1Mode} {fs gs : List G1Frame},
    G1ValidPath mode fs → G1ValidPath (g1AdvanceList mode fs) gs →
      G1ValidPath mode (fs ++ gs) := by
  intro mode fs
  induction fs generalizing mode with
  | nil => intro gs _ h2; simpa using h2
  | cons frame rest ih =>
      intro gs h1 h2
      obtain ⟨hm, hne, hrest⟩ := h1
      exact ⟨hm, hne, ih hrest h2⟩

/-! ## The physical tag rescan -/

/-- **The routing decision, as a function of the rescanned tag.**  This is the
mode the `argSep` closing the unary tag run selects on the *second* pass.  The
tag is not remembered across the T2a rewind: `G1Ctx` is `g1Ctx0` at the
handoff, and this mode is reached only by physically re-reading `tag^units`
off the tape. -/
def g1RouteMode : G1Tag → G1Mode
  | .input => .readAStart
  | .const => .rConst0
  | .not => .readAStart
  | .and => .rArg1Binary
  | .or => .rArg1Binary

/-- **The rescan folds the anchor and the unary tag run into the route mode.** -/
theorem g1_tagRescan_advance (t : G1Tag) (rest : List G1Frame) :
    g1AdvanceList .readBStart
        (.bof :: (List.replicate t.units .tag ++ .argSep :: rest)) =
      g1AdvanceList (g1RouteMode t) rest := by
  cases t <;> rfl

/-- **The rescan of the anchor and the tag run is a valid path.**  One forced
frame per `tag` unit, then the `argSep` that selects `g1RouteMode t`. -/
theorem g1_tagRescan_validPath (t : G1Tag) (rest : List G1Frame)
    (hrest : G1ValidPath (g1RouteMode t) rest) :
    G1ValidPath .readBStart
      (.bof :: (List.replicate t.units .tag ++ .argSep :: rest)) := by
  cases t <;>
    (repeat refine ⟨by exact trivial, by decide, ?_⟩) <;> exact hrest

/-! ## The three operand-field walks -/

/-- **The unary `const` literal is decoded physically.**  An immediate `argSep`
is the literal `0`, one `index` then `argSep` is the literal `1`. -/
theorem g1_constField_advance (b : Bool) (rest : List G1Frame) :
    g1AdvanceList .rConst0
        (List.replicate (if b then 1 else 0) .index ++ .argSep :: rest) =
      g1AdvanceList (g1ConstMode b) rest := by
  cases b <;> rfl

theorem g1_constField_validPath (b : Bool) (rest : List G1Frame)
    (hrest : G1ValidPath (g1ConstMode b) rest) :
    G1ValidPath .rConst0
      (List.replicate (if b then 1 else 0) .index ++ .argSep :: rest) := by
  cases b <;>
    (repeat refine ⟨by exact trivial, by decide, ?_⟩) <;> exact hrest

/-- **A binary gate skips the operand-1 field** and stops on the `argSep` that
opens the operand-2 field, entering the operand-2 walk. -/
theorem g1_argOne_advance (a1 : Nat) (rest : List G1Frame) :
    g1AdvanceList .rArg1Binary (List.replicate a1 .index ++ .argSep :: rest) =
      g1AdvanceList .bScan rest := by
  rw [g1AdvanceList_run (mode := .rArg1Binary) (unit := .index) rfl a1]
  rfl

theorem g1_argOne_validPath (a1 : Nat) (rest : List G1Frame)
    (hrest : G1ValidPath .bScan rest) :
    G1ValidPath .rArg1Binary (List.replicate a1 .index ++ .argSep :: rest) :=
  g1ValidPath_run (by exact trivial) rfl a1
    (g1ValidPath_cons (by exact trivial) rfl (by decide) hrest)

/-- **The zero-index probe, success.**  With no unspent `index` unit left, the
walk meets the `separator` at once and the probe reads the data frame behind
it into the store dispatch of that Boolean. -/
theorem g1_probe_advance (b : Bool) (rest : List G1Frame) :
    g1AdvanceList .bScan (.separator :: .data b :: rest) =
      g1AdvanceList (g1StoreMode b) rest := by
  cases b <;> rfl

theorem g1_probe_validPath (b : Bool) (rest : List G1Frame)
    (hrest : G1ValidPath (g1StoreMode b) rest) :
    G1ValidPath .bScan (.separator :: .data b :: rest) := by
  cases b <;>
    (repeat refine ⟨by exact trivial, by decide, ?_⟩) <;> exact hrest

/-- **The zero-index probe, out of range.**  The frame behind the `separator`
is the `output` destination, so the data region is empty and the index selects
nothing: the walk enters the stable out-of-range boundary. -/
theorem g1_probe_oob_advance (rest : List G1Frame) :
    g1AdvanceList .bScan (.separator :: .output false :: rest) =
      g1AdvanceList .bOOB rest := rfl

theorem g1_probe_oob_validPath (rest : List G1Frame)
    (hrest : G1ValidPath .bOOB rest) :
    G1ValidPath .bScan (.separator :: .output false :: rest) :=
  g1ValidPath_cons (by exact trivial) rfl (by decide)
    (g1ValidPath_cons (by exact trivial) rfl (by decide) hrest)

/-! ## The route prefixes of the canonical word -/

/-- The frames the pass-B rescan reads on an arity-1 non-`const` request: the
anchor, the unary tag run and the `argSep` that closes it.  The head then sits
on the first cell of the operand-1 field. -/
def g1TagRouteFrames (r : G1Request) : List G1Frame :=
  .bof :: (List.replicate r.tag.units .tag ++ [.argSep])

/-- The rest of the canonical word after `g1TagRouteFrames`. -/
def g1TagRouteRest (r : G1Request) : List G1Frame :=
  List.replicate r.arg1 .index ++ .argSep ::
    (List.replicate r.arg2 .index ++ .separator ::
      (r.vals.map .data ++ [.output false, .finish, .blank]))

/-- The frames the pass-B rescan reads on a `const` or a binary request: the
anchor, the unary tag run, the `argSep`, the whole operand-1 field and the
`argSep` that opens the operand-2 field. -/
def g1FieldRouteFrames (r : G1Request) : List G1Frame :=
  .bof :: (List.replicate r.tag.units .tag ++ .argSep ::
    (List.replicate r.arg1 .index ++ [.argSep]))

/-- The rest of the canonical word after `g1FieldRouteFrames`. -/
def g1FieldRouteRest (r : G1Request) : List G1Frame :=
  List.replicate r.arg2 .index ++ .separator ::
    (r.vals.map .data ++ [.output false, .finish, .blank])

/-- The complete pass-B route of a binary gate with `arg2 = 0` whose selected
operand-2 value is `b`. -/
def g1ReadBRouteFrames (r : G1Request) (b : Bool) : List G1Frame :=
  g1FieldRouteFrames r ++ [.separator, .data b]

/-- The complete pass-B route of a binary gate with `arg2 = 0` and an empty
data region: the probe meets the `output` destination frame. -/
def g1ReadBOOBFrames (r : G1Request) : List G1Frame :=
  g1FieldRouteFrames r ++ [.separator, .output false]

@[simp] theorem g1TagRouteFrames_length (r : G1Request) :
    (g1TagRouteFrames r).length = r.tag.units + 2 := by
  simp only [g1TagRouteFrames, List.length_cons, List.length_append,
    List.length_replicate]
  rfl

@[simp] theorem g1FieldRouteFrames_length (r : G1Request) :
    (g1FieldRouteFrames r).length = r.tag.units + r.arg1 + 3 := by
  simp only [g1FieldRouteFrames, List.length_cons, List.length_append,
    List.length_replicate, List.length_nil]
  omega

@[simp] theorem g1ReadBRouteFrames_length (r : G1Request) (b : Bool) :
    (g1ReadBRouteFrames r b).length = r.tag.units + r.arg1 + 5 := by
  simp only [g1ReadBRouteFrames, List.length_append, g1FieldRouteFrames_length]
  rfl

@[simp] theorem g1ReadBOOBFrames_length (r : G1Request) :
    (g1ReadBOOBFrames r).length = r.tag.units + r.arg1 + 5 := by
  simp only [g1ReadBOOBFrames, List.length_append, g1FieldRouteFrames_length]
  rfl

/-! ### Splits: every route is a prefix of the canonical word -/

theorem g1TagRoute_split (r : G1Request) :
    g1TagRouteFrames r ++ g1TagRouteRest r = encodeG1Frames r ++ [.blank] := by
  rw [encodeG1Frames_blank_shape]
  simp [g1TagRouteFrames, g1TagRouteRest, List.append_assoc]

theorem g1FieldRoute_split (r : G1Request) :
    g1FieldRouteFrames r ++ g1FieldRouteRest r =
      encodeG1Frames r ++ [.blank] := by
  rw [encodeG1Frames_blank_shape]
  simp [g1FieldRouteFrames, g1FieldRouteRest, List.append_assoc]

theorem g1ReadBRoute_split (r : G1Request) (h2 : r.arg2 = 0) (b : Bool)
    (rest : List Bool) (hv : r.vals = b :: rest) :
    g1ReadBRouteFrames r b ++
        (rest.map .data ++ [.output false, .finish, .blank]) =
      encodeG1Frames r ++ [.blank] := by
  rw [← g1FieldRoute_split r]
  simp only [g1ReadBRouteFrames, g1FieldRouteRest, h2, hv, List.replicate_zero,
    List.nil_append, List.map_cons, List.append_assoc, List.cons_append]

theorem g1ReadBOOB_split (r : G1Request) (h2 : r.arg2 = 0)
    (hv : r.vals = []) :
    g1ReadBOOBFrames r ++ [.finish, .blank] = encodeG1Frames r ++ [.blank] := by
  rw [← g1FieldRoute_split r]
  simp only [g1ReadBOOBFrames, g1FieldRouteRest, h2, hv, List.replicate_zero,
    List.nil_append, List.map_nil, List.append_assoc, List.cons_append]

/-! ### The folded mode and the valid path of each route -/

theorem g1TagRoute_advance (r : G1Request) :
    g1AdvanceList .readBStart (g1TagRouteFrames r) = g1RouteMode r.tag :=
  g1_tagRescan_advance r.tag []

theorem g1TagRoute_validPath (r : G1Request) :
    G1ValidPath .readBStart (g1TagRouteFrames r) :=
  g1_tagRescan_validPath r.tag [] trivial

/-- **`input` and `not` route straight to the pass-A handoff.** -/
theorem g1TagRoute_advance_unary (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1AdvanceList .readBStart (g1TagRouteFrames r) = .readAStart := by
  rw [g1TagRoute_advance]
  rcases ht with h | h <;> rw [h] <;> rfl

/-- **`const` routes to the literal dispatch of its unary bit.** -/
theorem g1FieldRoute_advance_const (r : G1Request) (ht : r.tag = .const)
    (b : Bool) (harg : r.arg1 = if b then 1 else 0) :
    g1AdvanceList .readBStart (g1FieldRouteFrames r) = g1ConstMode b := by
  show g1AdvanceList .readBStart
      (.bof :: (List.replicate r.tag.units .tag ++ .argSep ::
        (List.replicate r.arg1 .index ++ [.argSep]))) = _
  rw [g1_tagRescan_advance, ht, harg]
  exact g1_constField_advance b []

theorem g1FieldRoute_validPath_const (r : G1Request) (ht : r.tag = .const)
    (b : Bool) (harg : r.arg1 = if b then 1 else 0) :
    G1ValidPath .readBStart (g1FieldRouteFrames r) := by
  show G1ValidPath .readBStart
    (.bof :: (List.replicate r.tag.units .tag ++ .argSep ::
      (List.replicate r.arg1 .index ++ [.argSep])))
  refine g1_tagRescan_validPath r.tag _ ?_
  rw [ht, harg]
  exact g1_constField_validPath b [] trivial

/-- **`and` and `or` route to the operand-2 field.**  The head stops on the
first cell of `index^arg2`, i.e. on the `separator` when `arg2 = 0`. -/
theorem g1FieldRoute_advance_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1AdvanceList .readBStart (g1FieldRouteFrames r) = .bScan := by
  show g1AdvanceList .readBStart
      (.bof :: (List.replicate r.tag.units .tag ++ .argSep ::
        (List.replicate r.arg1 .index ++ [.argSep]))) = _
  rw [g1_tagRescan_advance]
  have hmode : g1RouteMode r.tag = .rArg1Binary := by
    rcases ht with h | h <;> rw [h] <;> rfl
  rw [hmode]
  exact g1_argOne_advance r.arg1 []

theorem g1FieldRoute_validPath_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    G1ValidPath .readBStart (g1FieldRouteFrames r) := by
  show G1ValidPath .readBStart
    (.bof :: (List.replicate r.tag.units .tag ++ .argSep ::
      (List.replicate r.arg1 .index ++ [.argSep])))
  refine g1_tagRescan_validPath r.tag _ ?_
  have hmode : g1RouteMode r.tag = .rArg1Binary := by
    rcases ht with h | h <;> rw [h] <;> rfl
  rw [hmode]
  exact g1_argOne_validPath r.arg1 [] trivial

/-- **The complete zero-index operand-2 read, at frame level.** -/
theorem g1ReadBRoute_advance (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool) :
    g1AdvanceList .readBStart (g1ReadBRouteFrames r b) = g1StoreMode b := by
  rw [g1ReadBRouteFrames, g1AdvanceList_append,
    g1FieldRoute_advance_binary r ht]
  exact g1_probe_advance b []

theorem g1ReadBRoute_validPath (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool) :
    G1ValidPath .readBStart (g1ReadBRouteFrames r b) := by
  refine g1ValidPath_append (g1FieldRoute_validPath_binary r ht) ?_
  rw [g1FieldRoute_advance_binary r ht]
  exact g1_probe_validPath b [] trivial

/-- **The complete zero-index out-of-range read, at frame level.** -/
theorem g1ReadBOOB_advance (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1AdvanceList .readBStart (g1ReadBOOBFrames r) = .bOOB := by
  rw [g1ReadBOOBFrames, g1AdvanceList_append,
    g1FieldRoute_advance_binary r ht]
  exact g1_probe_oob_advance []

theorem g1ReadBOOB_validPath (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    G1ValidPath .readBStart (g1ReadBOOBFrames r) := by
  refine g1ValidPath_append (g1FieldRoute_validPath_binary r ht) ?_
  rw [g1FieldRoute_advance_binary r ht]
  exact g1_probe_oob_validPath [] trivial

/-! ### The positive-index branch, at frame level

For `arg2 > 0` the operand-2 walk meets an unspent `index` unit and hands off to
`bInsSeek`, the **installation scan**, which crosses the rest of the operand-2
field, crosses the `separator` and stops at `bProbe2` on the *first* data frame.
`bProbe2` is the explicit local boundary of this slice: it has no outgoing row,
so it reads nothing further (`g1_bProbe2_stuck`), and PR2 supplies the latch and
cursor-install rows behind it.  `bRoundStart` — the bridge into the thirteen-step
rewrite cycle — is no longer a target of the forward table
(`g1_bRoundStart_unreachable`), so nothing here or downstream claims that
iterating that cycle addresses an operand-2 value. -/

theorem g1_bScan_index_install (rest : List G1Frame) :
    g1AdvanceList .bScan (.index :: rest) = g1AdvanceList .bInsSeek rest :=
  rfl

/-- **The installation scan crosses the rest of the operand-2 field.** -/
theorem g1_insSeek_advance (k : Nat) (rest : List G1Frame) :
    g1AdvanceList .bInsSeek (List.replicate k .index ++ .separator :: rest) =
      g1AdvanceList .bProbe2 rest := by
  rw [g1AdvanceList_run (mode := .bInsSeek) (unit := .index) rfl k]
  rfl

theorem g1_insSeek_validPath (k : Nat) (rest : List G1Frame)
    (hrest : G1ValidPath .bProbe2 rest) :
    G1ValidPath .bInsSeek (List.replicate k .index ++ .separator :: rest) :=
  g1ValidPath_run (by exact trivial) rfl k
    (g1ValidPath_cons (by exact trivial) rfl (by decide) hrest)

theorem g1_bRoundStart_stuck : G1Stuck .bRoundStart := by decide

/-- **The installation scan's endpoint reads nothing in this slice.**  `bProbe2`
completes every frame into `reject`, so it is an explicit boundary and no
theorem of this development runs the machine out of it.  PR2 replaces this by
the two latch rows `data b ↦ bLatch b` and the out-of-range row. -/
theorem g1_bProbe2_stuck : G1Stuck .bProbe2 := by decide

/-- **The rewrite-cycle bridge is unreachable from the forward table.**  No
mode/frame pair completes into `bRoundStart`. -/
theorem g1_bRoundStart_unreachable (mode : G1Mode) (frame : G1Frame) :
    g1Advance mode frame ≠ .bRoundStart := by
  revert mode frame; decide

/-! ## The installation route of a positive operand-2 index

The whole prefix the pass-B rescan reads on the positive-index branch:
the binary field route, the operand-2 index field and the `separator`.  It
replaces the bridge route of the previous slice, which is **removed** together
with its fold and valid-path lemmas: the re-pointed table makes them false or
pointless.  The executed capstone is `g1CS_readB_install_scan_exact` in
`GateOneInstallScan`. -/

/-- `g1FieldRouteFrames r · index^arg2 · separator`. -/
def g1InstallRouteFrames (r : G1Request) : List G1Frame :=
  g1FieldRouteFrames r ++ (List.replicate r.arg2 .index ++ [.separator])

/-- The rest of the canonical word after `g1InstallRouteFrames`. -/
def g1InstallRouteRest (r : G1Request) : List G1Frame :=
  r.vals.map .data ++ [.output false, .finish, .blank]

@[simp] theorem g1InstallRouteFrames_length (r : G1Request) :
    (g1InstallRouteFrames r).length = r.tag.units + r.arg1 + r.arg2 + 4 := by
  simp only [g1InstallRouteFrames, List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_singleton]
  omega

theorem g1InstallRoute_split (r : G1Request) :
    g1InstallRouteFrames r ++ g1InstallRouteRest r =
      encodeG1Frames r ++ [.blank] := by
  rw [← g1FieldRoute_split r]
  simp only [g1InstallRouteFrames, g1InstallRouteRest, g1FieldRouteRest,
    List.append_assoc, List.cons_append, List.nil_append]

/-- **The installation route ends at `bProbe2`.**  The first
`index` sends `bScan` into `bInsSeek`, which crosses the remaining `k` units and
the `separator`. -/
theorem g1InstallRoute_advance (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    g1AdvanceList .readBStart (g1InstallRouteFrames r) = .bProbe2 := by
  rw [g1InstallRouteFrames, g1AdvanceList_append,
    g1FieldRoute_advance_binary r ht, h2, List.replicate_succ,
    List.cons_append, g1_bScan_index_install]
  exact g1_insSeek_advance k []

theorem g1InstallRoute_validPath (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    G1ValidPath .readBStart (g1InstallRouteFrames r) := by
  refine g1ValidPath_append (g1FieldRoute_validPath_binary r ht) ?_
  rw [g1FieldRoute_advance_binary r ht, h2, List.replicate_succ,
    List.cons_append]
  exact g1ValidPath_cons (by exact trivial) rfl (by decide)
    (g1_insSeek_validPath k [] trivial)

end Pnp3.Internal.PsubsetPpoly.TM
