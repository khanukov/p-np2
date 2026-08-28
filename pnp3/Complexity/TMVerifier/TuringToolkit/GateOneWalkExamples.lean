import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkKernel

/-!
# G1 cursor walk: concrete encoded-frame probes of the remaining macros

**Progress classification: Infrastructure.**  One literal probe per macro of
`GateOneWalkKernel`, on the **reused** request
`G1InstallScanExamples.g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩` —
**fifteen** encoded frames and `60` input cells; the explicit list-backed
layouts append one `blank`, the frame the machine's own tape supplies past the
input, so each has **sixteen** frames and `64` bits.  The prefix
`bof · tag⁴ · argSep · argSep` lies at ordinals `0 … 6`, the operand-2 field at
ordinals `7 … 8` and the data region from ordinal `10`.

The request, its canonicity and length, the initial layout `g1WalkInitFrames`,
the initial-tape equation, the `169`-step installation-scan capstones and the
probe / latch / cursor-install probes are **not restated**: they are
`GateOneInstallScanExamples` and `GateOneProbeInstallExamples`.  New here are
the three intermediate layouts one normal round passes through, at `j = 1`
(before the mark, after it, and after the cursor restore), and the two layouts
of the **terminal** path at `j = 2 = arg2`: `g1WalkFramesTerminal`, with the
operand-2 field entirely `spent` and the cursor on ordinal `12`, and
`g1WalkFramesFinal`, after the terminal restore — data region exactly `vals`,
**no `cursor` anywhere**, head handed off to `readAResetStart`.

Every head position and step count is a literal, and every probe is an exact
`G1M` configuration equality — but each takes the tape length `n` and one
numeric safety bound from the **caller**.  Nothing composes the macros: no round
is chained, the terminal path is not chained to a round, no run here starts from
`G1M.initialConfig`, no invariant is stated and no arbitrary operand-2 index is
read.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1WalkExamples

open G1InstallScanExamples

/-- At `j = 1`: the cursor on ordinal `11` hides `vals[1] = true`, carried in
`G1Ctx.vB`; ordinal `7` is the one `index` left. -/
def g1WalkFramesRound1 : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .spent, .separator,
    .data false, .cursor, .data true, .output false, .finish, .blank]

/-- `g1WalkFramesRound1` after the `index ↦ spent` write of the round. -/
def g1WalkFramesMarked1 : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
    .data false, .cursor, .data true, .output false, .finish, .blank]

/-- `g1WalkFramesMarked1` after the cursor is restored to `data vals[1]`. -/
def g1WalkFramesRestored1 : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
    .data false, .data true, .data true, .output false, .finish, .blank]

/-- The layout at `j = 2 = arg2`: the operand-2 field entirely `spent`, so the
reverse seek finds no `index` and stops on the opening `argSep`; the cursor sits
on ordinal `12`, hiding `vals[2] = true`. -/
def g1WalkFramesTerminal : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
    .data false, .data true, .cursor, .output false, .finish, .blank]

/-- After the terminal restore: the data region is exactly `vals` and there is
**no `cursor` anywhere**.  It coincides with `g1WalkFramesRestored1` here only
because `vals[1] = vals[2]`; the two names mark the two roles. -/
def g1WalkFramesFinal : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
    .data false, .data true, .data true, .output false, .finish, .blank]

/-- Every walk layout is the merged initial layout with ordinals rewritten:
same request, same sixteen frames, same `64` bits. -/
theorem g1WalkFrames_length :
    g1WalkFramesRound1.length = 16 ∧
      g1WalkFramesMarked1.length = 16 ∧
      g1WalkFramesRestored1.length = 16 ∧
      (g1WalkFramesRound1.flatMap G1Frame.bits).length = 64 ∧
      (g1WalkFramesMarked1.flatMap G1Frame.bits).length = 64 ∧
      (g1WalkFramesRestored1.flatMap G1Frame.bits).length = 64 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two terminal layouts have the same shape as the round's: same request,
same sixteen frames, same `64` bits. -/
theorem g1WalkFramesTerminal_length :
    g1WalkFramesTerminal.length = 16 ∧
      g1WalkFramesFinal.length = 16 ∧
      (g1WalkFramesTerminal.flatMap G1Frame.bits).length = 64 ∧
      (g1WalkFramesFinal.flatMap G1Frame.bits).length = 64 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The final tape is cursor-free.**  No frame of `g1WalkFramesFinal` is the
`cursor`: the terminal restore is the step that removes the walk's last marker
from the tape. -/
theorem g1WalkFramesFinal_no_cursor : G1Frame.cursor ∉ g1WalkFramesFinal := by
  decide

/-- The latched context of the round: `vB = vals[1] = true`.  It is also the
latched context of the terminal path here, since `vals[2] = vals[1]`. -/
def ctx1 : G1Ctx := g1Ctx0.withVB true

/-- **Reverse seek plus mark.**  Head `43` (just left of the cursor) to `32` in
`4 * 3 + 8 = 20` steps: the `index` at ordinal `7` becomes `spent`. -/
theorem walk_seek_mark (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkFramesRound1.flatMap G1Frame.bits))
        .bSeek .p3 false false false ctx1) 20 =
      g1AlignedConfig n 32 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx1 := by
  have h := g1CS_walk_seek_mark n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep]
    [.spent, .separator, .data false]
    [.cursor, .data true, .output false, .finish, .blank] ctx1
    (by decide)
    (by simpa using hsafe)
  simpa [g1WalkFramesRound1, g1WalkFramesMarked1] using h

/-- **The exhaustion outcome.**  From the *same* head `43` on
the marked layout — operand-2 now `spent²`, so no `index` is left — `4 * 4 + 4 =
20` steps stop the seek on the **opening `argSep`** at cell `24`, tape
untouched, in `bExh`.  `walk_exh_to_cursor` below starts from that head and
mode, but on the `j = 2` layout, and nothing chains the two. -/
theorem walk_seek_exhaust (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bSeek .p3 false false false ctx1) 20 =
      g1AlignedConfig n 24 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bExh .p0 false false false ctx1 := by
  have h := g1CS_walk_seek_exhaust n
    [.bof, .tag, .tag, .tag, .tag, .argSep]
    [.spent, .spent, .separator, .data false]
    [.cursor, .data true, .output false, .finish, .blank] ctx1
    (by decide)
    (by simpa using hsafe)
  simpa [g1WalkFramesMarked1] using h

/-- **The forward scan back to the cursor.**  Cell `32` to `48` in
`4 * (3 + 1) = 16` steps, reading the `cursor` at ordinal `11`. -/
theorem walk_fwd_to_cursor (n : Nat) (hsafe : 48 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 32 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx1) 16 =
      g1AlignedConfig n 48 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bTurn .p0 false false false ctx1 := by
  have h := g1CS_walk_fwd_to_cursor n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent]
    [.spent, .separator, .data false]
    [.data true, .output false, .finish, .blank] ctx1
    (by decide)
    (by simpa using hsafe)
  simpa [g1WalkFramesMarked1] using h

/-- **The turn.**  Cell `48` back onto `44`, the cursor's first cell, into the
restore writer of the latched bit `vB = true`. -/
theorem walk_turn (n : Nat) (hsafe : 48 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 48 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bTurn .p0 false false false ctx1) 4 =
      g1AlignedConfig n 44 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bRestoreTrue .p0 false false false ctx1 := by
  have h := g1CS_walk_turn n 44 (by omega)
    (g1ListTape (n := n) (g1WalkFramesMarked1.flatMap G1Frame.bits)) ctx1
  simpa [ctx1, g1RestoreMode] using h

/-- **The cursor restore.**  Ordinal `11` back into `data true`, the latched
value; the probe opens on cell `48`. -/
theorem walk_restore (n : Nat) (hsafe : 48 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 44 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bRestoreTrue .p0 false false false ctx1) 4 =
      g1AlignedConfig n 48 (by omega)
        (g1ListTape (g1WalkFramesRestored1.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx1 := by
  have h := g1CS_walk_restore n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
      .data false]
    [.data true, .output false, .finish, .blank] true ctx1
    (by simpa using hsafe)
  simpa [g1WalkFramesMarked1, g1WalkFramesRestored1, g1RestoreMode] using h

/-! ## The terminal path, at `j = 2 = arg2`

Three literal probes on `g1WalkFramesTerminal`/`g1WalkFramesFinal`.  Each takes
`n` and one safety bound from the caller; nothing chains them to each other or
to the round's probes above. -/

/-- **The exhaustion scan.**  The opening `argSep` at cell `24` to cell `52` in
`4 * (5 + 2) = 28` read-only steps, reading the cursor at ordinal `12` and
entering the terminal turn. -/
theorem walk_exh_to_cursor (n : Nat) (hsafe : 52 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 24 (by omega)
        (g1ListTape (g1WalkFramesTerminal.flatMap G1Frame.bits))
        .bExh .p0 false false false ctx1) 28 =
      g1AlignedConfig n 52 (by omega)
        (g1ListTape (g1WalkFramesTerminal.flatMap G1Frame.bits))
        .bTurnFin .p0 false false false ctx1 := by
  have h := g1CS_walk_exh_to_cursor n
    [.bof, .tag, .tag, .tag, .tag, .argSep]
    [.spent, .spent, .separator, .data false, .data true]
    [.output false, .finish, .blank] ctx1
    (by decide)
    (by simpa using hsafe)
  simpa [g1WalkFramesTerminal] using h

/-- **The terminal turn.**  Cell `52` back onto `48`, the last cursor's first
cell, into the *terminal* writer of the latched bit `vB = true`. -/
theorem walk_turn_fin (n : Nat) (hsafe : 52 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 52 (by omega)
        (g1ListTape (g1WalkFramesTerminal.flatMap G1Frame.bits))
        .bTurnFin .p0 false false false ctx1) 4 =
      g1AlignedConfig n 48 (by omega)
        (g1ListTape (g1WalkFramesTerminal.flatMap G1Frame.bits))
        .bFinTrue .p0 false false false ctx1 := by
  have h := g1CS_walk_turn_fin n 48 (by omega)
    (g1ListTape (n := n) (g1WalkFramesTerminal.flatMap G1Frame.bits)) ctx1
  simpa [ctx1, g1FinMode] using h

/-- **The terminal restore.**  The last `cursor`, at ordinal `12`, back into
`data true`, handing off to `readAResetStart` on cell `52`.  The resulting tape
is `g1WalkFramesFinal`: data region exactly `vals` and **no cursor anywhere**
(`g1WalkFramesFinal_no_cursor`). -/
theorem walk_fin_restore (n : Nat) (hsafe : 52 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 48 (by omega)
        (g1ListTape (g1WalkFramesTerminal.flatMap G1Frame.bits))
        .bFinTrue .p0 false false false ctx1) 4 =
      g1AlignedConfig n 52 (by omega)
        (g1ListTape (g1WalkFramesFinal.flatMap G1Frame.bits))
        .readAResetStart .p0 false false false ctx1 := by
  have h := g1CS_walk_fin_restore n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
      .data false, .data true]
    [.output false, .finish, .blank] true ctx1
    (by simpa using hsafe)
  simpa [g1WalkFramesTerminal, g1WalkFramesFinal, g1FinMode] using h

end G1WalkExamples

end Pnp3.Internal.PsubsetPpoly.TM
