import Complexity.TMVerifier.TuringToolkit.GateOneWalkExamples

/-!
# G1 cursor walk, one normal round behind `bSeek`: surface tests

Import-side contracts for one normal round of the cursor walk: the three new
frame-kernel instances, the exact atomic macro of each of its steps on arbitrary
frame-list contexts, the two generic tape-preserving leftward primitives the
turn uses, and the literal encoded-frame probes.

**Every statement below takes the caller's configuration**, tape length and
safety bound.  None starts from `G1M.initialConfig`: the only
real-initial-configuration endpoint on this branch is still the installation
scan, pinned unchanged in `TMGateOneReadBSurfaceTests`.  There is **no
installation driver** here, and nothing composes two macros into a round.
`check_g1CS_walk_seek_exhaust` stops at the boundary `.bExh .p0`, which has no
successful frame row; the terminal exhaustion path is PR2b2.  Deliberately
absent: any walk invariant, iteration or loop clock, addressing, positive-index
operand-value read, aggregated out-of-range claim, repair, pass A, output write,
`TM.accepts`, gate-semantics, full-clock or padded-tape surface.

This is an audit surface: it pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneWalkSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

-- The frame class the walk's right-running scan crosses; `G1InstallSkip` and
-- the two `_fix` lemmas are merged and reused.
#check @G1WalkSkip
#check @g1Advance_bFwd_of_skip
#check @g1_bFwd_rows
#check @g1_bExh_stuck
-- The reverse-seek table and the three new kernel instances.
#check @g1WalkRevAdvance
#check @g1WalkRevComplete
#check @G1WalkMode
#check @G1WalkStop
#check @g1WalkRevAdvance_of_skip
#check @g1WalkScanner
#check @g1WalkScanner_machine
#check @g1DecWriter
#check @g1RestoreWriter
-- The generic tape-preserving leftward primitives, and the new layouts.
#check @Phased.holdLeft
#check @Phased.holdWalk4
#check @G1WalkExamples.g1WalkFramesRound1
#check @G1WalkExamples.g1WalkFramesMarked1
#check @G1WalkExamples.g1WalkFramesRestored1
#check @G1WalkExamples.g1WalkFrames_length
#check @G1WalkExamples.ctx1

theorem check_g1WalkFrames_length :
    G1WalkExamples.g1WalkFramesRound1.length = 16 ∧
      G1WalkExamples.g1WalkFramesMarked1.length = 16 ∧
      G1WalkExamples.g1WalkFramesRestored1.length = 16 ∧
      (G1WalkExamples.g1WalkFramesRound1.flatMap G1Frame.bits).length = 64 ∧
      (G1WalkExamples.g1WalkFramesMarked1.flatMap G1Frame.bits).length = 64 ∧
      (G1WalkExamples.g1WalkFramesRestored1.flatMap G1Frame.bits).length = 64 :=
  G1WalkExamples.g1WalkFrames_length

/-! ## The atomic macros, pinned exactly.  Each wrapper restates its macro
verbatim, so a later slice cannot silently drop the tape equation, move the
head, change the step count or specialise the surrounding frame list. -/

/-- **The seek stops on the rightmost remaining `index`**, on its first cell. -/
theorem check_g1CS_walk_seek_to_index (n : Nat)
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
          .bSeek .p3 false false false ctx)
        (4 * skipped.length + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
        .bDec .p0 false false false ctx :=
  g1CS_walk_seek_to_index n pre skipped suffix ctx hskip hsafe

/-- **The exhaustion endpoint and boundary.**  The seek stops on the
`argSep` that opens the operand-2 field, in `bExh` — which has no successful
frame row, so nothing runs past this configuration. -/
theorem check_g1CS_walk_seek_exhaust (n : Nat)
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.argSep :: skipped ++ suffix).flatMap G1Frame.bits))
          .bSeek .p3 false false false ctx)
        (4 * skipped.length + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ suffix).flatMap G1Frame.bits))
        .bExh .p0 false false false ctx :=
  g1CS_walk_seek_exhaust n pre skipped suffix ctx hskip hsafe

/-- **The `index ↦ spent` write** replaces exactly one frame. -/
theorem check_g1CS_walk_mark (n : Nat) (pre suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .bDec .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx :=
  g1CS_walk_mark n pre suffix ctx hsafe

/-- **Seek plus mark**, in `4k + 8` steps. -/
theorem check_g1CS_walk_seek_mark (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
          .bSeek .p3 false false false ctx)
        (4 * skipped.length + 8) =
      g1AlignedConfig n (4 * pre.length + 4) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.spent :: skipped ++ suffix).flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx :=
  g1CS_walk_seek_mark n pre skipped suffix ctx hskip hsafe

/-- **The forward scan back to the cursor** is read-only. -/
theorem check_g1CS_walk_fwd_to_cursor (n : Nat)
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx)
        (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .bTurn .p0 false false false ctx :=
  g1CS_walk_fwd_to_cursor n pre skipped suffix ctx hskip hsafe

/-- **The turn** leaves an arbitrary tape untouched. -/
theorem check_g1CS_walk_turn (n k : Nat) (hsafe : k + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (k + 4) hsafe tape .bTurn .p0 false false false ctx)
        4 =
      g1AlignedConfig n k (by omega) tape
        (g1RestoreMode ctx.vB) .p0 false false false ctx :=
  g1CS_walk_turn n k hsafe tape ctx

/-- **The cursor restore** replaces the `cursor` by `data b`. -/
theorem check_g1CS_walk_restore (n : Nat) (pre suffix : List G1Frame) (b : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        (g1RestoreMode b) .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data b :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx :=
  g1CS_walk_restore n pre suffix b ctx hsafe

/-- **The generic four-step turn**, at the shared phased layer. -/
theorem check_Phased_holdWalk4 {S : Type} [Fintype S] [DecidableEq S]
    (U : ConstStatePhasedProgram S) (ph : Fin U.numPhases) (n k : Nat)
    (hsafe : k + 4 < (Phased.machine U).tapeLength n)
    (tape : Fin ((Phased.machine U).tapeLength n) → Bool) (q3 q2 q1 q0 qe : S)
    (h3 : ∀ scan : Bool, U.transition ph q3 scan = (ph, q2, scan, Move.left))
    (h2 : ∀ scan : Bool, U.transition ph q2 scan = (ph, q1, scan, Move.left))
    (h1 : ∀ scan : Bool, U.transition ph q1 scan = (ph, q0, scan, Move.left))
    (h0 : ∀ scan : Bool, U.transition ph q0 scan = (ph, qe, scan, Move.left)) :
    TM.runConfig (M := Phased.machine U)
        (Phased.alignedAt U ph n (k + 4) hsafe tape q3) 4 =
      Phased.alignedAt U ph n k (by omega) tape qe :=
  Phased.holdWalk4 U ph n k hsafe tape q3 q2 q1 q0 qe h3 h2 h1 h0

/-! ## Representative literal probes, pinned exactly -/

open G1WalkExamples in
/-- Head `43 → 32` in `20` steps: ordinal `7` becomes `spent`. -/
theorem check_walk_seek_mark (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkFramesRound1.flatMap G1Frame.bits))
        .bSeek .p3 false false false ctx1) 20 =
      g1AlignedConfig n 32 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx1 :=
  walk_seek_mark n hsafe

open G1WalkExamples in
/-- Head `43 → 24` in `20` steps on the marked layout: with operand-2 exhausted
the seek stops on the opening `argSep` in `bExh`. -/
theorem check_walk_seek_exhaust (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bSeek .p3 false false false ctx1) 20 =
      g1AlignedConfig n 24 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bExh .p0 false false false ctx1 :=
  walk_seek_exhaust n hsafe

open G1WalkExamples in
/-- Head `44 → 48` in `4` steps: ordinal `11` goes back to `data true` and the
probe re-opens, closing the round. -/
theorem check_walk_restore (n : Nat) (hsafe : 48 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 44 (by omega)
        (g1ListTape (g1WalkFramesMarked1.flatMap G1Frame.bits))
        .bRestoreTrue .p0 false false false ctx1) 4 =
      g1AlignedConfig n 48 (by omega)
        (g1ListTape (g1WalkFramesRestored1.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx1 :=
  walk_restore n hsafe

end Pnp3.Tests.TMGateOneWalkSurface
