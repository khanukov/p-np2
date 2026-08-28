import Complexity.TMVerifier.TuringToolkit.GateOneReadB

/-!
# G1: the installation scan of the positive-index branch

**Progress classification: Infrastructure.**

The **installation scan** that the re-pointed positive-index row of `g1Advance`
opens.  For a canonical `and`/`or` request with `arg2 > 0` the pass-B walk
`bScan` meets an unspent `index`, enters `bInsSeek`, crosses the rest of the
operand-2 field and the `separator`, and stops at `bProbe2` on the **first cell
after the separator**: a `.data` frame when `r.vals` is nonempty and `.output
false` otherwise.
`g1CS_readB_install_scan_exact` is that run from the
**real** initial configuration `G1M.initialConfig (g1Point (encodeG1 r))`; it
replaces the retired first-round route of `GateOneIndexRound`.

`bProbe2` is the **live-route boundary**: the two rows behind it — the latch and
the cursor install — are exercised only from caller-supplied configurations in
`GateOneProbeInstall`, and no theorem here or there runs them from a real
initial configuration.

This module is deliberately *narrow*.  It imports `GateOneReadB` and nothing
else, so it depends only on the existing forward frame scanner
(`g1FrameScanner`); it uses **no** reverse scanner, **no** frame-writer
instance, and none of the tape-preserving turn helpers.  The only new frame-level
support it needs is the class of frames the installation scan crosses
(`G1InstallSkip`) and the two generic "the mode is fixed on this run" lemmas
`g1ValidPath_fix`/`g1AdvanceList_fix`, which `GateOneRouting` has only in the
homogeneous `List.replicate` form.

**Explicit deferrals.**  Nothing *here* latches a value, installs a cursor,
seeks, marks, restores, turns, iterates, or reads an operand-2 value for
`arg2 > 0`; the probe, latch and cursor-install macros are `GateOneProbeInstall`,
on caller-supplied configurations.  There is no walk invariant, no installation
driver, no loop clock, no out-of-range aggregation, no repair, no pass A, no
output write, no `TM.accepts`, no gate-semantics correctness, no full-clock
theorem and no padded-tape claim: the real-run statements are scoped to the
exact tape `encodeG1 r`, and the frame-list macro takes its layout and safety
bound from the caller.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- Frames the *installation* scan crosses: unspent and consumed index units. -/
def G1InstallSkip : G1Frame → Prop
  | .index => True
  | .spent => True
  | _ => False

instance : DecidablePred G1InstallSkip := fun f => by
  cases f <;> first | exact isTrue trivial | exact isFalse id

theorem g1Advance_bInsSeek_of_skip {f : G1Frame} (h : G1InstallSkip f) :
    g1Advance .bInsSeek f = .bInsSeek := by
  cases f <;> first | rfl | exact (show False from h).elim

/-! A run of frames the forward table *fixes* in a mode extends a valid path
and is skipped by the fold.  `GateOneRouting` has the `List.replicate` form;
these two are the heterogeneous form the installation scan needs, because the
operand-2 field it crosses may mix `index` and `spent`. -/

theorem g1ValidPath_fix {mode : G1Mode} (hmode : G1ForwardMode mode)
    (rest : List G1Frame) (hrest : G1ValidPath mode rest) :
    ∀ fs : List G1Frame, (∀ f ∈ fs, g1Advance mode f = mode) →
      G1ValidPath mode (fs ++ rest) := by
  intro fs
  induction fs with
  | nil => intro _; simpa using hrest
  | cons f tail ih =>
      intro hfix
      have hf : g1Advance mode f = mode := hfix f (by simp)
      refine ⟨hmode, ?_, ?_⟩
      · rw [hf]; exact fun h => G1ForwardMode.not_reject (h ▸ hmode)
      · rw [hf]; exact ih fun g hg => hfix g (by simp [hg])

theorem g1AdvanceList_fix {mode : G1Mode} (rest : List G1Frame) :
    ∀ fs : List G1Frame, (∀ f ∈ fs, g1Advance mode f = mode) →
      g1AdvanceList mode (fs ++ rest) = g1AdvanceList mode rest := by
  intro fs
  induction fs with
  | nil => intro _; simp
  | cons f tail ih =>
      intro hfix
      rw [List.cons_append, g1AdvanceList_cons, hfix f (by simp),
        ih fun g hg => hfix g (by simp [hg])]

/-! ## The installation scan on an arbitrary frame list

One macro, on a caller-supplied layout `pre ++ skipped ++ separator :: suffix`
with `skipped` an arbitrary run of `index`/`spent` frames.  It is the *existing*
forward frame scanner, so the tape and the carried context are untouched and the
step count is four per crossed frame. -/

/-- **The installation scan.**  `4 * (k + 1)` read-only steps cross the rest of
the operand-2 field and the `separator`, opening the probe behind it. -/
theorem g1CS_walk_install_scan (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1InstallSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.separator :: suffix).flatMap
            G1Frame.bits))
        .bInsSeek .p0 false false false ctx)
        (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.separator :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx := by
  have hfix : ∀ f ∈ skipped, g1Advance .bInsSeek f = .bInsSeek :=
    fun f hf => g1Advance_bInsSeek_of_skip (hskip f hf)
  have hlen : (skipped ++ [G1Frame.separator]).length = skipped.length + 1 := by
    simp
  have hlist : pre ++ (skipped ++ [G1Frame.separator]) ++ suffix =
      pre ++ skipped ++ G1Frame.separator :: suffix := by
    simp [List.append_assoc]
  have hpath : G1ValidPath .bInsSeek (skipped ++ [G1Frame.separator]) :=
    g1ValidPath_fix (mode := .bInsSeek) trivial [G1Frame.separator]
      ⟨trivial, by decide, trivial⟩ skipped hfix
  have hfold :
      g1AdvanceList .bInsSeek (skipped ++ [G1Frame.separator]) = .bProbe2 := by
    rw [g1AdvanceList_fix (mode := .bInsSeek) [G1Frame.separator] skipped hfix]
    rfl
  have hscan := g1FrameScanner_scanFrames n pre (skipped ++ [G1Frame.separator])
    suffix .bInsSeek ctx ((g1FrameScanner_validPath _ _).mpr hpath)
    (by rw [hlen]; exact hsafe)
  simp only [hlist, hlen, g1AlignedFrame_eq, g1FrameScanner_advanceList, hfold]
    at hscan
  exact hscan

/-! ## The re-pointed positive-index route, from the **real initial
configuration**.  It replaces the first-round route of the previous slice, which
is **removed**: the re-pointed table no longer reaches the bridge it started
from.  The latch, the cursor install and everything after them from a real
initial configuration are the **installation driver**, and are deferred. -/

/-- Steps from `initialConfig` to the endpoint of the installation scan. -/
def g1InstallScanSteps (r : G1Request) : Nat :=
  g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + r.arg2 + 4)

theorem g1InstallScanSteps_eq (r : G1Request) :
    g1InstallScanSteps r = g1FieldRouteSteps r + 4 * (r.arg2 + 1) := by
  unfold g1InstallScanSteps g1FieldRouteSteps
  omega

/-- **It fits the unchanged public clock**; `g1Clock` is not widened. -/
theorem g1InstallScanSteps_le_clock (r : G1Request) :
    g1InstallScanSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + r.arg1 + r.arg2 + 4)
    (by omega)
  simp only [g1InstallScanSteps]
  omega

/-- **The positive-index branch reaches the scan's endpoint, exactly.**  For a
canonical `and`/`or` request with a non-empty operand-2 field, exactly
`g1InstallScanSteps r` genuine steps validate the word, rewind, physically
rescan the tag, cross both operand fields and the `separator`, landing in
`bProbe2` on the **first cell after the separator**, context still `g1Ctx0`,
tape **bit-for-bit the initial tape**.  This is the re-pointed reachability
statement, *not* an addressing claim: nothing here reads that frame, latches a
value, installs a cursor, iterates a round, or says which data frame the operand
selects.  The frame is `.data r.vals[0]` when data is nonempty and `.output
false` otherwise.  The cursor-walk rows behind `bProbe2` are never run from this
configuration; their macros take the caller's own. -/
theorem g1CS_readB_install_scan_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + 4))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bProbe2 .p0 false false false g1Ctx0 := by
  have hsafe : 4 * (g1InstallRouteFrames r).length <
      G1M.tapeLength (encodeG1 r).length := by
    rw [g1InstallRouteFrames_length]
    exact g1_route_lt_tapeLength r _ (by omega)
  have h := g1CS_readB_scan r hc (g1InstallRouteFrames r)
    (g1InstallRouteRest r) (g1InstallRoute_split r)
    (g1InstallRoute_validPath r ht k h2) hsafe
  rw [g1InstallRoute_advance r ht k h2] at h
  simpa [g1InstallScanSteps] using h

theorem g1CS_readB_install_scan_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r)).head : Nat) =
      4 * (r.tag.units + r.arg1 + r.arg2 + 4) := by
  rw [g1CS_readB_install_scan_exact r hc ht k h2]; rfl

/-- **The installation scan is non-destructive.**  Not one tape cell changes, so
no marker is left behind and no data cursor has to be restored. -/
theorem g1CS_readB_install_scan_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_readB_install_scan_exact r hc ht k h2]; rfl

/-- The endpoint state, separately: the boundary `bProbe2`, with the context
still at its initial value. -/
theorem g1CS_readB_install_scan_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r)).state.snd = g1Probe2State g1Ctx0 := by
  rw [g1CS_readB_install_scan_exact r hc ht k h2]; rfl

end Pnp3.Internal.PsubsetPpoly.TM
