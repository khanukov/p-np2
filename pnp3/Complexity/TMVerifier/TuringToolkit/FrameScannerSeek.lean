import Complexity.TMVerifier.TuringToolkit.FrameScannerReverse

/-!
# The generic seek-until-marker layer

`FrameScannerReverse` proves the reverse macrostep and the exact reverse list
induction.  This module is the driver every destructive pass needs on top of
them: **run the reverse scan across an arbitrary run of skippable frames until
a distinguished marker/anchor frame stops it**, in an arbitrary surrounding
frame list `pre ++ marker :: skipped ++ suffix`.

`revSkipRun` is the skip half — exactly `4 * skipped.length` steps, head from
the last cell of the last skipped frame to the last cell of the marker, tape,
mode and context unchanged — and `revSeekToMarker` is the full driver:
`4 * skipped.length + 4` steps, ending on the *first* cell of the marker in
`stopState (revAdvance mode marker)`.  Both are exact configuration equalities,
so they pin head, tape, mode and carried context at once;
`revSeekToMarker_head` names the head projection separately.  The kernel's
`revScanToAnchor` is the `pre = []` case, so the marker no longer has to sit at
the left end of the tape.

**Obligation hygiene.**  The desired run is *not* packaged as a field or a
hypothesis-shaped abbreviation.  The premises are exactly: two mode facts of the
scanner's own table (the seek mode reads right to left and does not stop by
itself); one *frame predicate* — every frame of `skipped` is fixed by the
reverse table in that mode, i.e. skippable; one *table fact about the marker* —
`Stop (revAdvance mode marker)`; and physical head safety.  Nothing is assumed
about which frames those are, how many there are, or what the control does
afterwards.

**Non-goals.**  No addressing, validation, acceptance or rejection claim, and
no statement about non-canonical or physically padded tapes.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

namespace ReverseFrameScanner

variable {S : Type v} [Fintype S] [DecidableEq S] {F Mode Aux : Type v}

/-- **The skip half of a seek.**  A run of frames that the reverse table fixes
in `mode` is crossed in exactly four genuine TM steps per frame, leaving the
mode, the carried context and the list-backed tape untouched, with the head
landing on the last cell of the marker frame that precedes the run. -/
theorem revSkipRun (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (marker : F) (skipped suffix : List F) (mode : Mode)
    (a : Aux) (hrev : K.Reverse mode) (hnostop : ¬ K.Stop mode)
    (hskip : ∀ f ∈ skipped, K.revAdvance mode f = mode)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + skipped.length) + 3) (by omega)
          (frameListTape
            ((pre ++ marker :: skipped ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * skipped.length) =
      K.revAligned n (4 * pre.length + 3) (by omega)
        (frameListTape
          ((pre ++ marker :: skipped ++ suffix).flatMap K.codec.bits))
        mode a := by
  obtain ⟨hpath, hfold⟩ := K.revValidPath_const hrev hnostop skipped hskip
  have hscan := K.revScanFrames n pre marker skipped suffix mode a hpath hsafe
  rw [hfold] at hscan
  exact hscan

/-- **The generic seek-until-marker.**  From the last cell of the last skippable
frame, `4 * skipped.length + 4` genuine TM steps cross the whole run right to
left and read the marker, which stops the pass: the head finishes on the
*first* cell of the marker, `4 * pre.length`, the list-backed tape and the
carried context are untouched, and the control is in
`stopState (revAdvance mode marker)`. -/
theorem revSeekToMarker (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (marker : F) (skipped suffix : List F) (mode : Mode)
    (a : Aux) (hrev : K.Reverse mode) (hnostop : ¬ K.Stop mode)
    (hskip : ∀ f ∈ skipped, K.revAdvance mode f = mode)
    (hstop : K.Stop (K.revAdvance mode marker))
    (hsafe : 4 * (pre.length + skipped.length) + 4 < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + skipped.length) + 3) (by omega)
          (frameListTape
            ((pre ++ marker :: skipped ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * skipped.length + 4) =
      K.alignedConfigQ n (4 * pre.length) (by omega)
        (frameListTape
          ((pre ++ marker :: skipped ++ suffix).flatMap K.codec.bits))
        (K.stopState (K.revAdvance mode marker) a) := by
  have hmarkerSafe : 4 * pre.length + 4 < K.machine.tapeLength n := by omega
  have hbits : physicalBitsAt (h := 4 * pre.length) hmarkerSafe
      (frameListTape (L := K.machine.tapeLength n)
        ((pre ++ marker :: skipped ++ suffix).flatMap K.codec.bits)) =
      K.codec.bits marker := by
    have raw := physicalBitsAt_flatMap (L := K.machine.tapeLength n) K.codec pre
      (skipped ++ suffix) marker hmarkerSafe
    simpa [List.append_assoc] using raw
  have hanchor := K.revAnchorStep n (4 * pre.length) hmarkerSafe
    (frameListTape (L := K.machine.tapeLength n)
      ((pre ++ marker :: skipped ++ suffix).flatMap K.codec.bits))
    mode marker a hrev hstop hbits
  rw [runConfig_add,
    K.revSkipRun n pre marker skipped suffix mode a hrev hnostop hskip hsafe,
    hanchor]

/-- **Head placement of a seek**: the first cell of the marker frame. -/
theorem revSeekToMarker_head (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (marker : F) (skipped suffix : List F) (mode : Mode)
    (a : Aux) (hrev : K.Reverse mode) (hnostop : ¬ K.Stop mode)
    (hskip : ∀ f ∈ skipped, K.revAdvance mode f = mode)
    (hstop : K.Stop (K.revAdvance mode marker))
    (hsafe : 4 * (pre.length + skipped.length) + 4 < K.machine.tapeLength n) :
    ((TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + skipped.length) + 3) (by omega)
          (frameListTape
            ((pre ++ marker :: skipped ++ suffix).flatMap K.codec.bits))
          mode a)
        (4 * skipped.length + 4)).head : Nat) = 4 * pre.length := by
  rw [K.revSeekToMarker n pre marker skipped suffix mode a hrev hnostop hskip
    hstop hsafe]
  rfl

end ReverseFrameScanner

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
