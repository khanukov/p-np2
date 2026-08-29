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

**Mixed-boundary seeks.**  A pass whose *skip class changes* partway — it
crosses an outer region in one reverse mode, meets a distinguished `boundary`
frame that switches it into a second reverse mode, and crosses an inner region
in that second mode before the marker stops it — is still one reverse scan,
because `ReverseFrameScanner.revAdvance` already takes the mode as an argument.
`revSkipToBoundary` is the mode-switching half (`4 * outer.length + 4` steps,
ending reverse-aligned on the last cell of the frame *before* the boundary, in
the second mode) and `revSeekAcrossBoundary` composes it with `revSeekToMarker`
into the full two-region driver.  Nothing about the two regions is assumed
beyond the two skip predicates and the one boundary equation, and the field
selector therefore lives in the *mode*, never in the carried context.

**Obligation hygiene.**  The desired run is *not* packaged as a field or a
hypothesis-shaped abbreviation.  The premises are exactly: two mode facts of the
scanner's own table (the seek mode reads right to left and does not stop by
itself); one *frame predicate* — every frame of `skipped` is fixed by the
reverse table in that mode, i.e. skippable; one *table fact about the marker* —
`Stop (revAdvance mode marker)`; and physical head safety.  Nothing is assumed
about which frames those are, how many there are, or what the control does
afterwards.  The mixed-boundary lemmas add exactly one further table fact,
`revAdvance mOut boundary = mIn`.

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

/-! ### Mixed-boundary seeks: two regions, two reverse modes, one pass -/

/-- Head positions that are equal as numbers give equal reverse-aligned
configurations.  Pure `Fin`/proof-irrelevance plumbing. -/
private theorem revAligned_congr (K : ReverseFrameScanner S F Mode Aux)
    (n h h' : Nat) (hh : h < K.machine.tapeLength n)
    (hh' : h' < K.machine.tapeLength n) (heq : h = h')
    (tape : Fin (K.machine.tapeLength n) → Bool) (m : Mode) (a : Aux) :
    K.revAligned n h hh tape m a = K.revAligned n h' hh' tape m a := by
  subst heq; rfl

/-- **The mode-switching half of a mixed seek.**  A run of frames the reverse
table fixes in `mOut` is crossed in four steps per frame, then the `boundary`
frame is read — it does *not* stop the pass, it re-points it into `mIn` — and
the head lands reverse-aligned on the last cell of the frame preceding the
boundary.  Exactly `4 * outer.length + 4` genuine steps; the list-backed tape
and the carried context are untouched.

`hpre : 0 < pre.length` is the physical fact that the boundary is not the
leftmost frame of the tape, which is what lets the fourth step of the boundary
frame move left. -/
theorem revSkipToBoundary (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (boundary : F) (outer suffix : List F) (mOut mIn : Mode)
    (a : Aux) (hrev : K.Reverse mOut) (hnostop : ¬ K.Stop mOut)
    (houter : ∀ f ∈ outer, K.revAdvance mOut f = mOut)
    (hbnd : K.revAdvance mOut boundary = mIn) (hnostopIn : ¬ K.Stop mIn)
    (hpre : 0 < pre.length)
    (hsafe : 4 * (pre.length + outer.length) + 4 < K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.revAligned n (4 * (pre.length + outer.length) + 3) (by omega)
          (frameListTape
            ((pre ++ boundary :: outer ++ suffix).flatMap K.codec.bits))
          mOut a)
        (4 * outer.length + 4) =
      K.revAligned n (4 * pre.length - 1) (by omega)
        (frameListTape
          ((pre ++ boundary :: outer ++ suffix).flatMap K.codec.bits))
        mIn a := by
  have hbndSafe : 4 * pre.length + 4 < K.machine.tapeLength n := by omega
  have hbits : physicalBitsAt (h := 4 * pre.length) hbndSafe
      (frameListTape (L := K.machine.tapeLength n)
        ((pre ++ boundary :: outer ++ suffix).flatMap K.codec.bits)) =
      K.codec.bits boundary := by
    have raw := physicalBitsAt_flatMap (L := K.machine.tapeLength n) K.codec pre
      (outer ++ suffix) boundary hbndSafe
    simpa [List.append_assoc] using raw
  have hmacro := K.revFrameMacrostep n (4 * pre.length) (by omega) hbndSafe
    (frameListTape (L := K.machine.tapeLength n)
      ((pre ++ boundary :: outer ++ suffix).flatMap K.codec.bits))
    mOut boundary a hrev (by rw [hbnd]; exact hnostopIn) hbits
  rw [runConfig_add,
    K.revSkipRun n pre boundary outer suffix mOut a hrev hnostop houter hsafe,
    hmacro, hbnd]

/-- **The generic mixed-boundary seek.**  From the last cell of the last frame
of the outer region, exactly `4 * (inner.length + outer.length + 1) + 4` genuine
TM steps cross the outer region in `mOut`, switch to `mIn` at the `boundary`
frame, cross the inner region in `mIn` and read the `marker`, which stops the
pass: the head finishes on the *first* cell of the marker, `4 * pre.length`, the
list-backed tape and the carried context are untouched, and the control is in
`stopState (revAdvance mIn marker)`.

The two regions are separated **only** by the reverse mode, so a caller may give
them disjoint skip classes: this is exactly what a pass needs when the same
frame kind means "cross me" in one region and "stop here" in the other. -/
theorem revSeekAcrossBoundary (K : ReverseFrameScanner S F Mode Aux) (n : Nat)
    (pre : List F) (marker : F) (inner : List F) (boundary : F)
    (outer suffix : List F) (mOut mIn : Mode) (a : Aux)
    (hrevOut : K.Reverse mOut) (hnostopOut : ¬ K.Stop mOut)
    (hrevIn : K.Reverse mIn) (hnostopIn : ¬ K.Stop mIn)
    (houter : ∀ f ∈ outer, K.revAdvance mOut f = mOut)
    (hbnd : K.revAdvance mOut boundary = mIn)
    (hinner : ∀ f ∈ inner, K.revAdvance mIn f = mIn)
    (hstop : K.Stop (K.revAdvance mIn marker))
    (hsafe : 4 * (pre.length + (inner.length + outer.length + 1)) + 4 <
      K.machine.tapeLength n) :
    TM.runConfig (M := K.machine)
        (K.revAligned n
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by omega)
          (frameListTape
            ((pre ++ marker :: inner ++ boundary :: outer ++ suffix).flatMap
              K.codec.bits))
          mOut a)
        (4 * (inner.length + outer.length + 1) + 4) =
      K.alignedConfigQ n (4 * pre.length) (by omega)
        (frameListTape
          ((pre ++ marker :: inner ++ boundary :: outer ++ suffix).flatMap
            K.codec.bits))
        (K.stopState (K.revAdvance mIn marker) a) := by
  have hlen : (pre ++ marker :: inner).length = pre.length + inner.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  have hassoc : (pre ++ marker :: inner) ++ ((boundary :: outer) ++ suffix) =
      ((pre ++ marker :: inner) ++ (boundary :: outer)) ++ suffix :=
    (List.append_assoc _ _ _).symm
  have hout := K.revSkipToBoundary n (pre ++ marker :: inner) boundary outer
    suffix mOut mIn a hrevOut hnostopOut houter hbnd hnostopIn
    (by rw [hlen]; omega) (by rw [hlen]; omega)
  have hin := K.revSeekToMarker n pre marker inner
    ((boundary :: outer) ++ suffix) mIn a hrevIn hnostopIn hinner hstop
    (by omega)
  rw [hassoc] at hin
  rw [K.revAligned_congr n
      (4 * (pre.length + (inner.length + outer.length + 1)) + 3)
      (4 * ((pre ++ marker :: inner).length + outer.length) + 3) (by omega)
      (by rw [hlen]; omega) (by rw [hlen]; omega)
      (frameListTape
        ((pre ++ marker :: inner ++ boundary :: outer ++ suffix).flatMap
          K.codec.bits))
      mOut a,
    show 4 * (inner.length + outer.length + 1) + 4 =
      (4 * outer.length + 4) + (4 * inner.length + 4) from by omega,
    runConfig_add, hout,
    K.revAligned_congr n (4 * (pre ++ marker :: inner).length - 1)
      (4 * (pre.length + inner.length) + 3) (by rw [hlen]; omega) (by omega)
      (by rw [hlen]; omega)
      (frameListTape
        ((pre ++ marker :: inner ++ boundary :: outer ++ suffix).flatMap
          K.codec.bits))
      mIn a]
  exact hin

end ReverseFrameScanner

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
