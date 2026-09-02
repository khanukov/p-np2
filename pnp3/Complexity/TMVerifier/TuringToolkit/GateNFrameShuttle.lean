import Complexity.TMVerifier.TuringToolkit.GateNFixedDelegateRelocation

/-!
# GN-E2-1b dormant GNM identity-copy shuttle (2026-09-02)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module specializes the merged `FrameShuttle` kernel to the existing
`gnCS`/`GNM` transition table.  The temporary marker is decoded
`G1Frame.output true` (`1001`), the destination is the first aligned blank
(`0000`), and the image is identity.  Consequently source and middle frames
must be neither blank nor the marker.

The installer remains dormant: no row from the discovery, delegation,
interception, or `scratchEntry` regions enters `GNState.install`.  In
particular, this slice does not own the future fixed `cursor → bof` or
`finish → separator` boundary rows, a first-record seek, an installer driver,
a `GateNTapeState` execution bridge, clock adequacy, commit, verdict, or
acceptance.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- Only forward seek consumes ordinary frames. -/
def GNInstallForward : GNInstallMode → Prop
  | .seek => True
  | _ => False

/-- Frame-level forward decision: the first blank is the destination and the
temporary marker is rejected in forward middle. -/
def gnInstallAdvance : GNInstallMode → G1Frame → GNInstallMode
  | .seek, .blank => .destinationTurn
  | .seek, .output true => .reject
  | .seek, _ => .seek
  | _, _ => .reject

/-- Bit-level forward decision; all undecodable/reserved windows reject. -/
def gnInstallComplete (mode : GNInstallMode) (b0 b1 b2 b3 : Bool) :
    GNInstallMode :=
  match g1FrameCodec.decode? [b0, b1, b2, b3] with
  | some frame => gnInstallAdvance mode frame
  | none => .reject

/-- Reverse seek stops at the marker and also treats malformed input as a
terminal rejection into the existing outer sink. -/
def GNInstallReverseStop (mode : GNInstallMode) : Prop :=
  mode = .reverseStop ∨ mode = .reject

def GNInstallReverse : GNInstallMode → Prop
  | .reverse => True
  | _ => False

def gnInstallRevAdvance : GNInstallMode → G1Frame → GNInstallMode
  | .reverse, .output true => .reverseStop
  | .reverse, _ => .reverse
  | _, _ => .reject

/-- Bit-level reverse decision; `output true` is accepted only here. -/
def gnInstallRevComplete (mode : GNInstallMode) (b0 b1 b2 b3 : Bool) :
    GNInstallMode :=
  match g1FrameCodec.decode? [b0, b1, b2, b3] with
  | some frame => gnInstallRevAdvance mode frame
  | none => .reject

/-- The single fixed exit state; carried data is deliberately discarded. -/
def gnInstallExitState : GNState := .install .exit .p0 .empty

private theorem gnInstall_bits (a : GNInstallAux) :
    a.frame.bits =
      [gnInstallBit0 a, gnInstallBit1 a, gnInstallBit2 a, gnInstallBit3 a] := by
  cases a with
  | empty => rfl
  | carried frame =>
      cases frame with
      | data b | output b => cases b <;> rfl
      | blank | bof | tag | index | separator | cursor | finish | argSep |
          spent => rfl

/-- The installer scanner uses exactly the existing `gnCS`, phase, and public
G1 codec. -/
def gnInstallCore : FrameScanner GNState G1Frame GNInstallMode GNInstallAux where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  rejectMode := .reject
  advance := gnInstallAdvance
  complete := gnInstallComplete
  Forward := GNInstallForward
  st0 := fun mode aux => gnInstallControl mode .p0 aux
  st1 := fun mode aux b0 => gnInstallControl mode (.p1 b0) aux
  st2 := fun mode aux b0 b1 => gnInstallControl mode (.p2 b0 b1) aux
  st3 := fun mode aux b0 b1 b2 => gnInstallControl mode (.p3 b0 b1 b2) aux
  complete_decode := by
    intro mode b0 b1 b2 b3
    unfold gnInstallComplete
    cases g1FrameCodec.decode? [b0, b1, b2, b3] <;> rfl
  step_p0 := by
    intro mode hm aux scan
    cases mode <;> simp [GNInstallForward] at hm
    rfl
  step_p1 := by
    intro mode hm aux b0 scan
    cases mode <;> simp [GNInstallForward] at hm
    rfl
  step_p2 := by
    intro mode hm aux b0 b1 scan
    cases mode <;> simp [GNInstallForward] at hm
    rfl
  step_p3 := by
    intro mode hm aux b0 b1 b2 scan hne
    cases mode <;> simp [GNInstallForward] at hm
    cases b0 <;> cases b1 <;> cases b2 <;> cases scan
    all_goals simp_all [gnCS, gnTransition, gnInstallComplete, g1FrameCodec,
      gnInstallAdvance, gnInstallControl, decodeG1Frame?]

/-- Concrete dormant identity-copy specialization of the merged kernel. -/
def gnCopyShuttle : FrameShuttle GNState G1Frame GNInstallMode GNInstallAux where
  core := gnInstallCore
  blank := .blank
  marker := .output true
  admissible := GNInstallAdmissible
  image := id
  latch := gnInstallLatch
  carry := GNInstallAux.frame
  carry_latch := by intro a frame; rfl
  blank_bits := rfl
  blank_ne_marker := by decide
  image_ne_blank := by intro frame h; exact h.1
  image_ne_marker := by intro frame h; exact h.2
  pst0 := fun a => .install .probe .p0 a
  pst1 := fun a b0 => .install .probe (.p1 b0) a
  pst2 := fun a b0 b1 => .install .probe (.p2 b0 b1) a
  pst3 := fun a b0 b1 b2 => .install .probe (.p3 b0 b1 b2) a
  turnBack3 := fun a => .install .turnBack (.p3 false false false) a
  probe_p0 := by intro a scan; rfl
  probe_p1 := by intro a b0 scan; rfl
  probe_p2 := by intro a b0 b1 scan; rfl
  probe_p3 := by
    intro a b0 b1 b2 scan frame hf hd
    change decodeG1Frame? [b0, b1, b2, scan] = some frame at hd
    have hne : ¬(frame = G1Frame.blank ∨ frame = .output true) := by
      intro h
      exact h.elim hf.1 hf.2
    simp [gnInstallCore, gnCS, gnTransition, hd, hne]
  turnBack2 := fun a => .install .turnBack (.p2 false false) a
  turnBack1 := fun a => .install .turnBack (.p1 false) a
  turnBack0 := fun a => .install .turnBack .p0 a
  mark0 := fun a => .install .mark .p0 a
  turnBack_p3 := by intro a scan; rfl
  turnBack_p2 := by intro a scan; rfl
  turnBack_p1 := by intro a scan; rfl
  turnBack_p0 := by intro a scan; rfl
  mark1 := fun a => .install .mark (.p1 true) a
  mark2 := fun a => .install .mark (.p2 true false) a
  mark3 := fun a => .install .mark (.p3 true false false) a
  mw0 := true
  mw1 := false
  mw2 := false
  mw3 := true
  marker_bits := rfl
  seekMode := .seek
  destMode := .destinationTurn
  seek_forward := trivial
  seek_blank := rfl
  seek_marker := rfl
  seek_other := by
    intro frame hb hm
    cases frame <;> simp_all [gnInstallCore, gnInstallAdvance]
  seek_not_reject := by decide
  dest_not_reject := by decide
  mark_p0 := by intro a scan; rfl
  mark_p1 := by intro a scan; rfl
  mark_p2 := by intro a scan; rfl
  mark_p3 := by intro a scan; rfl
  revStop := GNInstallReverseStop
  revAdvance := gnInstallRevAdvance
  revComplete := gnInstallRevComplete
  revReverse := GNInstallReverse
  rst3 := fun mode a => gnInstallControl mode .r3 a
  rst2 := fun mode a b3 => gnInstallControl mode (.r2 b3) a
  rst1 := fun mode a b2 b3 => gnInstallControl mode (.r1 b2 b3) a
  rst0 := fun mode a b1 b2 b3 => gnInstallControl mode (.r0 b1 b2 b3) a
  revStopState := fun mode a => gnInstallControl mode .p0 a
  revComplete_decode := by
    intro mode frame b0 b1 b2 b3 h
    simp only [gnInstallRevComplete]
    rw [show g1FrameCodec.decode? [b0, b1, b2, b3] = some frame by
      simpa [gnInstallCore] using h]
  rev_p3 := by
    intro mode hm a scan
    cases mode <;> simp [GNInstallReverse] at hm
    rfl
  rev_p2 := by
    intro mode hm a b3 scan
    cases mode <;> simp [GNInstallReverse] at hm
    rfl
  rev_p1 := by
    intro mode hm a b2 b3 scan
    cases mode <;> simp [GNInstallReverse] at hm
    rfl
  rev_p0 := by
    intro mode hm a b1 b2 b3 scan hn
    cases mode <;> simp [GNInstallReverse] at hm
    cases scan <;> cases b1 <;> cases b2 <;> cases b3
    all_goals simp_all [gnInstallCore, gnCS, gnTransition, gnInstallRevComplete,
      gnInstallRevAdvance, GNInstallReverseStop, gnInstallControl,
      decodeG1Frame?]
  rev_p0_stop := by
    intro mode hm a b1 b2 b3 scan hs
    cases mode <;> simp [GNInstallReverse] at hm
    cases scan <;> cases b1 <;> cases b2 <;> cases b3
    all_goals simp_all [gnInstallCore, gnCS, gnTransition, gnInstallRevComplete,
      gnInstallRevAdvance, GNInstallReverseStop, gnInstallControl,
      decodeG1Frame?]
  revMode := .reverse
  revStopMode := .reverseStop
  rev_mode := trivial
  rev_nostop := by simp [GNInstallReverseStop]
  rev_marker := rfl
  rev_marker_stops := by simp [GNInstallReverseStop]
  rev_other := by
    intro frame hb hm
    cases frame <;> simp_all [gnInstallRevAdvance]
  dest3 := fun a => .install .destination (.p3 false false false) a
  turn_destination := by intro a scan; rfl
  dest2 := fun a => .install .destination (.p2 false false) a
  dest1 := fun a => .install .destination (.p1 false) a
  dest0 := fun a => .install .destination .p0 a
  dw0 := gnInstallBit0
  dw1 := gnInstallBit1
  dw2 := gnInstallBit2
  dw3 := gnInstallBit3
  dest_bits := gnInstall_bits
  dest_p3 := by intro a scan; rfl
  dest_p2 := by intro a scan; rfl
  dest_p1 := by intro a scan; rfl
  dest_p0 := by intro a scan; rfl
  restore1 := fun a => .install .restore (.p1 (gnInstallBit0 a)) a
  restore2 := fun a =>
    .install .restore (.p2 (gnInstallBit0 a) (gnInstallBit1 a)) a
  restore3 := fun a => .install .restore
    (.p3 (gnInstallBit0 a) (gnInstallBit1 a) (gnInstallBit2 a)) a
  exitState := fun _ => gnInstallExitState
  rw0 := gnInstallBit0
  rw1 := gnInstallBit1
  rw2 := gnInstallBit2
  rw3 := gnInstallBit3
  restore_bits := gnInstall_bits
  restore_p0 := by intro a scan; rfl
  restore_p1 := by intro a scan; rfl
  restore_p2 := by intro a scan; rfl
  restore_p3 := by intro a scan; rfl

private theorem gnCopy_lt_tapeLength {n k : Nat} (h : k ≤ 64) :
    k < GNM.tapeLength n := by
  change k < n + gnClock n + 1
  simp [gnClock, g1Clock]
  omega

/-- Concrete specialization of the generic list capstone.  Admissibility is
stated explicitly and identity copy leaves the source restored. -/
theorem gnCS_copyShuttle_onList (n : Nat) (pre : List G1Frame) (f : G1Frame)
    (middle rest : List G1Frame) (a : GNInstallAux)
    (hsource : f ≠ .blank ∧ f ≠ .output true)
    (hmiddle : ∀ g ∈ middle, g ≠ .blank ∧ g ≠ .output true)
    (hsafe : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n
          omega)
          (frameListTape
            ((pre ++ f :: middle ++ .blank :: rest).flatMap G1Frame.bits))
          (.install .probe .p0 a))
        (8 * middle.length + 29) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n
        omega)
        (frameListTape
          ((pre ++ f :: middle ++ f :: rest).flatMap G1Frame.bits))
        gnInstallExitState := by
  have h := gnCopyShuttle.shuttleOnList n pre f middle rest a hsource hmiddle
    hsafe
  rw [(FrameShuttle.shuttleSteps_provenance middle.length).2] at h
  exact h

/-- Next-frontier specialization: the copied frame is followed by an
explicit retained blank. -/
theorem gnCS_copyShuttle_nextBlank (n : Nat) (pre : List G1Frame)
    (f : G1Frame) (middle rest : List G1Frame) (a : GNInstallAux)
    (hsource : f ≠ .blank ∧ f ≠ .output true)
    (hmiddle : ∀ g ∈ middle, g ≠ .blank ∧ g ≠ .output true)
    (hsafe : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n
          omega)
          (frameListTape ((pre ++ f :: middle ++ .blank :: .blank :: rest).flatMap
            G1Frame.bits)) (.install .probe .p0 a))
        (8 * middle.length + 29) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n
        omega)
        (frameListTape ((pre ++ f :: middle ++ f :: .blank :: rest).flatMap
          G1Frame.bits)) gnInstallExitState := by
  have h := gnCopyShuttle.shuttleOnList_nextBlank n pre f middle rest a
    hsource hmiddle hsafe
  rw [(FrameShuttle.shuttleSteps_provenance middle.length).2] at h
  exact h

/-- Raw forward decoder completion rejects every malformed four-bit window. -/
theorem gnTransition_install_forward_none (phase : Fin 1)
    (mode : GNInstallMode) (aux : GNInstallAux) (b0 b1 b2 b3 : Bool)
    (hmode : mode = .probe ∨ mode = .seek)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    gnTransition phase (.install mode (.p3 b0 b1 b2) aux) b3 =
      (0, .reject, b3, .stay) := by
  rcases hmode with rfl | rfl <;> simp [gnTransition, hbad]

/-- Raw reverse decoder completion rejects every malformed four-bit window. -/
theorem gnTransition_install_reverse_none (phase : Fin 1)
    (aux : GNInstallAux) (b0 b1 b2 b3 : Bool)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    gnTransition phase (.install .reverse (.r0 b1 b2 b3) aux) b0 =
      (0, .reject, b0, .stay) := by
  simp [gnTransition, hbad]

/-- All three reserved codec words are rejected in probe, forward seek, and
reverse seek. -/
theorem gnTransition_install_reserved (phase : Fin 1) (aux : GNInstallAux) :
    (∀ mode, mode = GNInstallMode.probe ∨ mode = .seek →
      gnTransition phase (.install mode (.p3 true true false) aux) true =
        (0, .reject, true, .stay)) ∧
    (∀ mode, mode = GNInstallMode.probe ∨ mode = .seek →
      gnTransition phase (.install mode (.p3 true true true) aux) false =
        (0, .reject, false, .stay) ∧
      gnTransition phase (.install mode (.p3 true true true) aux) true =
        (0, .reject, true, .stay)) ∧
    gnTransition phase (.install .reverse (.r0 true false true) aux) true =
      (0, .reject, true, .stay) ∧
    gnTransition phase (.install .reverse (.r0 true true false) aux) true =
      (0, .reject, true, .stay) ∧
    gnTransition phase (.install .reverse (.r0 true true true) aux) true =
      (0, .reject, true, .stay) := by
  constructor
  · intro mode hm
    exact gnTransition_install_forward_none phase mode aux true true false true hm rfl
  constructor
  · intro mode hm
    exact ⟨gnTransition_install_forward_none phase mode aux true true true false hm rfl,
      gnTransition_install_forward_none phase mode aux true true true true hm rfl⟩
  exact ⟨gnTransition_install_reverse_none phase aux true true false true rfl,
    gnTransition_install_reverse_none phase aux true true true false rfl,
    gnTransition_install_reverse_none phase aux true true true true rfl⟩

/-- The decoded marker is accepted only in exact reverse completion; source
probe and forward-middle completion enter the existing reject sink. -/
theorem gnTransition_install_marker_modes (phase : Fin 1) (aux : GNInstallAux) :
    gnTransition phase (.install .probe (.p3 true false false) aux) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.install .seek (.p3 true false false) aux) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.install .reverse (.r0 false false true) aux) true =
        (0, .install .reverseStop .p0 aux, true, .stay) := by
  exact ⟨by simp [gnTransition, decodeG1Frame?],
    by simp [gnTransition, decodeG1Frame?],
    by simp [gnTransition, decodeG1Frame?]⟩

/-- Existing outer rejection remains a stable sink after installer failure. -/
theorem gnCS_install_reject_stable {n : Nat} (c : Configuration (M := GNM) n)
    (hstate : c.state = ⟨(0 : Fin 1), GNState.reject⟩) (k : Nat) :
    TM.runConfig (M := GNM) c k = c :=
  gnCS_reject_stable c hstate k

def gnCopyLiteralInput : List G1Frame :=
  [.tag, .argSep, .index, .blank, .blank]

def gnCopyLiteralOutput : List G1Frame :=
  [.tag, .argSep, .index, .tag, .blank]

/-- Caller-supplied dormant entry: copy `tag` across two middle frames in the
exact 45-step schedule, restoring the source and retaining the next blank. -/
theorem gnCS_copyShuttle_tag_run45 (n : Nat) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n 0 (gnCopy_lt_tapeLength (by omega))
          (frameListTape (gnCopyLiteralInput.flatMap G1Frame.bits))
          (.install .probe .p0 .empty)) 45 =
      gnCopyShuttle.cfg n 4 (gnCopy_lt_tapeLength (by omega))
        (frameListTape (gnCopyLiteralOutput.flatMap G1Frame.bits))
        gnInstallExitState := by
  have h := gnCS_copyShuttle_nextBlank n [] .tag [.argSep, .index] [] .empty
    (by decide) (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> decide)
    (gnCopy_lt_tapeLength (n := n) (k := 16) (by omega))
  simpa [gnCopyLiteralInput, gnCopyLiteralOutput] using h

/-- Negative literal: a marker in forward middle invalidates the concrete
seek path before any capstone can be applied. -/
theorem gnCopyShuttle_marker_middle_rejected :
    ¬ gnCopyShuttle.core.ValidPath gnCopyShuttle.seekMode
      [.argSep, .output true, .index] := by
  simp [gnCopyShuttle, gnInstallCore, FrameScanner.ValidPath, GNInstallForward,
    gnInstallAdvance]

end Pnp3.Internal.PsubsetPpoly.TM
