import Complexity.TMVerifier.TuringToolkit.GateNValuesRewind
import Complexity.TMVerifier.TuringToolkit.FrameScannerWriteCtx

/-! Infrastructure: physical macrosteps for the finite first-return commit. -/
namespace Pnp3.Internal.PsubsetPpoly.TM
open FrameScan Encoding

abbrev gnCommitConfig (n h : Nat) (hh : h < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (q : GNState) :=
  Phased.alignedAt gnCS gnCS.startPhase n h hh tape q

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

namespace GNCommitProof

def revMode (opening : Bool) : GNCommitMode := if opening then .seekOpening else .seekCursor
def revAnchor (opening : Bool) : G1Frame := if opening then .bof else .cursor
def revExit (opening res : Bool) : GNState :=
  if opening then .commitRead .opening .p0 res else .commitTransfer res

def revAdvance (opening : Bool) : GNRewindMode → G1Frame → GNRewindMode
  | _, f => if f = revAnchor opening then .anchor else
      if (gnCommitAdvance (revMode opening) f false).2 = .left then .scan else .reject

def revComplete (opening : Bool) (_ : GNRewindMode) (b0 b1 b2 b3 : Bool) :=
  match decodeG1Frame? [b0, b1, b2, b3] with
  | some f => revAdvance opening .scan f
  | none => GNRewindMode.reject

def reverse (opening : Bool) : ReverseFrameScanner GNState G1Frame GNRewindMode Bool where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  Stop := GNRewindMode.Stop
  Reverse := GNRewindMode.Reverse
  revAdvance := revAdvance opening
  revComplete := revComplete opening
  rst3 := fun _ res => .commitRead (revMode opening) .r3 res
  rst2 := fun _ res b3 => .commitRead (revMode opening) (.r2 b3) res
  rst1 := fun _ res b2 b3 => .commitRead (revMode opening) (.r1 b2 b3) res
  rst0 := fun _ res b1 b2 b3 => .commitRead (revMode opening) (.r0 b1 b2 b3) res
  stopState := fun m res => if m = .anchor then revExit opening res else .reject
  revComplete_decode := by intros; simp_all [revComplete, revAdvance]
  rstep_p3 := by intros; cases opening <;> rfl
  rstep_p2 := by intros; cases opening <;> rfl
  rstep_p1 := by intros; cases opening <;> rfl
  rstep_p0 := by
    intro m hm res b1 b2 b3 scan hn
    obtain rfl := hm.eq
    cases opening <;> cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      first | exact (hn trivial).elim | rfl
  rstep_p0_stop := by
    intro m hm res b1 b2 b3 scan hs
    obtain rfl := hm.eq
    cases opening <;> cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      first | exact hs.elim | rfl

theorem reverse_exact (n : Nat) (pre body post : List G1Frame) (opening res : Bool)
    (hb : ∀ f ∈ body, revAdvance opening .scan f = .scan)
    (hr : 4 * (pre.length + body.length + 1) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
      (gnCommitConfig n (4 * (pre.length + body.length) + 3) (by omega)
        (frameListTape ((pre ++ revAnchor opening :: body ++ post).flatMap G1Frame.bits))
        (.commitRead (revMode opening) .r3 res)) (4 * body.length + 4) =
      gnCommitConfig n (4 * pre.length) (by omega)
        (frameListTape ((pre ++ revAnchor opening :: body ++ post).flatMap G1Frame.bits))
        (revExit opening res) := by
  have hp := (reverse opening).revValidPath_const (m := GNRewindMode.scan)
    trivial (fun h => h) body hb
  have hs := (reverse opening).revScanFrames n pre (revAnchor opening) body post .scan res
    hp.1 (by change 4 * (pre.length + body.length) + 4 < GNM.tapeLength n; omega)
  rw [hp.2] at hs
  have ha := (reverse opening).revAnchorStep n (4 * pre.length)
    (by change 4 * pre.length + 4 < GNM.tapeLength n; omega)
    (frameListTape ((pre ++ revAnchor opening :: body ++ post).flatMap G1Frame.bits))
    .scan (revAnchor opening) res trivial
    (by cases opening <;> trivial)
    (by simpa only [List.append_assoc, List.cons_append, g1FrameCodec_bits] using
      physicalBitsAt_flatMap g1FrameCodec pre (body ++ post) (revAnchor opening) (by change 4 * pre.length + 4 < GNM.tapeLength n; omega))
  change TM.runConfig (M := GNM) (gnCommitConfig n _ _ _ _) _ =
    gnCommitConfig n _ _ _ _ at hs
  simp only [reverse, g1FrameCodec_bits] at hs
  rw [runConfig_add, hs]
  simpa [reverse, revAdvance] using ha

theorem right (n h : Nat) (hr : h+1 < GNM.tapeLength n)
    (t : Fin (GNM.tapeLength n) → Bool) (q q' : GNState)
    (he : gnTransition 0 q (t ⟨h, by omega⟩) = (0, q', t ⟨h, by omega⟩, .right)) :
    TM.stepConfig (M := GNM) (gnCommitConfig n h (by omega) t q) =
      gnCommitConfig n (h+1) hr t q' := by
  have h := Phased.stepRight gnCS gnCS.startPhase n h (by change h < GNM.tapeLength n; omega) hr t q q' _ he
  rwa [writeCell_self] at h

theorem stay (n h : Nat) (hr : h < GNM.tapeLength n)
    (t : Fin (GNM.tapeLength n) → Bool) (q q' : GNState)
    (he : gnTransition 0 q (t ⟨h, hr⟩) = (0, q', t ⟨h, hr⟩, .stay)) :
    TM.stepConfig (M := GNM) (gnCommitConfig n h hr t q) =
      gnCommitConfig n h hr t q' := by
  have h := Phased.stepStay gnCS gnCS.startPhase n h hr t q q' _ he
  rwa [writeCell_self] at h

/-- The fourth read is allowed to stay. This is not the generic forward scanner. -/
theorem read (n h : Nat) (hr : h+4 < GNM.tapeLength n)
    (t : Fin (GNM.tapeLength n) → Bool) (m : GNCommitMode) (res : Bool)
    (hm : ¬ (m = .seekCursor ∨ m = .seekOpening)) (f : G1Frame) (q : GNState)
    (go : Bool) (hd : gnCommitAdvance m f res = (q, if go then .right else .stay))
    (hb : physicalBitsAt hr t = f.bits) :
    TM.runConfig (M := GNM) (gnCommitConfig n h (by omega) t (.commitRead m .p0 res)) 4 =
      gnCommitConfig n (h+3+(if go then 1 else 0)) (by split <;> omega) t q := by
  have hc : gnCommitComplete m (t ⟨h, by omega⟩) (t ⟨h+1, by omega⟩)
      (t ⟨h+2, by omega⟩) (t ⟨h+3, by omega⟩) res =
      (q, if go then .right else .stay) := by
    unfold gnCommitComplete
    have hh : [t ⟨h, by omega⟩, t ⟨h+1, by omega⟩,
        t ⟨h+2, by omega⟩, t ⟨h+3, by omega⟩] = f.bits := hb
    rw [hh, show decodeG1Frame? f.bits = some f from g1FrameCodec.decode_bits f]; exact hd
  change TM.runConfig (M := GNM) _ (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [right n h (by omega) t _ (.commitRead m (.p1 (t ⟨h, by omega⟩)) res)
    (by simp [gnTransition, gnCommitRead, hm])]
  rw [right n (h+1) (by omega) t _
    (.commitRead m (.p2 (t ⟨h, by omega⟩) (t ⟨h+1, by omega⟩)) res)
    (by simp [gnTransition, gnCommitRead, hm])]
  rw [right n (h+2) (by omega) t _
    (.commitRead m (.p3 (t ⟨h, by omega⟩) (t ⟨h+1, by omega⟩)
      (t ⟨h+2, by omega⟩)) res) (by simp [gnTransition, gnCommitRead, hm])]
  cases go
  · exact stay n (h+3) (by omega) t _ q (by simp [gnTransition, gnCommitRead, hm, hc])
  · exact right n (h+3) (by omega) t _ q (by simp [gnTransition, gnCommitRead, hm, hc])

def writer (p : GNCommitPatch) : FrameWriterCtx GNState G1Frame Bool where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  target := gnCommitTarget p
  w0 := fun res => (gnCommitTarget p res).bits.getD 0 false
  w1 := fun res => (gnCommitTarget p res).bits.getD 1 false
  w2 := fun res => (gnCommitTarget p res).bits.getD 2 false
  w3 := fun res => (gnCommitTarget p res).bits.getD 3 false
  wst0 := fun res => .commitWrite p .p0 res
  wst1 := fun res => .commitWrite p (.p1 false) res
  wst2 := fun res => .commitWrite p (.p2 false false) res
  wst3 := fun res => .commitWrite p (.p3 false false false) res
  exitState := gnCommitWriteExit p
  target_bits := by intro res; cases p <;> cases res <;> rfl
  wstep_p0 := by intros; rfl
  wstep_p1 := by intros; rfl
  wstep_p2 := by intros; rfl
  wstep_p3 := by intros; rfl

theorem back (n h : Nat) (hr : h+3 < GNM.tapeLength n)
    (t : Fin (GNM.tapeLength n) → Bool) (p : GNCommitPatch) (res : Bool) :
    TM.runConfig (M := GNM)
      (gnCommitConfig n (h+3) hr t (.commitBack p (.p2 false false) res)) 3 =
      gnCommitConfig n h (by omega) t (.commitWrite p .p0 res) := by
  change TM.runConfig (M := GNM) _ (1+1+1) = _
  rw [runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [Phased.holdLeft gnCS gnCS.startPhase n (h+3) hr (by omega) t _ _ (fun _ => rfl)]
  simp only [show h+3-1 = h+2 by omega, show h+2-1 = h+1 by omega, Nat.add_sub_cancel]
  rw [Phased.holdLeft gnCS gnCS.startPhase n (h+2) (by change h+2 < GNM.tapeLength n; omega) (by omega) t _ _ (fun _ => rfl)]
  simp only [show h+3-1 = h+2 by omega, show h+2-1 = h+1 by omega, Nat.add_sub_cancel]
  rw [Phased.holdLeft gnCS gnCS.startPhase n (h+1) (by change h+1 < GNM.tapeLength n; omega) (by omega) t _ _ (fun _ => rfl)]
  simp

theorem patch (n : Nat) (pre post : List G1Frame) (old : G1Frame)
    (m : GNCommitMode) (p : GNCommitPatch) (res : Bool)
    (hm : ¬ (m = .seekCursor ∨ m = .seekOpening))
    (hd : gnCommitAdvance m old res = (.commitBack p (.p2 false false) res, .stay))
    (hr : 4*pre.length+4 < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
      (gnCommitConfig n (4*pre.length) (by omega)
        (frameListTape ((pre ++ old :: post).flatMap G1Frame.bits)) (.commitRead m .p0 res)) 11 =
      gnCommitConfig n (4*pre.length+4) hr
        (frameListTape ((pre ++ gnCommitTarget p res :: post).flatMap G1Frame.bits))
        (gnCommitWriteExit p res) := by
  change TM.runConfig (M := GNM) _ (4+3+4) = _
  have hs := read n _ hr _ m res hm old _ false hd
    (physicalBitsAt_flatMap g1FrameCodec pre post old hr)
  simp only [g1FrameCodec_bits] at hs
  rw [runConfig_add, runConfig_add, hs]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rw [back]
  exact (writer p).writeFrameOnList n pre post old res hr

/-- A proof relation describing only the ordinary four-right-read portions. -/
inductive Path (res : Bool) : GNCommitMode → List G1Frame → GNCommitMode → Prop
  | nil (m) : Path res m [] m
  | cons {m m' endMode f fs} (hm : ¬ (m = .seekCursor ∨ m = .seekOpening))
      (hd : gnCommitAdvance m f res = (.commitRead m' .p0 res, .right))
      (tail : Path res m' fs endMode) : Path res m (f :: fs) endMode

theorem Path.append {res m m' m'' fs gs} (h : Path res m fs m') (h' : Path res m' gs m'') :
    Path res m (fs ++ gs) m'' := by
  induction h with
  | nil => exact h'
  | cons hm hd _ ih => exact .cons hm hd (ih h')

theorem Path.scan {res m m' fs} (hp : Path res m fs m') (n : Nat)
    (pre post : List G1Frame) (hr : 4*(pre.length+fs.length) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
      (gnCommitConfig n (4*pre.length) (by omega)
        (frameListTape ((pre ++ fs ++ post).flatMap G1Frame.bits)) (.commitRead m .p0 res))
      (4*fs.length) =
      gnCommitConfig n (4*(pre.length+fs.length)) hr
        (frameListTape ((pre ++ fs ++ post).flatMap G1Frame.bits)) (.commitRead m' .p0 res) := by
  induction hp generalizing pre with
  | nil => simp [runConfig_zero]
  | @cons m m1 m2 f fs hm hd ht ih =>
    have hr' : 4*pre.length+4 < GNM.tapeLength n := by simp only [List.length_cons] at hr; omega
    have hs := read n (4*pre.length) hr' _ m res hm f (.commitRead m1 .p0 res) true hd
      (physicalBitsAt_flatMap g1FrameCodec pre (fs ++ post) f hr')
    rw [show 4*(f :: fs).length = 4+4*fs.length by simp; omega, runConfig_add]
    simp only [List.cons_append, List.append_assoc, g1FrameCodec_bits] at hs ⊢
    rw [hs]
    simp only [ite_true, ↓reduceIte, show 4*pre.length+3+1 = 4*pre.length+4 by omega]
    have hi := ih (pre ++ [f]) (by
      simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *
      omega)
    simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

end GNCommitProof
end Pnp3.Internal.PsubsetPpoly.TM
