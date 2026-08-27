import Complexity.TMVerifier.TuringToolkit.FrameScannerReverse

/-!
# The generic four-cell frame write/replacement layer

Generic pointwise four-cell overwrite, arbitrary-list frame replacement, and
an exact four-step writer machine.  `FrameWriter` carries one target-codeword
law and four concrete transition tuples—no semantic run field.  This slice
stops at one rightward frame replacement; the leftward writer and 13-step
rewrite cycle are explicitly deferred.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

/-! ## The pure four-cell overwrite -/
/-- Overwrite the four physical cells of the frame starting at `base`.  The
nesting order is the order a left-to-right writer produces them. -/
def writeFrame4 {L : Nat} (base : Nat) (b0 b1 b2 b3 : Bool)
    (tape : Fin L → Bool) : Fin L → Bool :=
  writeCell (base + 3) b3
    (writeCell (base + 2) b2 (writeCell (base + 1) b1 (writeCell base b0 tape)))

/-- **Pointwise description.**  Exactly the four cells change, each to its bit. -/
theorem writeFrame4_apply {L : Nat} (base : Nat) (b0 b1 b2 b3 : Bool)
    (tape : Fin L → Bool) (i : Fin L) :
    writeFrame4 base b0 b1 b2 b3 tape i =
      if (i : Nat) = base then b0
      else if (i : Nat) = base + 1 then b1
      else if (i : Nat) = base + 2 then b2
      else if (i : Nat) = base + 3 then b3
      else tape i := by
  by_cases h0 : (i : Nat) = base
  · simp [writeFrame4, writeCell, h0]
  · by_cases h1 : (i : Nat) = base + 1
    · simp [writeFrame4, writeCell, h1]
    · by_cases h2 : (i : Nat) = base + 2
      · simp [writeFrame4, writeCell, h2]
      · by_cases h3 : (i : Nat) = base + 3
        · simp [writeFrame4, writeCell, h3]
        · simp [writeFrame4, writeCell, h0, h1, h2, h3]

/-- `List.getD` across a concatenation, split at the left length. -/
private theorem getD_append_split (P Q : List Bool) (j : Nat) :
    (P ++ Q).getD j false =
      if j < P.length then P.getD j false else Q.getD (j - P.length) false := by
  induction P generalizing j with
  | nil => simp
  | cons b rest ih =>
      cases j with
      | zero => simp
      | succ k => simpa using ih k

/-- Generic arbitrary-list frame-replacement law for `writeFrame4`. -/
theorem writeFrame4_frameListTape {F : Type v} (C : FrameCodec F) {L : Nat}
    (pre suffix : List F) (old new : F) {b0 b1 b2 b3 : Bool}
    (hbits : C.bits new = [b0, b1, b2, b3]) :
    writeFrame4 (L := L) (4 * pre.length) b0 b1 b2 b3
        (frameListTape ((pre ++ old :: suffix).flatMap C.bits)) =
      frameListTape ((pre ++ new :: suffix).flatMap C.bits) := by
  obtain ⟨o0, o1, o2, o3, hold⟩ := C.bits_eq_four old
  have hlen : (pre.flatMap C.bits).length = 4 * pre.length :=
    C.flatMap_bits_length pre
  funext i
  rw [writeFrame4_apply]
  simp only [frameListTape, List.flatMap_append, List.flatMap_cons, hold, hbits,
    getD_append_split, hlen]
  rcases Nat.lt_or_ge (i : Nat) (4 * pre.length) with hlt | hge
  · have h0 : ¬ (i : Nat) = 4 * pre.length := by omega
    have h1 : ¬ (i : Nat) = 4 * pre.length + 1 := by omega
    have h2 : ¬ (i : Nat) = 4 * pre.length + 2 := by omega
    have h3 : ¬ (i : Nat) = 4 * pre.length + 3 := by omega
    simp [h0, h1, h2, h3, hlt]
  · rcases Nat.lt_or_ge (i : Nat) (4 * pre.length + 4) with hlt2 | hge2
    · have hcases : (i : Nat) = 4 * pre.length ∨ (i : Nat) = 4 * pre.length + 1 ∨
          (i : Nat) = 4 * pre.length + 2 ∨ (i : Nat) = 4 * pre.length + 3 := by
        omega
      rcases hcases with h | h | h | h <;>
        simp [h, Nat.not_lt.mpr]
    · have h0 : ¬ (i : Nat) = 4 * pre.length := by omega
      have h1 : ¬ (i : Nat) = 4 * pre.length + 1 := by omega
      have h2 : ¬ (i : Nat) = 4 * pre.length + 2 := by omega
      have h3 : ¬ (i : Nat) = 4 * pre.length + 3 := by omega
      have hnl : ¬ (i : Nat) < 4 * pre.length := by omega
      have hsub : ¬ ((i : Nat) - 4 * pre.length) < 4 := by omega
      simp [h0, h1, h2, h3, hnl, hsub]

/-! ## The generic frame writer -/
/-- **A fixed-width frame writer.**

`wst0 … wst3` are the four aligned control states of a destructive left-to-right
walk across one frame and `exitState` the state the control lands in after it.
The four bits `w0 … w3` are the literal cells the finite control writes, and
`target_bits` is the codec law identifying them with the codeword of `target`.

All five obligations are that codec law and four concrete transition tuples;
the tuples are quantified over the scanned cell, since a writer ignores what it
overwrites. -/
structure FrameWriter (S : Type v) [Fintype S] [DecidableEq S]
    (F Aux : Type v) where
  program : ConstStatePhasedProgram S
  phase : Fin program.numPhases
  codec : FrameCodec F
  /-- The frame this control installs. -/
  target : F
  w0 : Bool
  w1 : Bool
  w2 : Bool
  w3 : Bool
  wst0 : Aux → S
  wst1 : Aux → S
  wst2 : Aux → S
  wst3 : Aux → S
  exitState : Aux → S
  target_bits : codec.bits target = [w0, w1, w2, w3]
  wstep_p0 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (wst0 a) scan = (phase, wst1 a, w0, Move.right)
  wstep_p1 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (wst1 a) scan = (phase, wst2 a, w1, Move.right)
  wstep_p2 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (wst2 a) scan = (phase, wst3 a, w2, Move.right)
  wstep_p3 : ∀ (a : Aux) (scan : Bool),
    program.transition phase (wst3 a) scan = (phase, exitState a, w3, Move.right)

namespace FrameWriter

variable {S : Type v} [Fintype S] [DecidableEq S] {F Aux : Type v}

/-- The compiled machine of a writer. -/
abbrev machine (W : FrameWriter S F Aux) : TM.{v} := Phased.machine W.program

/-- A configuration in the writer's phase with an explicit head and state. -/
abbrev alignedConfigQ (W : FrameWriter S F Aux) (n h : Nat)
    (hh : h < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (q : S) :
    Configuration (M := W.machine) n :=
  Phased.alignedAt W.program W.phase n h hh tape q

/-- Exact four-step writer: head +4, context preserved, tape = `writeFrame4`. -/
theorem writeMacrostep (W : FrameWriter S F Aux) (n base : Nat)
    (hsafe : base + 4 < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (a : Aux) :
    TM.runConfig (M := W.machine)
        (W.alignedConfigQ n base (by omega) tape (W.wst0 a)) 4 =
      W.alignedConfigQ n (base + 4) hsafe
        (writeFrame4 base W.w0 W.w1 W.w2 W.w3 tape) (W.exitState a) := by
  have hb0 : base < W.machine.tapeLength n := by omega
  have hb1 : base + 1 < W.machine.tapeLength n := by omega
  have hb2 : base + 2 < W.machine.tapeLength n := by omega
  have hb3 : base + 3 < W.machine.tapeLength n := by omega
  show TM.runConfig (M := W.machine)
      (W.alignedConfigQ n base hb0 tape (W.wst0 a)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [Phased.stepRight W.program W.phase n base hb0 hb1 tape
    (W.wst0 a) (W.wst1 a) W.w0 (W.wstep_p0 a _)]
  rw [Phased.stepRight W.program W.phase n (base + 1) hb1 hb2 _
    (W.wst1 a) (W.wst2 a) W.w1 (W.wstep_p1 a _)]
  rw [Phased.stepRight W.program W.phase n (base + 2) hb2 hb3 _
    (W.wst2 a) (W.wst3 a) W.w2 (W.wstep_p2 a _)]
  rw [Phased.stepRight W.program W.phase n (base + 3) hb3 hsafe _
    (W.wst3 a) (W.exitState a) W.w3 (W.wstep_p3 a _)]
  rfl

/-- Four-step executable replacement of one frame in an arbitrary list tape. -/
theorem writeFrameOnList (W : FrameWriter S F Aux) (n : Nat)
    (pre suffix : List F) (old : F) (a : Aux)
    (hsafe : 4 * pre.length + 4 < W.machine.tapeLength n) :
    TM.runConfig (M := W.machine)
        (W.alignedConfigQ n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ old :: suffix).flatMap W.codec.bits))
          (W.wst0 a)) 4 =
      W.alignedConfigQ n (4 * pre.length + 4) hsafe
        (frameListTape ((pre ++ W.target :: suffix).flatMap W.codec.bits))
        (W.exitState a) := by
  rw [W.writeMacrostep n (4 * pre.length) hsafe _ a,
    writeFrame4_frameListTape W.codec pre suffix old W.target W.target_bits]

end FrameWriter

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
