import Complexity.TMVerifier.TuringToolkit.FrameScannerWriteLeft
import Complexity.TMVerifier.TuringToolkit.GateOneInstallScan

/-!
# Dormant G1 operand-A installation atoms

**Progress classification: Infrastructure.**  This module executes only four
atoms from caller-supplied configurations: the operand-A installation scan,
the data probe/latch, the out-of-range probe and the four-cell cursor writer.
`aInstallStart` remains stationary.  There is no bridge, initial-configuration
route, reverse seek, walk round, repair, combine, output or acceptance claim.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- Frames crossed before the operand-A installation scan reaches the data
separator: operand units, their consumed form, and either operand boundary. -/
def G1AInstallSkip : G1Frame → Prop
  | .index | .spent | .argSep => True
  | _ => False

instance : DecidablePred G1AInstallSkip := fun frame => by
  cases frame <;> first | exact isTrue trivial | exact isFalse id

theorem g1Advance_aInsSeek_of_skip {frame : G1Frame}
    (h : G1AInstallSkip frame) :
    g1Advance .aInsSeek frame = .aInsSeek := by
  cases frame <;> first | rfl | exact (show False from h).elim

theorem g1Advance_aProbe_data (v : Bool) :
    g1Advance .aProbe (.data v) = g1ALatchMode v := by
  cases v <;> rfl

/-- The complete successful installation-scan subtable. -/
theorem g1Advance_aInsSeek_rows :
    g1Advance .aInsSeek .index = .aInsSeek ∧
      g1Advance .aInsSeek .spent = .aInsSeek ∧
      g1Advance .aInsSeek .argSep = .aInsSeek ∧
      g1Advance .aInsSeek .separator = .aProbe :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The complete successful probe subtable. -/
theorem g1Advance_aProbe_rows :
    g1Advance .aProbe (.data false) = .aLatchFalse ∧
      g1Advance .aProbe (.data true) = .aLatchTrue ∧
      g1Advance .aProbe (.output false) = .bOOB :=
  ⟨rfl, rfl, rfl⟩

/-- Representative decoded frames outside the two exact subtable languages
reject rather than being silently crossed. -/
theorem g1Advance_aInstallAtoms_rejects :
    g1Advance .aInsSeek (.data false) = .reject ∧
      g1Advance .aInsSeek (.output false) = .reject ∧
      g1Advance .aProbe .index = .reject ∧
      g1Advance .aProbe .separator = .reject ∧
      g1Advance .aProbe (.output true) = .reject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Four fixed cursor bits, written right-to-left, exiting into the dormant
normal-walk outer seek. -/
def g1AInstallCursorWriter : ReverseFrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := fun _ => .cursor
  w0 := fun _ => false
  w1 := fun _ => true
  w2 := fun _ => true
  w3 := fun _ => true
  lst3 := g1AInsState
  lst2 := fun ctx => g1State .aIns .p2 false false false ctx
  lst1 := fun ctx => g1State .aIns .p1 false false false ctx
  lst0 := fun ctx => g1State .aIns .p0 false false false ctx
  exitState := g1ASeekOutState
  target_bits := fun _ => rfl
  lstep_p3 := fun ctx scan =>
    g1Transition_aIns_p3 g1CS.startPhase false false false scan ctx
  lstep_p2 := fun ctx scan =>
    g1Transition_aIns_p2 g1CS.startPhase false false false scan ctx
  lstep_p1 := fun ctx scan =>
    g1Transition_aIns_p1 g1CS.startPhase false false false scan ctx
  lstep_p0 := fun ctx scan =>
    g1Transition_aIns_p0 g1CS.startPhase false false false scan ctx

@[simp] theorem g1AInstallCursorWriter_machine :
    g1AInstallCursorWriter.machine = G1M := rfl

/-! ## Exact caller-supplied macros -/

/-- The read-only installation scan crosses exactly the caller-certified run
of `index`/`spent`/`argSep` frames and the following `separator`. -/
theorem g1CS_aInstall_scan (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1AInstallSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.separator :: suffix).flatMap G1Frame.bits))
        .aInsSeek .p0 false false false ctx) (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.separator :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx := by
  have hfix : ∀ f ∈ skipped, g1Advance .aInsSeek f = .aInsSeek :=
    fun f hf => g1Advance_aInsSeek_of_skip (hskip f hf)
  have hlen : (skipped ++ [G1Frame.separator]).length = skipped.length + 1 := by
    simp
  have hlist : pre ++ (skipped ++ [G1Frame.separator]) ++ suffix =
      pre ++ skipped ++ G1Frame.separator :: suffix := by
    simp [List.append_assoc]
  have hpath : G1ValidPath .aInsSeek (skipped ++ [.separator]) :=
    g1ValidPath_fix (mode := .aInsSeek) trivial [.separator]
      ⟨trivial, by decide, trivial⟩ skipped hfix
  have hfold :
      g1AdvanceList .aInsSeek (skipped ++ [.separator]) = .aProbe := by
    rw [g1AdvanceList_fix (mode := .aInsSeek) [.separator] skipped hfix]
    rfl
  have hscan := g1FrameScanner_scanFrames n pre (skipped ++ [.separator]) suffix
    .aInsSeek ctx ((g1FrameScanner_validPath _ _).mpr hpath)
    (by rw [hlen]; exact hsafe)
  simp only [hlist, hlen, g1AlignedFrame_eq, g1FrameScanner_advanceList, hfold]
    at hscan
  exact hscan

/-- Four probe steps plus one latch step preserve the tape, store exactly `v`
in `ctx.vB`, and leave the head on the data frame's last cell. -/
theorem g1CS_aProbe_latch (n : Nat) (pre suffix : List G1Frame) (v : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx) 5 =
      g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .aIns .p3 false false false (ctx.withVB v) := by
  have hbits : physicalBitsAt (h := 4 * pre.length) hsafe
      (g1ListTape (n := n)
        ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits)) =
      (G1Frame.data v).bits :=
    physicalBitsAt_flatMap g1FrameCodec pre suffix (.data v) hsafe
  have hmacro := g1FrameScanner_frameMacrostep n (4 * pre.length) hsafe
    (g1ListTape (n := n)
      ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
    .aProbe (.data v) ctx trivial (by cases v <;> decide) hbits
  rw [g1Advance_aProbe_data v] at hmacro
  have hlatch : TM.runConfig (M := G1M)
      (g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        (g1ALatchMode v) .p0 false false false ctx) 1 =
      g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .aIns .p3 false false false (ctx.withVB v) := by
    rw [runConfig_one]
    have hstep := g1CS_aligned_step_left n (4 * pre.length + 4) hsafe
      (by omega)
      (g1ListTape (n := n)
        ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
      (g1State (g1ALatchMode v) .p0 false false false ctx)
      (g1AInsState (ctx.withVB v)) _
      (fun phase => g1Transition_aLatch phase v .p0 false false false _ ctx)
    rw [writeCell_self] at hstep
    simpa [show 4 * pre.length + 4 - 1 = 4 * pre.length + 3 by omega]
      using hstep
  refine Eq.trans (runConfig_add _ 4 1) ?_
  exact Eq.trans (congrArg (fun c => TM.runConfig (M := G1M) c 1) hmacro) hlatch

/-- The destination frame is the exact out-of-range branch: four read-only
steps reach the existing stable `bOOB` boundary with context unchanged. -/
theorem g1CS_aProbe_oob (n : Nat) (pre suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .bOOB .p0 false false false ctx := by
  have hbits : physicalBitsAt (h := 4 * pre.length) hsafe
      (g1ListTape (n := n)
        ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits)) =
      (G1Frame.output false).bits :=
    physicalBitsAt_flatMap g1FrameCodec pre suffix (.output false) hsafe
  exact g1FrameScanner_frameMacrostep n (4 * pre.length) hsafe
    (g1ListTape (n := n)
      ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
    .aProbe (.output false) ctx trivial (by decide) hbits

/-- Literal raw-window rejection.  In either new forward mode the reserved
window `1101` reaches the existing reject sink in exactly four steps, without
moving past its fourth cell or changing the tape. -/
theorem g1CS_aInstall_reserved_1101_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : mode = .aInsSeek ∨ mode = .aProbe)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n base (by omega) tape mode .p0
          false false false ctx) 4 =
      g1AlignedConfig n (base + 3) (by omega) tape .reject .p0
        false false false g1Ctx0 := by
  have hforward : G1ForwardMode mode := by
    rcases hmode with rfl | rfl <;> trivial
  have hwindow :
      [tape ⟨base, by omega⟩, tape ⟨base + 1, by omega⟩,
        tape ⟨base + 2, by omega⟩, tape ⟨base + 3, by omega⟩] =
        [true, true, false, true] := by
    simpa [physicalBitsAt] using hbits
  have hcomplete : g1Complete mode (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩) = .reject := by
    have hcells :
        tape ⟨base, by omega⟩ = true ∧
          tape ⟨base + 1, by omega⟩ = true ∧
          tape ⟨base + 2, by omega⟩ = false ∧
          tape ⟨base + 3, by omega⟩ = true := by
      simpa only [List.cons.injEq, and_true] using hwindow
    rcases hcells with ⟨hb0, hb1, hb2, hb3⟩
    simpa only [hb0, hb1, hb2, hb3] using
      (g1Complete_aInstallAtoms_reserved mode).1
  show TM.runConfig (M := G1M)
      (g1AlignedConfigQ n base (by omega) tape
        (g1State mode .p0 false false false ctx)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have hs0 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n base (by omega) tape
        (g1State mode .p0 false false false ctx)) =
      g1AlignedConfigQ n (base + 1) (by omega) tape
        (g1State mode .p1 (tape ⟨base, by omega⟩) false false ctx) := by
    have hstep := g1CS_aligned_step_right n base (by omega) (by omega) tape
      (g1State mode .p0 false false false ctx)
      (g1State mode .p1 (tape ⟨base, by omega⟩) false false ctx)
      (tape ⟨base, by omega⟩)
      (fun phase =>
        g1Transition_forward_p0 hforward phase false false false _ ctx)
    rwa [writeCell_self] at hstep
  have hs1 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n (base + 1) (by omega) tape
        (g1State mode .p1 (tape ⟨base, by omega⟩) false false ctx)) =
      g1AlignedConfigQ n (base + 2) (by omega) tape
        (g1State mode .p2 (tape ⟨base, by omega⟩)
          (tape ⟨base + 1, by omega⟩) false ctx) := by
    have hstep := g1CS_aligned_step_right n (base + 1) (by omega) (by omega) tape
      (g1State mode .p1 (tape ⟨base, by omega⟩) false false ctx)
      (g1State mode .p2 (tape ⟨base, by omega⟩)
        (tape ⟨base + 1, by omega⟩) false ctx)
      (tape ⟨base + 1, by omega⟩)
      (fun phase =>
        g1Transition_forward_p1 hforward phase _ false false _ ctx)
    rwa [writeCell_self] at hstep
  have hs2 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n (base + 2) (by omega) tape
        (g1State mode .p2 (tape ⟨base, by omega⟩)
          (tape ⟨base + 1, by omega⟩) false ctx)) =
      g1AlignedConfigQ n (base + 3) (by omega) tape
        (g1State mode .p3 (tape ⟨base, by omega⟩)
          (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
          ctx) := by
    have hstep := g1CS_aligned_step_right n (base + 2) (by omega) (by omega) tape
      (g1State mode .p2 (tape ⟨base, by omega⟩)
        (tape ⟨base + 1, by omega⟩) false ctx)
      (g1State mode .p3 (tape ⟨base, by omega⟩)
        (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩) ctx)
      (tape ⟨base + 2, by omega⟩)
      (fun phase =>
        g1Transition_forward_p2 hforward phase _ _ false _ ctx)
    rwa [writeCell_self] at hstep
  have hs3 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n (base + 3) (by omega) tape
        (g1State mode .p3 (tape ⟨base, by omega⟩)
          (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
          ctx)) =
      g1AlignedConfigQ n (base + 3) (by omega) tape g1RejectState := by
    have hstep := g1CS_aligned_step_stay n (base + 3) (by omega) tape
      (g1State mode .p3 (tape ⟨base, by omega⟩)
        (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩) ctx)
      g1RejectState (tape ⟨base + 3, by omega⟩)
      (fun phase =>
        g1Transition_forward_p3_reject hforward phase _ _ _ _ ctx hcomplete)
    rwa [writeCell_self] at hstep
  rw [hs0, hs1, hs2, hs3]
  rfl

/-- Four leftward writes replace exactly one caller-supplied frame by
`cursor`, preserve the context and land on its predecessor's last cell. -/
theorem g1CS_aInstall_cursor (n : Nat) (pre suffix : List G1Frame)
    (old : G1Frame) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ old :: suffix).flatMap G1Frame.bits))
        .aIns .p3 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aSeekOut .p3 false false false ctx :=
  g1AInstallCursorWriter.writeFrameOnListLeft n pre suffix old ctx hpre hsafe

end Pnp3.Internal.PsubsetPpoly.TM
