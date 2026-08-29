import Complexity.TMVerifier.TuringToolkit.FrameScannerWriteLeft
import Complexity.TMVerifier.TuringToolkit.GateOnePassAControl

/-!
# Live G1 operand-A cursor installation

**Progress classification: Infrastructure.**  S4 composes the existing
operand-A installation scan, data probe/latch, out-of-range probe and four-cell
cursor writer through the single live `aInstallStart → aInsSeek` entry.  The
successful run stops at the writer's existing `aSeekOut .p3` boundary: the
cursor is complete, but no reverse seek, mark, round, iteration or repair step
executes.  Const, reject/malformed, operand-B, output and acceptance behavior
are unchanged.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private theorem g1AIConfig_congr (n h h' : Nat)
    (hh : h < G1M.tapeLength n) (hh' : h' < G1M.tapeLength n) (heq : h = h')
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode)
    (position : G1FramePosition) (b0 b1 b2 : Bool) (ctx : G1Ctx) :
    g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx =
      g1AlignedConfig n h' hh' tape mode position b0 b1 b2 ctx := by
  subst heq
  rfl

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

/-! ## S4 live composition -/

/-- Frames crossed after the pass-A tag latch and before the data separator. -/
def g1AInstallSkippedFrames (r : G1Request) : List G1Frame :=
  List.replicate r.arg1 .index ++
    G1Frame.argSep :: List.replicate r.arg2 .index

@[simp] theorem g1AInstallSkippedFrames_length (r : G1Request) :
    (g1AInstallSkippedFrames r).length = r.arg1 + r.arg2 + 1 := by
  simp [g1AInstallSkippedFrames]
  omega

/-- Exact S4 cost from `aInstallStart` through the completed cursor writer. -/
def g1ALiveInstallSteps (r : G1Request) : Nat :=
  1 + 4 * (r.arg1 + r.arg2 + 2) + 5 + 4

/-- Exact S4 empty-data cost from `aInstallStart` to `bOOB`. -/
def g1ALiveInstallOOBSteps (r : G1Request) : Nat :=
  1 + 4 * (r.arg1 + r.arg2 + 2) + 4

/-- The canonical frame word after replacing exactly data slot zero by the
designated cursor. -/
def g1AFirstCursorFrames (r : G1Request) : List G1Frame :=
  g1InstallRouteFrames r ++ G1Frame.cursor ::
    (r.vals.drop 1).map G1Frame.data ++
      [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- The exact dormant post-writer boundary.  `aIns .p3` is the pre-writer
latch endpoint; after all four writer steps the existing table is at
`aSeekOut .p3`, on the last cell preceding the cursor. -/
def g1APostWriterConfig (r : G1Request) (bA bB : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length
    (4 * (g1InstallRouteFrames r).length - 1)
    (by
      have h := g1_route_lt_tapeLength r
        (r.tag.units + r.arg1 + r.arg2 + 4) (by omega)
      rw [g1InstallRouteFrames_length]
      omega)
    (g1ListTape ((g1AFirstCursorFrames r).flatMap G1Frame.bits))
    .aSeekOut .p3 false false false
    (((g1Ctx0.withVB bB).withRes (g1Residual r.tag bB)).withVB bA)

/-- Exact empty-data endpoint: read-only tape, residual and operand-B latch
unchanged, at the existing stable OOB boundary. -/
def g1AInstallOOBConfig (r : G1Request) (bB : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length
    (4 * ((g1InstallRouteFrames r).length + 1))
    (by
      have h := g1_route_lt_tapeLength r
        (r.tag.units + r.arg1 + r.arg2 + 5) (by omega)
      rw [g1InstallRouteFrames_length]
      omega)
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .bOOB .p0 false false false
    ((g1Ctx0.withVB bB).withRes (g1Residual r.tag bB))

@[simp] theorem g1APostWriterConfig_res (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.ctx.res =
      g1Residual r.tag bB := by
  simp [g1APostWriterConfig, g1AlignedConfig, g1AlignedConfigQ, g1State]

@[simp] theorem g1APostWriterConfig_vB (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.ctx.vB = bA := rfl

@[simp] theorem g1APostWriterConfig_mode (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.mode = .aSeekOut := rfl

private theorem g1AInstallRoute_eq (r : G1Request) :
    g1TagRouteFrames r ++ g1AInstallSkippedFrames r ++ [.separator] =
      g1InstallRouteFrames r := by
  simp [g1TagRouteFrames, g1AInstallSkippedFrames, g1InstallRouteFrames,
    g1FieldRouteFrames, List.append_assoc]

private theorem g1AInstallSkippedFrames_skip (r : G1Request) :
    ∀ f ∈ g1AInstallSkippedFrames r, G1AInstallSkip f := by
  intro f hf
  simp only [g1AInstallSkippedFrames, List.mem_append, List.mem_replicate,
    List.mem_cons] at hf
  rcases hf with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ <;> trivial

private theorem g1AInstallScanFrames_probe (r : G1Request) (v : Bool)
    (rest : List Bool) :
    g1TagRouteFrames r ++ g1AInstallSkippedFrames r ++
        G1Frame.separator :: G1Frame.data v ::
          (rest.map G1Frame.data ++
            [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      g1InstallRouteFrames r ++ G1Frame.data v ::
        (rest.map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) := by
  rw [← g1AInstallRoute_eq r]
  simp [List.append_assoc]

private theorem g1AInstallScanFrames_oob (r : G1Request) :
    g1TagRouteFrames r ++ g1AInstallSkippedFrames r ++
        [G1Frame.separator, G1Frame.output false, G1Frame.finish, G1Frame.blank] =
      g1InstallRouteFrames r ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] := by
  rw [← g1AInstallRoute_eq r]
  simp [List.append_assoc]

private theorem g1AInstallSplit_probe (r : G1Request) (v : Bool)
    (rest : List Bool) (hv : r.vals = v :: rest) :
    g1InstallRouteFrames r ++ G1Frame.data v ::
        (rest.map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) =
      encodeG1Frames r ++ [G1Frame.blank] := by
  rw [← g1InstallRoute_split r, g1InstallRouteRest, hv]
  simp

private theorem g1AInstallSplit_oob (r : G1Request) (hv : r.vals = []) :
    g1InstallRouteFrames r ++ G1Frame.output false ::
        [G1Frame.finish, G1Frame.blank] =
      encodeG1Frames r ++ [G1Frame.blank] := by
  rw [← g1InstallRoute_split r, g1InstallRouteRest, hv]
  simp

private theorem g1AInitialTape (r : G1Request) :
    (G1M.initialConfig (g1Point (encodeG1 r))).tape =
      g1ListTape (n := (encodeG1 r).length)
        ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits) := by
  rw [← g1ListTape_validation_eq_initial r]
  rfl

/-- Exact live installation from the residual-latched boundary.  It scans both
operand-index fields, probes and latches data slot zero, replaces exactly that
frame by `cursor`, and stops at the dormant post-writer boundary. -/
theorem g1CS_aInstall_success_exact (r : G1Request) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (g1AInstallConfig r bB)
        (g1ALiveInstallSteps r) = g1APostWriterConfig r bA bB := by
  let ctx := (g1Ctx0.withVB bB).withRes (g1Residual r.tag bB)
  have hpre : (g1InstallRouteFrames r).length =
      r.tag.units + r.arg1 + r.arg2 + 4 := g1InstallRouteFrames_length r
  have hsplit := g1AInstallSplit_probe r bA rest hv
  have hscan := g1CS_aInstall_scan (encodeG1 r).length
    (g1TagRouteFrames r) (g1AInstallSkippedFrames r)
    (G1Frame.data bA ::
      (rest.map G1Frame.data ++ [.output false, .finish, .blank]))
    ctx (g1AInstallSkippedFrames_skip r)
    (by simp only [g1TagRouteFrames_length, g1AInstallSkippedFrames_length];
        have h := g1_route_lt_tapeLength r
          (r.tag.units + r.arg1 + r.arg2 + 4) (by omega)
        omega)
  have hprobe := g1CS_aProbe_latch (encodeG1 r).length
    (g1InstallRouteFrames r)
    (rest.map G1Frame.data ++ [.output false, .finish, .blank])
    bA ctx (by
      rw [hpre]
      have h := g1_route_lt_tapeLength r
        (r.tag.units + r.arg1 + r.arg2 + 5) (by omega)
      omega)
  have hwrite := g1CS_aInstall_cursor (encodeG1 r).length
    (g1InstallRouteFrames r)
    (rest.map G1Frame.data ++ [.output false, .finish, .blank])
    (G1Frame.data bA) (ctx.withVB bA)
    (by rw [hpre]; omega)
    (by
      rw [hpre]
      have h := g1_route_lt_tapeLength r
        (r.tag.units + r.arg1 + r.arg2 + 5) (by omega)
      omega)
  rw [g1ALiveInstallSteps,
    show 1 + 4 * (r.arg1 + r.arg2 + 2) + 5 + 4 =
      1 + (4 * (r.arg1 + r.arg2 + 2) + (5 + 4)) by omega,
    runConfig_add, g1CS_aInstall_entry_initial_exact,
    runConfig_add]
  rw [g1AInstallScanFrames_probe r bA rest] at hscan
  simp only [g1TagRouteFrames_length, g1AInstallSkippedFrames_length] at hscan
  have hscanSteps : 4 * (r.arg1 + r.arg2 + 1 + 1) =
      4 * (r.arg1 + r.arg2 + 2) := by omega
  have hscanHead :
      4 * (r.tag.units + 2 + (r.arg1 + r.arg2 + 1 + 1)) =
        4 * (r.tag.units + r.arg1 + r.arg2 + 4) := by omega
  rw [hscanSteps] at hscan
  have hseek : TM.runConfig (M := G1M) (g1AInstallSeekConfig r bB)
      (4 * (r.arg1 + r.arg2 + 2)) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1InstallRouteFrames r).length) (by
          rw [hpre]
          have h := g1_route_lt_tapeLength r
            (r.tag.units + r.arg1 + r.arg2 + 4) (by omega)
          exact h)
        (g1ListTape
          ((g1InstallRouteFrames r ++ G1Frame.data bA ::
            (rest.map G1Frame.data ++ [.output false, .finish, .blank])).flatMap
            G1Frame.bits))
        .aProbe .p0 false false false ctx := by
    rw [g1AInstallSeekConfig, g1AInitialTape r, ← hsplit]
    simp only [ctx]
    refine Eq.trans hscan ?_
    apply g1AIConfig_congr
    rw [hpre]
    exact hscanHead
  rw [hseek, runConfig_add]
  rw [hprobe]
  simpa [g1APostWriterConfig, g1AFirstCursorFrames, hv, ctx] using hwrite

/-- Exact empty-data route from the residual-latched boundary.  The scan and
probe are read-only and reach `bOOB`; no cursor writer is entered. -/
theorem g1CS_aInstall_oob_exact (r : G1Request) (bB : Bool)
    (hv : r.vals = []) :
    TM.runConfig (M := G1M) (g1AInstallConfig r bB)
        (g1ALiveInstallOOBSteps r) = g1AInstallOOBConfig r bB := by
  let ctx := (g1Ctx0.withVB bB).withRes (g1Residual r.tag bB)
  have hpre : (g1InstallRouteFrames r).length =
      r.tag.units + r.arg1 + r.arg2 + 4 := g1InstallRouteFrames_length r
  have hsplit := g1AInstallSplit_oob r hv
  have hscan := g1CS_aInstall_scan (encodeG1 r).length
    (g1TagRouteFrames r) (g1AInstallSkippedFrames r)
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]
    ctx (g1AInstallSkippedFrames_skip r)
    (by simp only [g1TagRouteFrames_length, g1AInstallSkippedFrames_length];
        have h := g1_route_lt_tapeLength r
          (r.tag.units + r.arg1 + r.arg2 + 4) (by omega)
        omega)
  have hoob := g1CS_aProbe_oob (encodeG1 r).length
    (g1InstallRouteFrames r) [G1Frame.finish, G1Frame.blank] ctx
    (by
      rw [hpre]
      have h := g1_route_lt_tapeLength r
        (r.tag.units + r.arg1 + r.arg2 + 5) (by omega)
      omega)
  rw [g1ALiveInstallOOBSteps,
    show 1 + 4 * (r.arg1 + r.arg2 + 2) + 4 =
      1 + (4 * (r.arg1 + r.arg2 + 2) + 4) by omega,
    runConfig_add, g1CS_aInstall_entry_initial_exact, runConfig_add]
  rw [g1AInstallScanFrames_oob r] at hscan
  simp only [g1TagRouteFrames_length, g1AInstallSkippedFrames_length] at hscan
  have hscanSteps : 4 * (r.arg1 + r.arg2 + 1 + 1) =
      4 * (r.arg1 + r.arg2 + 2) := by omega
  have hscanHead :
      4 * (r.tag.units + 2 + (r.arg1 + r.arg2 + 1 + 1)) =
        4 * (r.tag.units + r.arg1 + r.arg2 + 4) := by omega
  rw [hscanSteps] at hscan
  have hseek : TM.runConfig (M := G1M) (g1AInstallSeekConfig r bB)
      (4 * (r.arg1 + r.arg2 + 2)) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1InstallRouteFrames r).length) (by
          rw [hpre]
          have h := g1_route_lt_tapeLength r
            (r.tag.units + r.arg1 + r.arg2 + 4) (by omega)
          exact h)
        (g1ListTape
          ((g1InstallRouteFrames r ++
            [G1Frame.output false, G1Frame.finish, G1Frame.blank]).flatMap
            G1Frame.bits))
        .aProbe .p0 false false false ctx := by
    rw [g1AInstallSeekConfig, g1AInitialTape r, ← hsplit]
    simp only [ctx]
    refine Eq.trans hscan ?_
    apply g1AIConfig_congr
    rw [hpre]
    exact hscanHead
  rw [hseek]
  rw [g1AInstallOOBConfig, g1AInitialTape r, ← hsplit]
  simpa [hpre, Nat.mul_add] using hoob

/-! ## Real-initial capstones and unchanged clock -/

def g1AUnaryCursorSteps (r : G1Request) : Nat :=
  g1UActivatedSteps r + (4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r

def g1ABinaryCursorSteps (r : G1Request) : Nat :=
  g1BActivatedSteps r + (4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r

def g1AUnaryOOBSteps (r : G1Request) : Nat :=
  g1UActivatedSteps r + (4 * (r.tag.units + 2) + 1) +
    g1ALiveInstallOOBSteps r

/-- Every unary `input`/`not` route with nonempty data runs from the genuine
initial configuration to the exact post-writer boundary. -/
theorem g1CS_aCursor_unary_initial_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (bA : Bool) (rest : List Bool)
    (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r) = g1APostWriterConfig r bA false := by
  rw [g1AUnaryCursorSteps, runConfig_add,
    g1CS_install_unary_exact r hc ht]
  exact g1CS_aInstall_success_exact r bA false rest hv

/-- Every successful binary route retains its physically read operand-B value
in the latched residual while `vB` becomes operand A at the post-writer
boundary. -/
theorem g1CS_aCursor_binary_initial_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (bA bB : Bool) (rest : List Bool)
    (hB : r.vals[r.arg2]? = some bB) (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r) = g1APostWriterConfig r bA bB := by
  rw [g1ABinaryCursorSteps, runConfig_add,
    g1CS_install_binary_exact r hc ht bB hB]
  exact g1CS_aInstall_success_exact r bA bB rest hv

/-- Canonical non-`const` requests may have empty data.  Unary routes therefore
have a genuine executable initial-configuration OOB capstone. -/
theorem g1CS_aInstall_unary_oob_initial_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (hv : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryOOBSteps r) = g1AInstallOOBConfig r false := by
  rw [g1AUnaryOOBSteps, runConfig_add,
    g1CS_install_unary_exact r hc ht]
  exact g1CS_aInstall_oob_exact r false hv

/-- A successful binary-read premise rules out the empty-data case precisely;
this is not used to overclaim an unreachable binary OOB run. -/
theorem g1A_binary_success_not_empty (r : G1Request) (b : Bool)
    (hB : r.vals[r.arg2]? = some b) : r.vals ≠ [] := by
  intro hv
  rw [hv] at hB
  simp at hB

@[simp] theorem g1AFirstCursorFrames_count_cursor (r : G1Request) :
    (g1AFirstCursorFrames r).count .cursor = 1 := by
  have hmap : ∀ xs : List Bool,
      (xs.map G1Frame.data).count G1Frame.cursor = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons b xs ih => simp [ih]
  have htail : ∀ xs : List Bool,
      (xs.map G1Frame.data).tail.count G1Frame.cursor = 0 := by
    intro xs
    cases xs <;> simp [hmap]
  simp [g1AFirstCursorFrames, g1InstallRouteFrames, g1FieldRouteFrames,
    List.count_replicate, htail]

@[simp] theorem g1APostWriterConfig_head (r : G1Request) (bA bB : Bool) :
    ((g1APostWriterConfig r bA bB).head : Nat) =
      4 * (r.tag.units + r.arg1 + r.arg2 + 4) - 1 := by
  simp [g1APostWriterConfig]

@[simp] theorem g1APostWriterConfig_tape (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).tape =
      g1ListTape ((g1AFirstCursorFrames r).flatMap G1Frame.bits) := rfl

/-- The boundary is exact and dormant: the completed writer has entered
`aSeekOut`, but it has not executed seek, probe, repair or combine. -/
theorem g1APostWriterConfig_no_wrong_exit (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.mode = .aSeekOut ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .aIns ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .aProbe ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .aRepairStart ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .combineStart := by
  exact ⟨rfl, G1Mode.noConfusion, G1Mode.noConfusion, G1Mode.noConfusion,
    G1Mode.noConfusion⟩

private theorem g1AIClock_sq (k : Nat) :
    (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by
  rw [Nat.pow_two, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
  omega

private theorem g1AIClock_quad (N : Nat) :
    g1Clock (4 * N) = 8192 * N ^ 2 + (4096 * N + 1024) := by
  rw [g1Clock, g1AIClock_sq, Nat.mul_pow, show (4 : Nat) ^ 2 = 16 from rfl]
  omega

private theorem g1AIClock_eq (r : G1Request) :
    g1Clock (encodeG1 r).length =
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 +
        (4096 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) + 1024) := by
  rw [encodeG1_length r, g1AIClock_quad]

theorem g1AUnaryCursorSteps_le_clock (r : G1Request) :
    g1AUnaryCursorSteps r ≤ g1Clock (encodeG1 r).length := by
  have hlen := encodeG1_length r
  rw [g1AIClock_eq]
  simp only [g1AUnaryCursorSteps, g1ALiveInstallSteps, g1UActivatedSteps,
    g1UReadASteps, g1ReadARouteSteps, g1ReadBHandoffSteps,
    g1AUnaryRewindSteps, hlen]
  omega

theorem g1ABinaryCursorSteps_le_clock (r : G1Request) :
    g1ABinaryCursorSteps r ≤ g1Clock (encodeG1 r).length := by
  have hlen := encodeG1_length r
  have hsq : 8 * r.arg2 ^ 2 ≤
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  rw [g1AIClock_eq]
  simp only [g1ABinaryCursorSteps, g1ALiveInstallSteps, g1BActivatedSteps,
    g1BPassASteps, g1BReadSteps, g1InstallScanSteps, g1ZPassASteps,
    g1ReadBSteps, g1RepairSteps, g1ReadBHandoffSteps, hlen]
  split_ifs <;> omega

theorem g1AUnaryOOBSteps_le_clock (r : G1Request) :
    g1AUnaryOOBSteps r ≤ g1Clock (encodeG1 r).length := by
  have hlen := encodeG1_length r
  rw [g1AIClock_eq]
  simp only [g1AUnaryOOBSteps, g1ALiveInstallOOBSteps, g1UActivatedSteps,
    g1UReadASteps, g1ReadARouteSteps, g1ReadBHandoffSteps,
    g1AUnaryRewindSteps, hlen]
  omega

/-- Run-level unary no-wrong-exit closure at the completed writer boundary. -/
theorem g1CS_aCursor_unary_no_wrong_exit (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (bA : Bool) (rest : List Bool)
    (hv : r.vals = bA :: rest) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r)).state.snd.mode = .aSeekOut ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r)).state.snd.mode ≠ .combineStart := by
  rw [g1CS_aCursor_unary_initial_exact r hc ht bA rest hv]
  exact ⟨rfl, G1Mode.noConfusion⟩

/-- Run-level binary no-wrong-exit closure at the completed writer boundary. -/
theorem g1CS_aCursor_binary_no_wrong_exit (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (bA bB : Bool) (rest : List Bool)
    (hB : r.vals[r.arg2]? = some bB) (hv : r.vals = bA :: rest) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r)).state.snd.mode = .aSeekOut ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r)).state.snd.mode ≠ .combineStart := by
  rw [g1CS_aCursor_binary_initial_exact r hc ht bA bB rest hB hv]
  exact ⟨rfl, G1Mode.noConfusion⟩

namespace G1ALiveInstallExamples

def reqInputFalse : G1Request := ⟨.input, 0, 0, [false]⟩
def reqNotTrue : G1Request := ⟨.not, 0, 0, [true]⟩
def reqAndFalse : G1Request := ⟨.and, 0, 0, [false]⟩
def reqOrTrue : G1Request := ⟨.or, 0, 0, [true]⟩
def reqInputOOB : G1Request := ⟨.input, 0, 0, []⟩

theorem requests_canonical :
    reqInputFalse.Canonical ∧ reqNotTrue.Canonical ∧
      reqAndFalse.Canonical ∧ reqOrTrue.Canonical ∧
      reqInputOOB.Canonical := by decide

theorem input_false_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 131 =
      g1APostWriterConfig reqInputFalse false false := by
  have h := g1CS_aCursor_unary_initial_exact reqInputFalse
    requests_canonical.1 (Or.inl rfl) false [] rfl
  simpa [g1AUnaryCursorSteps, g1ALiveInstallSteps, g1UActivatedSteps,
    g1UReadASteps, g1ReadARouteSteps, g1ReadBHandoffSteps,
    g1AUnaryRewindSteps] using h

theorem not_true_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 171 =
      g1APostWriterConfig reqNotTrue true false := by
  have h := g1CS_aCursor_unary_initial_exact reqNotTrue
    requests_canonical.2.1 (Or.inr rfl) true [] rfl
  simpa [g1AUnaryCursorSteps, g1ALiveInstallSteps, g1UActivatedSteps,
    g1UReadASteps, g1ReadARouteSteps, g1ReadBHandoffSteps,
    g1AUnaryRewindSteps] using h

theorem and_false_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 216 =
      g1APostWriterConfig reqAndFalse false false := by
  have h := g1CS_aCursor_binary_initial_exact reqAndFalse
    requests_canonical.2.2.1 (Or.inl rfl) false false [] rfl rfl
  simpa [g1ABinaryCursorSteps, g1ALiveInstallSteps, g1BActivatedSteps,
    g1ZPassASteps, g1ReadBSteps, g1RepairSteps, g1ReadBHandoffSteps] using h

theorem or_true_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 236 =
      g1APostWriterConfig reqOrTrue true true := by
  have h := g1CS_aCursor_binary_initial_exact reqOrTrue
    requests_canonical.2.2.2.1 (Or.inr rfl) true true [] rfl rfl
  simpa [g1ABinaryCursorSteps, g1ALiveInstallSteps, g1BActivatedSteps,
    g1ZPassASteps, g1ReadBSteps, g1RepairSteps, g1ReadBHandoffSteps] using h

theorem input_empty_oob_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputOOB))) 118 =
      g1AInstallOOBConfig reqInputOOB false := by
  have h := g1CS_aInstall_unary_oob_initial_exact reqInputOOB
    requests_canonical.2.2.2.2 (Or.inl rfl) rfl
  simpa [g1AUnaryOOBSteps, g1ALiveInstallOOBSteps, g1UActivatedSteps,
    g1UReadASteps, g1ReadARouteSteps, g1ReadBHandoffSteps,
    g1AUnaryRewindSteps] using h

theorem literal_clock_bounds :
    131 ≤ g1Clock (encodeG1 reqInputFalse).length ∧
      171 ≤ g1Clock (encodeG1 reqNotTrue).length ∧
      216 ≤ g1Clock (encodeG1 reqAndFalse).length ∧
      236 ≤ g1Clock (encodeG1 reqOrTrue).length ∧
      118 ≤ g1Clock (encodeG1 reqInputOOB).length := by decide

end G1ALiveInstallExamples

end Pnp3.Internal.PsubsetPpoly.TM
