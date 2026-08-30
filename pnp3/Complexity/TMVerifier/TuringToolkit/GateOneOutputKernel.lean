import Complexity.TMVerifier.TuringToolkit.GateOneAResult

/-!
# S10a dormant G1 output scan/turn/write kernel (2026-08-30)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

This module executes a caller-supplied output scan on the current five-tag G1
ABI.  It scans exactly the repaired canonical prefix, stops only on the unique
`output false`, turns one cell left, and uses one of two literal four-cell
writers to install `output res`.  The endpoint is the local stationary
`outputDoneFalse`/`outputDoneTrue` boundary.

The kernel is deliberately dormant.  `combineStart` remains stationary and no
live result route enters an output mode.  There is no combine bridge, accept
transition, `TM.accepts` theorem, full-initial composition, clock composition,
or claim about a request whose specification is `none`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Strict scan grammar -/

/-- Exactly the frame kinds permitted before the destination. -/
def G1OutputSkip : G1Frame → Prop
  | .bof | .tag | .argSep | .index | .separator | .data _ => True
  | _ => False

instance : DecidablePred G1OutputSkip := fun f => by
  cases f <;> first | exact isTrue trivial | exact isFalse id

theorem G1OutputSkip_ne_output {f : G1Frame} (h : G1OutputSkip f) (v : Bool) :
    f ≠ .output v := by
  cases f <;> simp_all [G1OutputSkip]

theorem G1OutputSkip_ne_spent {f : G1Frame} (h : G1OutputSkip f) :
    f ≠ .spent := by
  cases f <;> simp_all [G1OutputSkip]

theorem G1OutputSkip_ne_cursor {f : G1Frame} (h : G1OutputSkip f) :
    f ≠ .cursor := by
  cases f <;> simp_all [G1OutputSkip]

theorem g1Advance_outSeek_of_skip {f : G1Frame} (h : G1OutputSkip f) :
    g1Advance .outSeek f = .outSeek := by
  cases f <;> first | rfl | exact (show False from h).elim

theorem g1Advance_outSeek_output_false :
    g1Advance .outSeek (.output false) = .outTurn := rfl

/-- Every decoded frame outside the strict prefix or target grammar rejects. -/
theorem g1Advance_outSeek_reject_iff (f : G1Frame) :
    g1Advance .outSeek f = .reject ↔
      f = .blank ∨ f = .cursor ∨ f = .output true ∨
        f = .finish ∨ f = .spent := by
  revert f
  decide

theorem g1Advance_outSeek_forbidden :
    g1Advance .outSeek (.output true) = .reject ∧
      g1Advance .outSeek .spent = .reject ∧
      g1Advance .outSeek .cursor = .reject ∧
      g1Advance .outSeek .finish = .reject ∧
      g1Advance .outSeek .blank = .reject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Malformed and all three reserved raw windows reject at completion. -/
theorem g1Complete_outSeek_malformed_reserved
    {b0 b1 b2 b3 : Bool}
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    g1Complete .outSeek b0 b1 b2 b3 = .reject ∧
      g1Complete .outSeek true true false true = .reject ∧
      g1Complete .outSeek true true true false = .reject ∧
      g1Complete .outSeek true true true true = .reject := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp [g1Complete, hbad]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
/-- Executable predecessor closure: no transition from outside the six output
modes can enter them.  Thus the caller-supplied start is genuinely dormant. -/
theorem g1Transition_outputKernel_predecessor (phase : Fin 1) (s : G1State)
    (scan : Bool)
    (h : G1OutputKernelMode (g1Transition phase s scan).2.1.mode) :
    G1OutputKernelMode s.mode := by
  obtain ⟨mode, position, b0, b1, b2, ctx⟩ := s
  obtain ⟨pass, crossed, vB⟩ := ctx
  cases mode <;> cases position <;>
    first
      | exact trivial
      | exact False.elim h
      | (cases vB <;> exact False.elim h)
      | (cases pass <;> exact False.elim h)
      | (simp only [g1Transition, g1State] at h
         split at h <;>
           first
             | exact False.elim h
             | exact g1Complete_outputKernel_predecessor _ _ _ _ _ h)

/-- In particular, the unchanged stationary combine row does not enter S10a. -/
theorem g1Transition_combineStart_not_output (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    ¬ G1OutputKernelMode
      (g1Transition phase
        (g1State .combineStart position b0 b1 b2 ctx) scan).2.1.mode := by
  rw [g1Transition_combineStart_idle]
  exact id

/-! ## Exact caller-supplied atoms -/

/-- The strict scan crosses `skipped` and consumes exactly the target frame. -/
theorem g1CS_out_scan (n : Nat) (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1OutputSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length) (by omega)
          (g1ListTape
            ((pre ++ skipped ++ G1Frame.output false :: suffix).flatMap
              G1Frame.bits))
          .outSeek .p0 false false false ctx)
        (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.output false :: suffix).flatMap
            G1Frame.bits))
        .outTurn .p0 false false false ctx := by
  have hfix : ∀ f ∈ skipped, g1Advance .outSeek f = .outSeek :=
    fun f hf => g1Advance_outSeek_of_skip (hskip f hf)
  have hlen : (skipped ++ [G1Frame.output false]).length = skipped.length + 1 := by
    simp
  have hlist : pre ++ (skipped ++ [G1Frame.output false]) ++ suffix =
      pre ++ skipped ++ G1Frame.output false :: suffix := by
    simp [List.append_assoc]
  have hpath : G1ValidPath .outSeek (skipped ++ [G1Frame.output false]) :=
    g1ValidPath_fix (mode := .outSeek) trivial [G1Frame.output false]
      ⟨trivial, by decide, trivial⟩ skipped hfix
  have hfold : g1AdvanceList .outSeek
      (skipped ++ [G1Frame.output false]) = .outTurn := by
    rw [g1AdvanceList_fix (mode := .outSeek) [G1Frame.output false] skipped hfix]
    rfl
  have hscan := g1FrameScanner_scanFrames n pre
    (skipped ++ [G1Frame.output false]) suffix .outSeek ctx
    ((g1FrameScanner_validPath _ _).mpr hpath) (by rw [hlen]; exact hsafe)
  simpa only [hlist, hlen, g1AlignedFrame_eq, g1FrameScanner_advanceList,
    hfold] using hscan

/-- One tape-preserving turn selects the false/true writer from `ctx.vB`. -/
theorem g1CS_out_turn (n h : Nat) (hh : h < G1M.tapeLength n) (hpos : 0 < h)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .outTurn .p0 false false false ctx) 1 =
      g1AlignedConfigQ n (h - 1) (by omega) tape
        (g1OutWriteState ctx.vB ctx) := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_left n h hh hpos tape (g1OutTurnState ctx)
    (g1OutWriteState ctx.vB ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_outTurn phase .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-- A result-indexed generic reverse writer for the literal `output res`. -/
def g1OutWriter (res : Bool) : ReverseFrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := fun _ => .output res
  w0 := fun _ => true
  w1 := fun _ => false
  w2 := fun _ => false
  w3 := fun _ => res
  lst3 := fun ctx => g1OutWriteState res ctx
  lst2 := fun ctx => g1State (g1OutWriteMode res) .p2 false false false ctx
  lst1 := fun ctx => g1State (g1OutWriteMode res) .p1 false false false ctx
  lst0 := fun ctx => g1State (g1OutWriteMode res) .p0 false false false ctx
  exitState := fun _ => g1OutputDoneState res
  target_bits := by cases res <;> intro ctx <;> rfl
  lstep_p3 := fun ctx scan =>
    g1Transition_outWrite g1CS.startPhase res .p3 false false false scan ctx
  lstep_p2 := fun ctx scan =>
    g1Transition_outWrite g1CS.startPhase res .p2 false false false scan ctx
  lstep_p1 := fun ctx scan =>
    g1Transition_outWrite g1CS.startPhase res .p1 false false false scan ctx
  lstep_p0 := fun ctx scan =>
    g1Transition_outWrite g1CS.startPhase res .p0 false false false scan ctx

@[simp] theorem g1OutWriter_machine (res : Bool) :
    (g1OutWriter res).machine = G1M := rfl

/-- Four cells replace exactly the designated `output false` frame. -/
theorem g1CS_out_write (n : Nat) (pre suffix : List G1Frame) (res : Bool)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfigQ n (4 * pre.length + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
          (g1OutWriteState res ctx)) 4 =
      g1AlignedConfigQ n (4 * pre.length - 1) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.output res :: suffix).flatMap G1Frame.bits))
        (g1OutputDoneState res) :=
  (g1OutWriter res).writeFrameOnListLeft n pre suffix (.output false) ctx
    hpre hsafe

/-- The local output-complete boundary stays fixed for every further budget. -/
theorem g1CS_outputDone_stable (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (res : Bool) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfigQ n h hh tape (g1OutputDoneState res)) k =
      g1AlignedConfigQ n h hh tape (g1OutputDoneState res) :=
  g1CS_runConfig_stable n h hh tape (g1OutputDoneState res)
    (fun phase scan => g1Transition_outputDone_stable phase res scan) k

/-! ## Canonical output layout -/

def g1OutputFrames (r : G1Request) (res : Bool) : List G1Frame :=
  g1PrefixFrames r ++ [.output res, .finish, .blank]

theorem g1OutputFrames_false (r : G1Request) :
    g1OutputFrames r false = g1ValidationFrames r := by
  rw [g1OutputFrames, g1ValidationFrames, encodeG1Frames_eq_prefix]
  simp [List.append_assoc]

@[simp] theorem g1OutputFrames_length (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp only [g1OutputFrames, List.length_append, g1PrefixFrames_length,
    List.length_cons, List.length_nil]

def g1OutputBase (r : G1Request) : Nat := 4 * (g1PrefixFrames r).length

theorem g1OutputBase_eq (r : G1Request) :
    g1OutputBase r =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) := by
  rw [g1OutputBase, g1PrefixFrames_length]

theorem g1OutputPosition_eq_base (r : G1Request) :
    g1OutputPosition r = g1OutputBase r + 3 := by
  rw [g1OutputBase_eq, g1OutputPosition]

theorem g1OutputBase_pos (r : G1Request) : 0 < g1OutputBase r := by
  rw [g1OutputBase_eq]
  omega

def g1OutputExitHead (r : G1Request) : Nat := g1OutputBase r - 1

theorem g1OutputBase_safe (r : G1Request) :
    g1OutputBase r + 4 < G1M.tapeLength (encodeG1 r).length := by
  have h := g1_route_lt_tapeLength r
    (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5) (by omega)
  rw [g1OutputBase_eq]
  omega

theorem g1OutputExitHead_safe (r : G1Request) :
    g1OutputExitHead r < G1M.tapeLength (encodeG1 r).length := by
  have h := g1OutputBase_safe r
  rw [g1OutputExitHead]
  omega

theorem g1OutputTape_false (r : G1Request) :
    g1ListTape (n := (encodeG1 r).length)
        ((g1OutputFrames r false).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1OutputFrames_false]
  exact g1ListTape_validation_eq_initial r

private theorem g1OutputFrames_split (r : G1Request) (res : Bool) :
    g1OutputFrames r res =
      g1PrefixFrames r ++ G1Frame.output res :: [.finish, .blank] := rfl

private theorem g1WriteOutputFrame {L : Nat} (base : Nat) (res : Bool)
    (tape : Fin L → Bool)
    (h0 : ∀ i : Fin L, (i : Nat) = base → tape i = true)
    (h1 : ∀ i : Fin L, (i : Nat) = base + 1 → tape i = false)
    (h2 : ∀ i : Fin L, (i : Nat) = base + 2 → tape i = false) :
    writeFrame4 base true false false res tape =
      writeCell (base + 3) res tape := by
  funext i
  rw [writeFrame4_apply]
  by_cases hi0 : (i : Nat) = base
  · rw [if_pos hi0]
    simp only [writeCell, if_neg (show (i : Nat) ≠ base + 3 by omega)]
    exact (h0 i hi0).symm
  · rw [if_neg hi0]
    by_cases hi1 : (i : Nat) = base + 1
    · rw [if_pos hi1]
      simp only [writeCell, if_neg (show (i : Nat) ≠ base + 3 by omega)]
      exact (h1 i hi1).symm
    · rw [if_neg hi1]
      by_cases hi2 : (i : Nat) = base + 2
      · rw [if_pos hi2]
        simp only [writeCell, if_neg (show (i : Nat) ≠ base + 3 by omega)]
        exact (h2 i hi2).symm
      · rw [if_neg hi2]
        by_cases hi3 : (i : Nat) = base + 3
        · rw [if_pos hi3]
          simp [writeCell, hi3]
        · rw [if_neg hi3]
          simp [writeCell, hi3]

/-- The final layout is exactly one designated-cell write on the initial tape. -/
theorem g1OutputTape_eq_writeCell (r : G1Request) (res : Bool) :
    g1ListTape (n := (encodeG1 r).length)
        ((g1OutputFrames r res).flatMap G1Frame.bits) =
      writeCell (g1OutputPosition r) res
        (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  have hsafe : 4 * (g1PrefixFrames r).length + 4 <
      G1M.tapeLength (encodeG1 r).length := by
    have h := g1OutputBase_safe r
    rw [g1OutputBase] at h
    exact h
  have hfalse : frameListTape (L := G1M.tapeLength (encodeG1 r).length)
      ((g1OutputFrames r false).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := g1OutputTape_false r
  have hwrite := writeFrame4_frameListTape
    (L := G1M.tapeLength (encodeG1 r).length) g1FrameCodec (g1PrefixFrames r)
    [G1Frame.finish, G1Frame.blank] (G1Frame.output false)
    (G1Frame.output res) (b0 := true) (b1 := false) (b2 := false) (b3 := res)
    (by cases res <;> rfl)
  simp only [g1FrameCodec_bits] at hwrite
  rw [← g1OutputFrames_split r res, ← g1OutputFrames_split r false,
    hfalse] at hwrite
  have hbits : physicalBitsAt (h := 4 * (g1PrefixFrames r).length) hsafe
      (G1M.initialConfig (g1Point (encodeG1 r))).tape =
      (G1Frame.output false).bits := by
    have hraw := physicalBitsAt_flatMap
      (L := G1M.tapeLength (encodeG1 r).length) g1FrameCodec
      (g1PrefixFrames r) [G1Frame.finish, G1Frame.blank]
      (G1Frame.output false) hsafe
    simp only [g1FrameCodec_bits] at hraw
    rw [← g1OutputFrames_split r false, hfalse] at hraw
    exact hraw
  simp only [physicalBitsAt, G1Frame.bits, List.cons.injEq] at hbits
  obtain ⟨hb0, hb1, hb2, -⟩ := hbits
  show frameListTape (L := G1M.tapeLength (encodeG1 r).length)
      ((g1OutputFrames r res).flatMap G1Frame.bits) = _
  rw [← hwrite, g1OutputPosition_eq_base, g1OutputBase]
  refine g1WriteOutputFrame (4 * (g1PrefixFrames r).length) res _ ?_ ?_ ?_
  · intro i hi
    have hfin : i = (⟨4 * (g1PrefixFrames r).length, by omega⟩ : Fin _) :=
      Fin.ext hi
    rw [hfin]
    exact hb0
  · intro i hi
    have hfin : i =
        (⟨4 * (g1PrefixFrames r).length + 1, by omega⟩ : Fin _) := Fin.ext hi
    rw [hfin]
    exact hb1
  · intro i hi
    have hfin : i =
        (⟨4 * (g1PrefixFrames r).length + 2, by omega⟩ : Fin _) := Fin.ext hi
    rw [hfin]
    exact hb2

theorem g1OutputTape_at (r : G1Request) (res : Bool)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) i = res := by
  rw [g1OutputTape_eq_writeCell]
  simp [writeCell, hi]

theorem g1OutputTape_off (r : G1Request) (res : Bool)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) ≠ g1OutputPosition r) :
    g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) i =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape i := by
  rw [g1OutputTape_eq_writeCell]
  simp [writeCell, hi]

theorem g1OutputTape_true_ne_initial (r : G1Request)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    g1ListTape ((g1OutputFrames r true).flatMap G1Frame.bits) i ≠
      (G1M.initialConfig (g1Point (encodeG1 r))).tape i := by
  rw [g1OutputTape_at r true i hi]
  have hfalse := g1OutputTape_eq_writeCell r false
  rw [g1OutputTape_false] at hfalse
  rw [hfalse]
  simp [writeCell, hi]

theorem g1OutputTape_false_identity (r : G1Request) :
    g1ListTape ((g1OutputFrames r false).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1OutputTape_false r

private theorem g1OutputCount_unchanged (r : G1Request) (res : Bool)
    (f : G1Frame) (hout : ∀ b : Bool, f ≠ .output b)
    (hfinish : f ≠ .finish) (hblank : f ≠ .blank) :
    (g1OutputFrames r res).count f =
      (g1OutputFrames r false).count f := by
  cases res
  · rfl
  · simp [g1OutputFrames, List.count_append, Ne.symm (hout true),
      Ne.symm (hout false), Ne.symm hfinish, Ne.symm hblank]

theorem g1OutputFrames_count_spent (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count .spent = 0 := by
  rw [g1OutputCount_unchanged r res .spent (by decide) (by decide) (by decide),
    g1OutputFrames_false]
  exact g1ARepairCanonical_count_spent r

theorem g1OutputFrames_count_cursor (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count .cursor = 0 := by
  rw [g1OutputCount_unchanged r res .cursor (by decide) (by decide) (by decide),
    g1OutputFrames_false]
  exact g1ARepairCanonical_count_cursor r

theorem g1OutputFrames_count_index (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count .index = r.arg1 + r.arg2 := by
  rw [g1OutputCount_unchanged r res .index (by decide) (by decide) (by decide),
    g1OutputFrames_false]
  exact g1ARepairCanonical_count_index r

theorem g1PrefixFrames_outSkip (r : G1Request) :
    ∀ f ∈ g1PrefixFrames r, G1OutputSkip f := by
  intro f hf
  cases f with
  | bof | tag | index | separator | argSep => trivial
  | data b => trivial
  | blank | cursor | output b | finish | spent =>
      simp [g1PrefixFrames] at hf

theorem g1PrefixFrames_ne_output (r : G1Request) (res : Bool) :
    ∀ f ∈ g1PrefixFrames r, f ≠ .output res := fun f hf =>
  G1OutputSkip_ne_output (g1PrefixFrames_outSkip r f hf) res

private theorem g1PrefixFrames_count_output (r : G1Request) (res : Bool) :
    (g1PrefixFrames r).count (.output res) = 0 :=
  List.count_eq_zero.2 (fun h => g1PrefixFrames_ne_output r res _ h rfl)

theorem g1OutputFrames_count_output (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count (.output res) = 1 := by
  simp [g1OutputFrames, List.count_append, g1PrefixFrames_count_output]

theorem g1OutputFrames_count_other_output (r : G1Request) (res : Bool) :
    (g1OutputFrames r res).count (.output (!res)) = 0 := by
  cases res <;>
    simp [g1OutputFrames, List.count_append, g1PrefixFrames_count_output]

/-! ## Canonical caller-supplied capstone -/

def g1OutputRoute (r : G1Request) : List G1Frame :=
  g1PrefixFrames r ++ [.output false]

@[simp] theorem g1OutputRoute_length (r : G1Request) :
    (g1OutputRoute r).length = (g1PrefixFrames r).length + 1 := by
  simp [g1OutputRoute]

/-- No bridge is included: this is the exact caller-supplied dormant entry. -/
def g1OutputStartConfig (r : G1Request) (res : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length 0 (g1_route_lt_tapeLength r 0 (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .outSeek .p0 false false false (g1ResultCtx res)

def g1OutputDoneConfig (r : G1Request) (res : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfigQ (encodeG1 r).length (g1OutputExitHead r)
    (g1OutputExitHead_safe r)
    (g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits))
    (g1OutputDoneState res)

@[simp] theorem g1OutputDoneConfig_state (r : G1Request) (res : Bool) :
    (g1OutputDoneConfig r res).state.snd = g1OutputDoneState res := rfl

@[simp] theorem g1OutputDoneConfig_head (r : G1Request) (res : Bool) :
    ((g1OutputDoneConfig r res).head : Nat) = g1OutputExitHead r := rfl

@[simp] theorem g1OutputDoneConfig_tape (r : G1Request) (res : Bool) :
    (g1OutputDoneConfig r res).tape =
      g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) := rfl

/-- Four steps per prefix/target frame, one turn, and four writer steps. -/
def g1OutputKernelSteps (r : G1Request) : Nat :=
  4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 9

theorem g1OutputKernelSteps_eq (r : G1Request) :
    g1OutputKernelSteps r = 4 * ((g1PrefixFrames r).length + 1) + 5 := by
  rw [g1OutputKernelSteps, g1PrefixFrames_length]
  omega

private theorem g1OutputAlignedQ_congr (n h h' : Nat)
    (hh : h < G1M.tapeLength n) (hh' : h' < G1M.tapeLength n) (heq : h = h')
    (tape : Fin (G1M.tapeLength n) → Bool) (q : G1State) :
    g1AlignedConfigQ n h hh tape q = g1AlignedConfigQ n h' hh' tape q := by
  subst heq
  rfl

theorem g1CS_output_scan_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (4 * ((g1PrefixFrames r).length + 1)) =
      g1AlignedConfig (encodeG1 r).length (g1OutputBase r + 4)
        (g1OutputBase_safe r)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .outTurn .p0 false false false (g1ResultCtx res) := by
  have h := g1CS_out_scan (encodeG1 r).length [] (g1PrefixFrames r)
    [G1Frame.finish, G1Frame.blank] (g1ResultCtx res)
    (g1PrefixFrames_outSkip r) (by
      have hsafe := g1OutputBase_safe r
      rw [g1OutputBase] at hsafe
      simpa using hsafe)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, Nat.mul_zero] at h
  rw [← g1OutputFrames_split r false, g1OutputTape_false] at h
  simpa [g1OutputStartConfig, g1OutputBase] using h

theorem g1CS_output_turn_write_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length (g1OutputBase r + 4)
          (g1OutputBase_safe r)
          (G1M.initialConfig (g1Point (encodeG1 r))).tape
          .outTurn .p0 false false false (g1ResultCtx res)) 5 =
      g1OutputDoneConfig r res := by
  have hturn := g1CS_out_turn (encodeG1 r).length (g1OutputBase r + 4)
    (g1OutputBase_safe r) (by omega)
    (G1M.initialConfig (g1Point (encodeG1 r))).tape (g1ResultCtx res)
  simp only [g1ResultCtx_vB] at hturn
  have hwrite := g1CS_out_write (encodeG1 r).length (g1PrefixFrames r)
    [G1Frame.finish, G1Frame.blank] res (g1ResultCtx res)
    (by rw [g1PrefixFrames_length]; omega)
    (by rw [← g1OutputBase]; exact g1OutputBase_safe r)
  rw [← g1OutputFrames_split r false, g1OutputTape_false] at hwrite
  rw [show (5 : Nat) = 1 + 4 by omega, runConfig_add, hturn]
  rw [g1OutputAlignedQ_congr (encodeG1 r).length (g1OutputBase r + 4 - 1)
      (4 * (g1PrefixFrames r).length + 3)
      (by have hs := g1OutputBase_safe r; omega)
      (by have hs := g1OutputBase_safe r; rw [g1OutputBase] at hs; omega)
      (by rw [g1OutputBase]; omega)
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      (g1OutWriteState res (g1ResultCtx res)), hwrite,
    g1OutputDoneConfig, ← g1OutputFrames_split r res]
  exact g1OutputAlignedQ_congr (encodeG1 r).length
    (4 * (g1PrefixFrames r).length - 1) (g1OutputExitHead r)
    (by have hs := g1OutputBase_safe r; rw [g1OutputBase] at hs; omega)
    (g1OutputExitHead_safe r)
    (by rw [g1OutputExitHead, g1OutputBase])
    (g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits))
    (g1OutputDoneState res)

/-- Dependency-closed executable capstone from the caller-supplied scan state. -/
theorem g1CS_output_kernel_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (g1OutputKernelSteps r) = g1OutputDoneConfig r res := by
  rw [g1OutputKernelSteps_eq, runConfig_add, g1CS_output_scan_exact,
    g1CS_output_turn_write_exact]

theorem g1CS_output_kernel_tape (r : G1Request) (res : Bool) :
    (TM.runConfig (M := G1M) (g1OutputStartConfig r res)
      (g1OutputKernelSteps r)).tape =
      writeCell (g1OutputPosition r) res
        (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_output_kernel_exact, g1OutputDoneConfig_tape,
    g1OutputTape_eq_writeCell]

theorem g1CS_output_kernel_head (r : G1Request) (res : Bool) :
    ((TM.runConfig (M := G1M) (g1OutputStartConfig r res)
      (g1OutputKernelSteps r)).head : Nat) = g1OutputExitHead r := by
  rw [g1CS_output_kernel_exact]
  rfl

theorem g1CS_output_kernel_state (r : G1Request) (res : Bool) :
    (TM.runConfig (M := G1M) (g1OutputStartConfig r res)
      (g1OutputKernelSteps r)).state.snd = g1OutputDoneState res := by
  rw [g1CS_output_kernel_exact]
  rfl

theorem g1OutputDone_false_ne_reject :
    g1OutputDoneState false ≠ g1RejectState := by decide

theorem g1OutputDone_false_ne_oob (ctx : G1Ctx) :
    g1OutputDoneState false ≠ g1OOBState ctx := by
  intro h
  exact G1Mode.noConfusion (congrArg G1State.mode h)

theorem g1OutputDone_ne_combine (res : Bool) (ctx : G1Ctx) :
    g1OutputDoneState res ≠ g1CombineState ctx := by
  cases res <;> intro h <;>
    exact G1Mode.noConfusion (congrArg G1State.mode h)

theorem g1CS_output_kernel_stable (r : G1Request) (res : Bool) (k : Nat) :
    TM.runConfig (M := G1M) (g1OutputStartConfig r res)
        (g1OutputKernelSteps r + k) = g1OutputDoneConfig r res := by
  rw [runConfig_add, g1CS_output_kernel_exact, g1OutputDoneConfig]
  exact g1CS_outputDone_stable _ _ _ _ res k

/-! ## Literal caller-supplied false/true probes -/

namespace G1OutputKernelProbes

def req : G1Request := ⟨.const, 0, 0, []⟩

theorem literal_frames_false :
    g1OutputFrames req false =
      [.bof, .tag, .tag, .argSep, .argSep, .separator,
        .output false, .finish, .blank] := by decide

theorem literal_frames_true :
    g1OutputFrames req true =
      [.bof, .tag, .tag, .argSep, .argSep, .separator,
        .output true, .finish, .blank] := by decide

theorem literal_steps : g1OutputKernelSteps req = 33 := by decide

theorem literal_false_run :
    TM.runConfig (M := G1M) (g1OutputStartConfig req false) 33 =
      g1OutputDoneConfig req false := by
  rw [← literal_steps]
  exact g1CS_output_kernel_exact req false

theorem literal_true_run :
    TM.runConfig (M := G1M) (g1OutputStartConfig req true) 33 =
      g1OutputDoneConfig req true := by
  rw [← literal_steps]
  exact g1CS_output_kernel_exact req true

theorem literal_false_tape :
    (TM.runConfig (M := G1M) (g1OutputStartConfig req false) 33).tape =
      g1ListTape
        ([G1Frame.bof, .tag, .tag, .argSep, .argSep, .separator,
          .output false, .finish, .blank].flatMap G1Frame.bits) := by
  rw [literal_false_run, g1OutputDoneConfig_tape, literal_frames_false]

theorem literal_true_tape :
    (TM.runConfig (M := G1M) (g1OutputStartConfig req true) 33).tape =
      g1ListTape
        ([G1Frame.bof, .tag, .tag, .argSep, .argSep, .separator,
          .output true, .finish, .blank].flatMap G1Frame.bits) := by
  rw [literal_true_run, g1OutputDoneConfig_tape, literal_frames_true]

end G1OutputKernelProbes

end Pnp3.Internal.PsubsetPpoly.TM
