import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernel
import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples

/-!
# G1 operand-2 repair kernel: all-literal probes

**Progress classification: Infrastructure.**  Four exact `G1M` runs on the
sixteen-frame word for `⟨and, 0, 2, [false, true, true]⟩` with both operand-2
units consumed: one cycle (`13`, head `35 ↦ 31`), seek+repair (`37`, `59 ↦ 31`),
the two-unit run (`26`, `35 ↦ 27`) and the whole pass (`79`, `59 ↦ 0`).
The endpoint word is exactly the canonical encoding plus `blank`; literal
counts and cell `32` witness the real `spent ↦ index` changes.  Every
configuration is caller-supplied: no probe starts from `G1M.initialConfig`, no
live route reaches the repair modes, and `readAStart` remains idle.  The
request-specific driver is Repair-2.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1RepairKernelExamples

open G1InstallScanExamples (g1WalkExample g1WalkExample_length)

/-- The probe tape length: the canonical word of `⟨and, 0, 2, [false, true,
true]⟩`, `60` physical cells, so the sixteenth (blank) frame lives on the
tape the machine supplies past the input. -/
def probeLen : Nat := 60

theorem probeLen_eq : probeLen = (encodeG1 g1WalkExample).length :=
  g1WalkExample_length.symm

/-- Every cell the probes touch is far inside the tape. -/
theorem probe_safe {k : Nat} (hk : k ≤ 64) : k < G1M.tapeLength probeLen :=
  g1_lt_tapeLength (by simp only [probeLen]; omega)

/-- The word **before** the sweep: both operand-2 units consumed. -/
def probeSpentFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
    .data false, .data true, .data true, .output false, .finish, .blank]

/-- The word after **one** cycle: the rightmost unit repaired, the left one
still consumed. -/
def probeHalfFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .index, .separator,
    .data false, .data true, .data true, .output false, .finish, .blank]

/-- The word **after** the sweep. -/
def probeIndexFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .index, .separator,
    .data false, .data true, .data true, .output false, .finish, .blank]

/-- **Nonvacuity, at the word level.**  The repaired word is literally the
canonical encoded word of a real request plus the trailing blank frame, the
three words are pairwise different, and the consumed units really disappear:
`2 ↦ 1 ↦ 0`, with the operand-2 index field restored to its two `index`
frames. -/
theorem probeIndex_eq_encoded :
    probeIndexFrames = encodeG1Frames g1WalkExample ++ [G1Frame.blank] := rfl

theorem probe_words_distinct :
    probeSpentFrames ≠ probeHalfFrames ∧
      probeHalfFrames ≠ probeIndexFrames ∧
      probeSpentFrames ≠ probeIndexFrames := by decide

theorem probe_counts :
    probeSpentFrames.count G1Frame.spent = 2 ∧
      probeHalfFrames.count G1Frame.spent = 1 ∧
      probeIndexFrames.count G1Frame.spent = 0 ∧
      probeSpentFrames.count G1Frame.index = 0 ∧
      probeIndexFrames.count G1Frame.index = 2 ∧
      probeSpentFrames.length = 16 ∧
      probeIndexFrames.length = 16 := by decide

/-- **Nonvacuity, at the cell level.**  Physical cell `32` — the first cell of
the eighth frame — flips: `spent` spells `[true, true, false, false]` there and
`index` spells `[false, false, true, true]`, so the two tapes are genuinely
different functions and the `79` steps below cannot be a no-op. -/
theorem probe_cell32 :
    g1ListTape (n := probeLen) (probeSpentFrames.flatMap G1Frame.bits)
        ⟨32, probe_safe (by omega)⟩ = true ∧
      g1ListTape (n := probeLen) (probeIndexFrames.flatMap G1Frame.bits)
        ⟨32, probe_safe (by omega)⟩ = false :=
  ⟨rfl, rfl⟩

/- `[bof] ++ left ++ spent^2 ++ mid ++ tail`: six frames between the anchor and the
run, two consumed units, six frames the scan crosses on the way in, and one
frame — the trailing blank — that sits to the **right** of where the scan
starts and is therefore never read at all. -/

def probeLeft : List G1Frame := [.tag, .tag, .tag, .tag, .argSep, .argSep]

def probeMid : List G1Frame :=
  [.separator, .data false, .data true, .data true, .output false, .finish]

def probeTail : List G1Frame := [.blank]

theorem probeSpent_split :
    probeSpentFrames =
      [G1Frame.bof] ++ probeLeft ++ List.replicate 2 G1Frame.spent ++
        probeMid ++ probeTail := rfl

theorem probeIndex_split :
    probeIndexFrames =
      [G1Frame.bof] ++ probeLeft ++ List.replicate 2 G1Frame.index ++
        probeMid ++ probeTail := rfl

theorem probeLeft_skip : ∀ f ∈ probeLeft, G1RepairSkip f := by decide

theorem probeMid_skip : ∀ f ∈ probeMid, G1RepairSkip f := by decide

/-- `4 * 6 + 13 * 2 + 4 * 6 + 5`: six frames skipped on the way in, two units
repaired, six frames skipped on the way out, the anchor read and the dispatch. -/
theorem probe_passSteps : g1RepairPassSteps 6 2 6 = 79 := rfl

theorem probe_passSteps_split :
    g1RepairPassSteps 6 2 6 = 4 * 6 + 13 * 2 + 4 * 6 + 5 := rfl

/-- The eight frames left of the repaired unit: the anchor, the tag run, both
`argSep`s and the still-consumed first unit. -/
def probeCyclePre : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent]

def probeCycleSuffix : List G1Frame :=
  [.separator, .data false, .data true, .data true, .output false, .finish,
    .blank]

theorem probeCycle_split_spent :
    probeSpentFrames = probeCyclePre ++ G1Frame.spent :: probeCycleSuffix := rfl

theorem probeCycle_split_half :
    probeHalfFrames = probeCyclePre ++ G1Frame.index :: probeCycleSuffix := rfl

/-- **Exactly `13` genuine steps repair the rightmost consumed unit.**  The head
goes from cell `35` — the last cell of that unit — to cell `31`, the last cell
of the unit before it, the control is back in the reverse-read entry shape, and
the only cells that change are the four of frame `8`. -/
theorem cycle_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 13 =
      g1AlignedConfig probeLen 31 (probe_safe (by omega))
        (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_cycle_onList probeLen probeCyclePre probeCycleSuffix
    (g1Ctx0.withVB true) (by decide) (probe_safe (by decide))
  simpa only [probeCycle_split_spent, probeCycle_split_half,
    show (probeCyclePre.length : Nat) = 8 from rfl] using h

/-- The cycle preserves the whole carried context, latch included. -/
theorem cycle_probe_ctx :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        13).state.snd.ctx = g1Ctx0.withVB true := by
  rw [cycle_probe]; rfl

/-- The seven frames left of the run: the anchor, the tag run and both
`argSep`s. -/
def probeRunPre : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep]

theorem probeRun_split_spent :
    probeSpentFrames =
      probeRunPre ++ List.replicate 2 G1Frame.spent ++ (probeMid ++ probeTail) :=
  rfl

theorem probeRun_split_index :
    probeIndexFrames =
      probeRunPre ++ List.replicate 2 G1Frame.index ++ (probeMid ++ probeTail) :=
  rfl

/-- **Exactly `26 = 13 * 2` genuine steps repair both consumed units.**  The
head goes from cell `35` to cell `27`, the last cell of the second `argSep`, and
the operand-2 field is back to `index index`. -/
theorem run_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 26 =
      g1AlignedConfig probeLen 27 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_spent_run probeLen probeRunPre (probeMid ++ probeTail) 2
    (g1Ctx0.withVB true) (by decide) (probe_safe (by decide))
  simpa only [probeRun_split_spent, probeRun_split_index,
    show (probeRunPre.length : Nat) = 7 from rfl] using h

theorem run_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        26).tape = g1ListTape (probeIndexFrames.flatMap G1Frame.bits) := by
  rw [run_probe]; rfl

theorem seek_repair_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 37 =
      g1AlignedConfig probeLen 31 (probe_safe (by omega))
        (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_seek_and_repair probeLen
    (probeRunPre ++ [G1Frame.spent]) probeMid probeTail (g1Ctx0.withVB true)
    (by decide) probeMid_skip (probe_safe (by decide))
  simpa [probeSpentFrames, probeHalfFrames, probeRunPre, probeMid, probeTail] using h

/-- **Exactly `79` genuine steps run the whole sweep.**  From cell `59` — the
last cell of the `finish` frame, where a caller hands the sweep over — the
machine crosses `mid` right to left, repairs both consumed units, crosses the
tag run and both `argSep`s, reads the anchor and dispatches: head `0`,
control `readAStart`, tape exactly the canonical word plus the blank frame, and
the latched `vB = true` still in place. -/
theorem pass_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 79 =
      g1AlignedConfig probeLen 0 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .readAStart .p0 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_pass_exact probeLen 2 probeLeft probeMid probeTail
    (g1Ctx0.withVB true) probeLeft_skip probeMid_skip (probe_safe (by decide))
  simpa only [probeSpent_split, probeIndex_split, probe_passSteps,
    show (probeLeft.length : Nat) = 6 from rfl,
    show (probeMid.length : Nat) = 6 from rfl] using h

theorem pass_probe_head :
    ((TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).head : Nat) = 0 := by
  rw [pass_probe]; rfl

/-- The endpoint tape is bit-for-bit the canonical word of the real request
plus the trailing blank frame. -/
theorem pass_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).tape =
      g1ListTape
        ((encodeG1Frames g1WalkExample ++ [G1Frame.blank]).flatMap
          G1Frame.bits) := by
  rw [pass_probe, ← probeIndex_eq_encoded]; rfl

/-- The sweep never touches the carried context: `vB` still holds what the
caller latched. -/
theorem pass_probe_ctx :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).state.snd.ctx = g1Ctx0.withVB true ∧
      (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).state.snd.ctx.vB = true := by
  constructor <;> · rw [pass_probe]; rfl

/- `readAStart` is **not** activated by this slice: the repaired endpoint holds its
state, head and tape for the whole remaining budget.  Operand 1 is not read. -/

theorem pass_probe_idle (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) (79 + k) =
      g1AlignedConfig probeLen 0 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .readAStart .p0 false false false (g1Ctx0.withVB true) := by
  rw [runConfig_add, pass_probe]
  exact g1CS_runConfig_readA_idle _ _ _ _ _ k

end G1RepairKernelExamples

end Pnp3.Internal.PsubsetPpoly.TM
