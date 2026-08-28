import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernel
import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples

/-!
# G1 operand-2 repair kernel: all-literal probes

**Progress classification: Infrastructure.**  Four exact `G1M` runs on the
sixteen-frame word for `⟨and, 0, 2, [false, true, true]⟩` with both operand-2
units consumed: one cycle (`13`, head `35 ↦ 31`), seek+repair (`37`,
`59 ↦ 31`), the two-unit run (`26`, `35 ↦ 27`) and the whole pass (`79`,
`59 ↦ 0`).  The endpoint word is exactly the canonical encoding plus `blank`;
literal counts and cell `32` witness the real `spent ↦ index` changes.  Every
configuration is caller-supplied: no probe starts from `G1M.initialConfig`, no
live route reaches the repair modes, and `readAStart` remains idle.  The
request-specific driver is Repair-2.

**These probes respect the narrowed crossable-frame predicate.**  `G1RepairSkip`
holds for exactly the canonical interior frame kinds; `blank`, `bof`, `cursor`
and `spent` are **not** crossable, and a `blank` or a leftover `cursor` under
the scan sends it to the `reject` sink instead.  The two lists this module hands
to the kernel — `probeLeft` (the tag run and both `argSep`s) and `probeMid` (the
`separator`, the data region, `output` and `finish`) — are therefore pinned
against the narrowed predicate directly, and `probe_scan_lists_clean` records
that neither contains a `blank` or a `cursor`.  The sixteenth frame, the
trailing `blank` of `probeTail`, is **not** crossable and is never scanned: it
sits entirely to the right of the sweep's entry cell `59`
(`probeTail_beyond_entry`), so it is passed as the kernel's unconstrained
`tail`, never read, and preserved bit-for-bit.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1RepairKernelExamples

open G1InstallScanExamples (g1WalkExample g1WalkExample_length)

/-- The encoded-input length parameter is `60`; physical configurations use
`G1M.tapeLength probeInputLen`, not a 60-cell tape. -/
def probeInputLen : Nat := 60

theorem probeInputLen_eq : probeInputLen = (encodeG1 g1WalkExample).length :=
  g1WalkExample_length.symm

/-- Every cell the probes touch is far inside the tape. -/
theorem probe_safe {k : Nat} (hk : k ≤ 64) : k < G1M.tapeLength probeInputLen :=
  g1_lt_tapeLength (by simp only [probeInputLen]; omega)

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

/-- The literal word occupies `16 * 4 = 64` cells, all strictly inside the
machine's derived physical tape capacity. -/
theorem probe_word_cells :
    (probeSpentFrames.flatMap G1Frame.bits).length = 64 ∧
      64 < G1M.tapeLength probeInputLen :=
  ⟨by decide, probe_safe (by omega)⟩

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
frame `8`, the rightmost operand-2 unit — flips: `spent` spells
`[true, true, false, false]` there and
`index` spells `[false, false, true, true]`, so the two tapes are genuinely
different functions and the `79` steps below cannot be a no-op. -/
theorem probe_cell32 :
    g1ListTape (n := probeInputLen) (probeSpentFrames.flatMap G1Frame.bits)
        ⟨32, probe_safe (by omega)⟩ = true ∧
      g1ListTape (n := probeInputLen) (probeIndexFrames.flatMap G1Frame.bits)
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

/-- The fifteen frames the sweep reads: the anchor, `left`, the consumed run and
`mid`.  The sixteenth is the tail. -/
def probeScanned : List G1Frame :=
  [G1Frame.bof] ++ probeLeft ++ List.replicate 2 G1Frame.spent ++ probeMid

theorem probeSpent_scanned_tail :
    probeSpentFrames = probeScanned ++ probeTail ∧
      probeScanned.length = 15 ∧ probeTail.length = 1 := ⟨rfl, rfl, rfl⟩

/-- **The narrowed predicate, checked on the lists the sweep actually
crosses.**  `G1RepairSkip` is false for `blank`, `bof`, `cursor` and `spent`,
and both canonical scanned lists still satisfy it — because neither contains a
`blank` or a leftover `cursor`, and neither does the scanned region as a whole.
This is the regression that keeps the probes honest about the rejection
outcome: were a malformed frame to appear in `left` or `mid`,
`probeLeft_skip`/`probeMid_skip` would fail and every pass theorem below would
lose its hypotheses. -/
theorem probe_scan_lists_clean :
    (¬ G1RepairSkip G1Frame.blank ∧ ¬ G1RepairSkip G1Frame.cursor ∧
        ¬ G1RepairSkip G1Frame.bof ∧ ¬ G1RepairSkip G1Frame.spent) ∧
      G1Frame.blank ∉ probeLeft ++ probeMid ∧
      G1Frame.cursor ∉ probeLeft ++ probeMid ∧
      G1Frame.blank ∉ probeScanned ∧ G1Frame.cursor ∉ probeScanned ∧
      (∀ f ∈ probeLeft ++ probeMid, G1RepairSkip f) := by decide

/-- **The trailing `blank` is outside the scan.**  It is not a crossable frame,
it does not occur inside the scanned region, and every one of its four physical
cells (`60 … 63`) lies strictly to the right of the sweep's entry cell
`59 = 4 * 15 - 1`.  That is why it may be — and is — handed to the kernel as the
unconstrained `tail` of `g1CS_repair_pass_exact`: the pass hypotheses never
mention it, the scan never reads it, and the endpoint tape reproduces it
bit-for-bit. -/
theorem probeTail_beyond_entry :
    probeTail = [G1Frame.blank] ∧ ¬ G1RepairSkip G1Frame.blank ∧
      G1Frame.blank ∉ probeScanned ∧
      4 * probeScanned.length - 1 = 59 ∧
      (∀ i < 4 * probeTail.length, 59 < 4 * probeScanned.length + i) := by
  decide

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
        (g1AlignedConfig probeInputLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 13 =
      g1AlignedConfig probeInputLen 31 (probe_safe (by omega))
        (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_cycle_onList probeInputLen probeCyclePre probeCycleSuffix
    (g1Ctx0.withVB true) (by decide) (probe_safe (by decide))
  simpa only [probeCycle_split_spent, probeCycle_split_half,
    show (probeCyclePre.length : Nat) = 8 from rfl] using h

/-- The cycle preserves the whole carried context, latch included. -/
theorem cycle_probe_ctx :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 35 (probe_safe (by omega))
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
        (g1AlignedConfig probeInputLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 26 =
      g1AlignedConfig probeInputLen 27 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_spent_run probeInputLen probeRunPre (probeMid ++ probeTail) 2
    (g1Ctx0.withVB true) (by decide) (probe_safe (by decide))
  simpa only [probeRun_split_spent, probeRun_split_index,
    show (probeRunPre.length : Nat) = 7 from rfl] using h

theorem run_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        26).tape = g1ListTape (probeIndexFrames.flatMap G1Frame.bits) := by
  rw [run_probe]; rfl

/-- **Exactly `37 = 4 * 6 + 13` genuine steps seek across `mid` and repair the
first unit they meet.**  From cell `59` — the last cell of the `finish` frame —
the scan crosses the six crossable frames of `probeMid` right to left, rewrites
the rightmost consumed unit and lands on cell `31`.  The trailing `blank` sits
at cells `60 … 63` and is never read (`probeTail_beyond_entry`). -/
theorem seek_repair_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 37 =
      g1AlignedConfig probeInputLen 31 (probe_safe (by omega))
        (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_seek_and_repair probeInputLen
    (probeRunPre ++ [G1Frame.spent]) probeMid probeTail (g1Ctx0.withVB true)
    (by decide) probeMid_skip (probe_safe (by decide))
  simpa [probeSpentFrames, probeHalfFrames, probeRunPre, probeMid, probeTail] using h

/-- The seek+repair endpoint tape is the **half**-repaired word: the left unit
is still consumed. -/
theorem seek_repair_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        37).tape = g1ListTape (probeHalfFrames.flatMap G1Frame.bits) := by
  rw [seek_repair_probe]; rfl

/-- **Exactly `79` genuine steps run the whole sweep.**  From cell `59` — the
last cell of the `finish` frame, where a caller hands the sweep over — the
machine crosses `mid` right to left, repairs both consumed units, crosses the
tag run and both `argSep`s, reads the anchor and dispatches: head `0`,
control `readAStart`, tape exactly the canonical word plus the blank frame, and
the latched `vB = true` still in place. -/
theorem pass_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 79 =
      g1AlignedConfig probeInputLen 0 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .readAStart .p0 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_repair_pass_exact probeInputLen 2 probeLeft probeMid probeTail
    (g1Ctx0.withVB true) probeLeft_skip probeMid_skip (probe_safe (by decide))
  simpa only [probeSpent_split, probeIndex_split, probe_passSteps,
    show (probeLeft.length : Nat) = 6 from rfl,
    show (probeMid.length : Nat) = 6 from rfl] using h

theorem pass_probe_head :
    ((TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).head : Nat) = 0 := by
  rw [pass_probe]; rfl

/-- The endpoint tape is bit-for-bit the canonical word of the real request
plus the trailing blank frame. -/
theorem pass_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
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
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).state.snd.ctx = g1Ctx0.withVB true ∧
      (TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).state.snd.ctx.vB = true := by
  constructor <;> · rw [pass_probe]; rfl

/- `readAStart` is **not** activated by this slice: the repaired endpoint holds its
state, head and tape for the whole remaining budget.  Operand 1 is not read. -/

theorem pass_probe_idle (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeInputLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) (79 + k) =
      g1AlignedConfig probeInputLen 0 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .readAStart .p0 false false false (g1Ctx0.withVB true) := by
  rw [runConfig_add, pass_probe]
  exact g1CS_runConfig_readA_idle _ _ _ _ _ k

end G1RepairKernelExamples

end Pnp3.Internal.PsubsetPpoly.TM
