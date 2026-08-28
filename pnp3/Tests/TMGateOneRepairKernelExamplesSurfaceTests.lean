import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernelExamples

/-!
# G1 operand-2 repair kernel, all-literal probes: surface tests

Theorem-style exact wrappers for **every** public statement of
`GateOneRepairKernelExamples`, the Repair-1b probe module: the literal
sixteen-frame word for `⟨and, 0, 2, [false, true, true]⟩` with both operand-2
units consumed, its three splits, the encoded repaired word, the pairwise
differences, the literal counts, the flipped cell `32`, the head-safety bound,
the closed pass cost and its split, and the four exact `G1M` runs — the `13`-step
cycle (`35 ↦ 31`), the `37`-step seek+repair (`59 ↦ 31`), the `26`-step two-unit
run (`35 ↦ 27`) and the `79`-step whole pass (`59 ↦ 0`) with its head, tape,
context and idle projections.

**The narrowed crossable-frame predicate is pinned here too.**
`check_probe_scan_lists_clean` restates that `blank`, `cursor`, `bof` and
`spent` are **not** `G1RepairSkip` and that the two canonical scanned lists
`probeLeft`/`probeMid` contain neither a `blank` nor a `cursor`, so the skip
hypotheses the pass consumes are genuinely discharged rather than assumed away.
`check_probeTail_beyond_entry` restates that the sixteenth frame — the trailing
`blank` — is not crossable, does not occur in the scanned region, and lies
entirely to the right of the sweep's entry cell `59`: it is the kernel's
unconstrained `tail`, never read and preserved bit-for-bit.

**Every configuration is caller-supplied**: every run below starts from an
explicit `g1AlignedConfig`, and nothing here mentions `G1M.initialConfig`.

**Absent from this surface**: the request-specific repair driver, any
composition of the operand-2 read with a repair, any pass-A read, combine step,
output write, and any `TM.accepts`, verdict, full-clock, gate-semantics,
acceptance-gate, multi-gate, specification-bridge or padded-tape surface.  It
pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneRepairKernelExamplesSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1RepairKernelExamples

/-- The probe tape length is the canonical word's own length, `60`. -/
theorem check_probeLen_eq :
    probeLen = 60 ∧
      probeLen = (encodeG1 G1InstallScanExamples.g1WalkExample).length :=
  ⟨rfl, probeLen_eq⟩

/-- Every cell the probes touch is far inside the tape. -/
theorem check_probe_safe {k : Nat} (hk : k ≤ 64) : k < G1M.tapeLength probeLen :=
  probe_safe hk

/-- The repaired word is literally the canonical encoding of a real request plus
the trailing blank frame. -/
theorem check_probeIndex_eq_encoded :
    probeIndexFrames =
      encodeG1Frames G1InstallScanExamples.g1WalkExample ++ [G1Frame.blank] :=
  probeIndex_eq_encoded

/-- The three literal words are pairwise different. -/
theorem check_probe_words_distinct :
    probeSpentFrames ≠ probeHalfFrames ∧
      probeHalfFrames ≠ probeIndexFrames ∧
      probeSpentFrames ≠ probeIndexFrames :=
  probe_words_distinct

/-- The consumed units really disappear, `2 ↦ 1 ↦ 0`, and the operand-2 index
field is restored to its two `index` frames. -/
theorem check_probe_counts :
    probeSpentFrames.count G1Frame.spent = 2 ∧
      probeHalfFrames.count G1Frame.spent = 1 ∧
      probeIndexFrames.count G1Frame.spent = 0 ∧
      probeSpentFrames.count G1Frame.index = 0 ∧
      probeIndexFrames.count G1Frame.index = 2 ∧
      probeSpentFrames.length = 16 ∧
      probeIndexFrames.length = 16 :=
  probe_counts

/-- Physical cell `32` genuinely flips, so the two tapes are different
functions and the `79` steps cannot be a no-op. -/
theorem check_probe_cell32 :
    g1ListTape (n := probeLen) (probeSpentFrames.flatMap G1Frame.bits)
        ⟨32, probe_safe (by omega)⟩ = true ∧
      g1ListTape (n := probeLen) (probeIndexFrames.flatMap G1Frame.bits)
        ⟨32, probe_safe (by omega)⟩ = false :=
  probe_cell32

/-- Both words in the `[bof] ++ left ++ unit^2 ++ mid ++ tail` shape the pass
capstone consumes. -/
theorem check_probe_splits :
    probeSpentFrames =
        [G1Frame.bof] ++ probeLeft ++ List.replicate 2 G1Frame.spent ++
          probeMid ++ probeTail ∧
      probeIndexFrames =
        [G1Frame.bof] ++ probeLeft ++ List.replicate 2 G1Frame.index ++
          probeMid ++ probeTail :=
  ⟨probeSpent_split, probeIndex_split⟩

/-- Both canonical scanned lists satisfy the **narrowed** `G1RepairSkip`. -/
theorem check_probe_scan_lists_skip :
    (∀ f ∈ probeLeft, G1RepairSkip f) ∧ (∀ f ∈ probeMid, G1RepairSkip f) :=
  ⟨probeLeft_skip, probeMid_skip⟩

/-- Fifteen of the sixteen frames are scanned; the sixteenth is the tail. -/
theorem check_probeSpent_scanned_tail :
    probeSpentFrames = probeScanned ++ probeTail ∧
      probeScanned.length = 15 ∧ probeTail.length = 1 :=
  probeSpent_scanned_tail

/-- **The rejection outcome is respected, not dodged.**  `blank`, `cursor`,
`bof` and `spent` are not crossable, and neither scanned list — nor the scanned
region as a whole — contains a `blank` or a leftover `cursor`, so the pass's
skip hypotheses are genuinely discharged. -/
theorem check_probe_scan_lists_clean :
    (¬ G1RepairSkip G1Frame.blank ∧ ¬ G1RepairSkip G1Frame.cursor ∧
        ¬ G1RepairSkip G1Frame.bof ∧ ¬ G1RepairSkip G1Frame.spent) ∧
      G1Frame.blank ∉ probeLeft ++ probeMid ∧
      G1Frame.cursor ∉ probeLeft ++ probeMid ∧
      G1Frame.blank ∉ probeScanned ∧ G1Frame.cursor ∉ probeScanned ∧
      (∀ f ∈ probeLeft ++ probeMid, G1RepairSkip f) :=
  probe_scan_lists_clean

/-- **The trailing `blank` is outside the scan**: not crossable, absent from the
scanned region, and every one of its cells lies strictly right of the entry cell
`59 = 4 * 15 - 1`. -/
theorem check_probeTail_beyond_entry :
    probeTail = [G1Frame.blank] ∧ ¬ G1RepairSkip G1Frame.blank ∧
      G1Frame.blank ∉ probeScanned ∧
      4 * probeScanned.length - 1 = 59 ∧
      (∀ i < 4 * probeTail.length, 59 < 4 * probeScanned.length + i) :=
  probeTail_beyond_entry

/-- The closed pass cost at the probe's parameters, and its split. -/
theorem check_probe_passSteps :
    g1RepairPassSteps 6 2 6 = 79 ∧
      g1RepairPassSteps 6 2 6 = 4 * 6 + 13 * 2 + 4 * 6 + 5 :=
  ⟨probe_passSteps, probe_passSteps_split⟩

/-- The one-cycle split of the `spent` and half-repaired words. -/
theorem check_probeCycle_splits :
    probeSpentFrames = probeCyclePre ++ G1Frame.spent :: probeCycleSuffix ∧
      probeHalfFrames = probeCyclePre ++ G1Frame.index :: probeCycleSuffix :=
  ⟨probeCycle_split_spent, probeCycle_split_half⟩

/-- The two-unit-run split of the `spent` and repaired words. -/
theorem check_probeRun_splits :
    probeSpentFrames =
        probeRunPre ++ List.replicate 2 G1Frame.spent ++
          (probeMid ++ probeTail) ∧
      probeIndexFrames =
        probeRunPre ++ List.replicate 2 G1Frame.index ++
          (probeMid ++ probeTail) :=
  ⟨probeRun_split_spent, probeRun_split_index⟩

/-- **`13` genuine steps repair the rightmost consumed unit**, head `35 ↦ 31`. -/
theorem check_cycle_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 13 =
      g1AlignedConfig probeLen 31 (probe_safe (by omega))
        (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) :=
  cycle_probe

/-- The cycle preserves the whole carried context, latch included. -/
theorem check_cycle_probe_ctx :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        13).state.snd.ctx = g1Ctx0.withVB true :=
  cycle_probe_ctx

/-- **`37 = 4 * 6 + 13` genuine steps seek across `mid` and repair the first
unit**, head `59 ↦ 31`. -/
theorem check_seek_repair_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 37 =
      g1AlignedConfig probeLen 31 (probe_safe (by omega))
        (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) :=
  seek_repair_probe

/-- Its endpoint tape is the **half**-repaired word: the left unit is still
consumed. -/
theorem check_seek_repair_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        37).tape = g1ListTape (probeHalfFrames.flatMap G1Frame.bits) :=
  seek_repair_probe_tape

/-- **`26 = 13 * 2` genuine steps repair both consumed units**, head
`35 ↦ 27`. -/
theorem check_run_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 26 =
      g1AlignedConfig probeLen 27 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false (g1Ctx0.withVB true) :=
  run_probe

/-- Its endpoint tape is the fully repaired word. -/
theorem check_run_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 35 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        26).tape = g1ListTape (probeIndexFrames.flatMap G1Frame.bits) :=
  run_probe_tape

/-- **`79` genuine steps run the whole sweep**: head `59 ↦ 0`, control
`readAStart`, tape exactly the repaired word, carried context untouched. -/
theorem check_pass_probe :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 79 =
      g1AlignedConfig probeLen 0 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .readAStart .p0 false false false (g1Ctx0.withVB true) :=
  pass_probe

/-- The endpoint head is `0`. -/
theorem check_pass_probe_head :
    ((TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).head : Nat) = 0 := by
  have h := pass_probe_head
  rw [pass_probe] at h ⊢
  exact h

/-- The endpoint tape is bit-for-bit the canonical encoded word of a real
request plus the trailing blank frame: no consumed unit survives, and the
never-read tail is reproduced exactly. -/
theorem check_pass_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).tape =
      g1ListTape
        ((encodeG1Frames G1InstallScanExamples.g1WalkExample ++
          [G1Frame.blank]).flatMap G1Frame.bits) :=
  pass_probe_tape

/-- The carried context comes out untouched, latch included. -/
theorem check_pass_probe_ctx :
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
  have h := pass_probe_ctx
  rw [pass_probe] at h ⊢
  exact h

/-- The endpoint is a **handoff**: it holds for the whole remaining budget, so
nothing in this slice continues from the repaired configuration and operand 1 is
never read. -/
theorem check_pass_probe_idle (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) (79 + k) =
      g1AlignedConfig probeLen 0 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .readAStart .p0 false false false (g1Ctx0.withVB true) :=
  pass_probe_idle k

end Pnp3.Tests.TMGateOneRepairKernelExamplesSurface
