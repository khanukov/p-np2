import Complexity.TMVerifier.TuringToolkit.GateOneRepairExamples

/-!
# G1 repair sweep, all-literal repaired reads: surface tests

Theorem-style exact wrappers for **every** public statement of
`GateOneRepairExamples`, the Repair-2b probe module: the literal zero-index
request `⟨and, 0, 0, [true]⟩`, the three head-safety bounds, the three endpoint
words and their `spent`/`cursor`/`index` counts, the three-way length
distinction, the closed sweep cost at `s = 0, 1, 2` with its split, and the
three exact `G1M` runs **from the real `G1M.initialConfig`** — `172` steps at
`arg2 = 0`, `294` at `arg2 = 1`, `400` at `arg2 = 2` — with their head, state,
`vB`, endpoint-word, initial-tape, cell-level, clock and idle projections, plus
both arms of the common capstone on literals.

**Three lengths, kept apart.**  `check_probe_extents` restates the encoded
input length (`44`, `52`, `60`), explicit validation frame-word extent
(`48`, `56`, `64`, including the all-false trailing `blank`) and the
physical capacity `G1M.tapeLength (encodeG1 r).length` (literally `1037357` for
the zero probe) are three different numbers.  Nothing here identifies the
physical tape length with the input length.

**Nonvacuity is pinned, not assumed.**  `check_zero_repaired_tape` restates no
net tape change at `arg2 = 0`; `check_one_repaired_cell28` and
`check_two_repaired_cell32` restate that the two positive branches genuinely
flip a physical cell between the read's terminal tape and the repaired endpoint;
`check_common_branch_literals` restates that the common capstone's branch is
real — at the zero-index literal the other arm would be `204`, not `172`.

**Absent from this surface**: any pass-A read, combine step, output write, and
any `TM.accepts`, verdict, full-clock, gate-semantics, acceptance-gate,
multi-gate, specification-bridge, out-of-range-repair, non-canonical-word or
padded-tape surface.  It pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneRepairExamplesSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1RepairExamples
open Pnp3.Internal.PsubsetPpoly.TM.G1InstallScanExamples (g1WalkExample)
open Pnp3.Internal.PsubsetPpoly.TM.G1WalkDriverExamples (g1BReadExample
  g1BReadFramesFinal)
open Pnp3.Internal.PsubsetPpoly.TM.G1RepairKernelExamples (probeSpentFrames
  probeIndexFrames)

/-! ## The literal requests, their lengths and their head-safety bounds -/

/-- The zero-index probe request, its canonicity and its **encoded input length**. -/
theorem check_g1ZeroExample :
    g1ZeroExample = ⟨.and, 0, 0, [true]⟩ ∧ g1ZeroExample.Canonical ∧
      (encodeG1 g1ZeroExample).length = 44 :=
  ⟨rfl, g1ZeroExample_canonical, g1ZeroExample_length⟩

theorem check_zero_safe {k : Nat} (hk : k ≤ 48) :
    k < G1M.tapeLength (encodeG1 g1ZeroExample).length :=
  zero_safe hk

theorem check_one_safe {k : Nat} (hk : k ≤ 56) :
    k < G1M.tapeLength (encodeG1 g1BReadExample).length :=
  one_safe hk

theorem check_two_safe {k : Nat} (hk : k ≤ 64) :
    k < G1M.tapeLength (encodeG1 g1WalkExample).length :=
  two_safe hk

/-- **Encoded input length, explicit word extent and physical capacity are three
different numbers.**  The explicit word includes the four all-false cells of
the trailing `blank` frame; the capacity is separately derived and far
larger than either. -/
theorem check_probe_extents :
    ((encodeG1 g1ZeroExample).length = 44 ∧
        (g1ZeroFrames.flatMap G1Frame.bits).length = 48 ∧
        48 < G1M.tapeLength (encodeG1 g1ZeroExample).length) ∧
      ((encodeG1 g1BReadExample).length = 52 ∧
        (g1OneRepairedFrames.flatMap G1Frame.bits).length = 56 ∧
        56 < G1M.tapeLength (encodeG1 g1BReadExample).length) ∧
      ((encodeG1 g1WalkExample).length = 60 ∧
        (probeIndexFrames.flatMap G1Frame.bits).length = 64 ∧
        64 < G1M.tapeLength (encodeG1 g1WalkExample).length) ∧
      G1M.tapeLength (encodeG1 g1ZeroExample).length = 1037357 :=
  probe_extents

/-! ## The three endpoint words -/

/-- The two new literal words, each the canonical encoded word of its own
request plus the trailing `blank` frame; the layout the `arg2 = 0` sweep starts
from is already that word; and the `arg2 = 2` words are Repair-1b's, reused
verbatim on both ends. -/
theorem check_endpoint_words :
    g1ZeroFrames =
        [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .separator, .data true,
          .output false, .finish, .blank] ∧
      encodeG1Frames g1ZeroExample ++ [G1Frame.blank] = g1ZeroFrames ∧
      g1OneRepairedFrames =
        [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .separator,
          .data false, .data true, .output false, .finish, .blank] ∧
      encodeG1Frames g1BReadExample ++ [G1Frame.blank] = g1OneRepairedFrames ∧
      g1BSpentFrames g1ZeroExample 0 = g1ZeroFrames ∧
      g1BSpentFrames g1WalkExample g1WalkExample.arg2 = probeSpentFrames ∧
      encodeG1Frames g1WalkExample ++ [G1Frame.blank] = probeIndexFrames :=
  ⟨rfl, zeroFrames_eq, rfl, oneRepairedFrames_eq, zeroFrames_layout,
    twoFrames_eq.1, twoFrames_eq.2⟩

/-- **No `spent` and no `cursor` survives anywhere.**  The zero probe's word has
no operand-2 unit at all; the `arg2 = 1` read's terminal word carries one
`spent` and no `index` while its repaired word carries no `spent` and one
`index`; the `arg2 = 2` counts are Repair-1b's, reused. -/
theorem check_word_counts :
    (g1ZeroFrames.count G1Frame.spent = 0 ∧
        g1ZeroFrames.count G1Frame.cursor = 0 ∧
        g1ZeroFrames.count G1Frame.index = 0 ∧ g1ZeroFrames.length = 12) ∧
      (g1BReadFramesFinal.count G1Frame.spent = 1 ∧
        g1BReadFramesFinal.count G1Frame.index = 0 ∧
        g1OneRepairedFrames.count G1Frame.spent = 0 ∧
        g1OneRepairedFrames.count G1Frame.cursor = 0 ∧
        g1OneRepairedFrames.count G1Frame.index = 1 ∧
        g1OneRepairedFrames.length = 14) ∧
      (probeSpentFrames.count G1Frame.spent = 2 ∧
        probeIndexFrames.count G1Frame.spent = 0 ∧
        probeIndexFrames.count G1Frame.index = 2 ∧
        probeIndexFrames.count G1Frame.cursor = 0) :=
  ⟨zeroFrames_counts, oneRepairedFrames_counts, twoRepaired_counts⟩

/-- **The closed sweep cost on literals.**  `4u + 4a1 + 8a + 9s + 22` at
`s = 0, 1, 2`, and the same three numbers
through the driver's own `1 + g1RepairPassSteps (left) s (mid)` at the real
layout lengths. -/
theorem check_repairSteps :
    (g1RepairSteps g1ZeroExample 0 = 38 ∧
        g1RepairSteps g1BReadExample 1 = 55 ∧
        g1RepairSteps g1WalkExample 2 = 72) ∧
      (g1RepairSteps g1ZeroExample 0 = 1 + g1RepairPassSteps 6 0 2 ∧
        g1RepairSteps g1BReadExample 1 = 1 + g1RepairPassSteps 6 1 3 ∧
        g1RepairSteps g1WalkExample 2 = 1 + g1RepairPassSteps 6 2 4) :=
  ⟨⟨repairSteps_zero, repairSteps_one, repairSteps_two⟩, repairSteps_splits⟩

/-! ## `⟨and, 0, 0, [true]⟩`: the zero-index read and its rewind -/

theorem check_zeroExample_steps :
    g1ReadBSteps g1ZeroExample = 134 ∧ g1ZPassASteps g1ZeroExample = 172 ∧
      g1ZPassASteps g1ZeroExample = 134 + 38 :=
  zeroExample_steps

/-- **`172` genuine steps from the real `G1M.initialConfig` to the canonical
pass-A handoff.** -/
theorem check_zero_repaired :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172 =
      g1ReadAConfig g1ZeroExample true :=
  zero_repaired

/-- Head `0`, control `readAStart`, and the **actual** `vals[0]` latched in
`G1Ctx.vB`. -/
theorem check_zero_repaired_projections :
    ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
          172).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
          172).state.snd = g1ReadAState (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
          172).state.snd.ctx.vB = true :=
  zero_repaired_projections

theorem check_zero_selected :
    g1ZeroExample.vals[g1ZeroExample.arg2]? = some true ∧
      g1ZeroExample.vals = [true] :=
  zero_selected

/-- The endpoint word, and **no net tape change** on the zero branch: the
endpoint tape is literally the initial tape and the rewrite block is empty. -/
theorem check_zero_repaired_tape :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172).tape =
        g1ListTape (g1ZeroFrames.flatMap G1Frame.bits) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172).tape =
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))).tape ∧
      g1BSpentFrames g1ZeroExample 0 = g1ZeroFrames ∧
      g1ZeroFrames.count G1Frame.spent = 0 :=
  ⟨zero_repaired_tape, zero_repaired_no_net_change⟩

/-- The total fits the **unchanged** public clock of this request. -/
theorem check_zero_repaired_clock :
    g1Clock (encodeG1 g1ZeroExample).length = 1037312 ∧
      172 ≤ g1Clock (encodeG1 g1ZeroExample).length :=
  zero_repaired_clock

/-- The endpoint is a **handoff**: it holds for the whole remaining budget, so
operand 1 is never read. -/
theorem check_readA_idle_after_zero (k : Nat) :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) (172 + k) =
      g1ReadAConfig g1ZeroExample true :=
  readA_idle_after_zero k

/-! ## `⟨and, 0, 1, [false, true]⟩`: one consumed unit repaired -/

theorem check_oneExample_steps :
    g1BPassASteps g1BReadExample = 294 ∧
      g1BPassASteps g1BReadExample = 239 + 55 :=
  oneExample_steps

/-- **`294` genuine steps read `vals[1] = true` and repair the tape.** -/
theorem check_one_repaired :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294 =
      g1ReadAConfig g1BReadExample true :=
  one_repaired

theorem check_one_repaired_projections :
    ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          294).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          294).state.snd = g1ReadAState (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          294).state.snd.ctx.vB = true :=
  one_repaired_projections

/-- **The latched bit is the actual selected element, not `vals[0]`:**
`vals[1]` is `true` while `vals[0]` is `false`. -/
theorem check_one_selected :
    g1BReadExample.vals[g1BReadExample.arg2]? = some true ∧
      g1BReadExample.vals[0]? = some false ∧
      g1BReadExample.vals = [false, true] :=
  one_selected

/-- The endpoint word is the canonical encoding plus the trailing `blank`, and
that word is bit-for-bit the initial tape. -/
theorem check_one_repaired_tape :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294).tape =
        g1ListTape (g1OneRepairedFrames.flatMap G1Frame.bits) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294).tape =
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))).tape :=
  one_repaired_tape

/-- **The sweep genuinely writes here**: physical cell `28` flips between the
read's terminal tape and the repaired endpoint. -/
theorem check_one_repaired_cell28 :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 239).tape
        ⟨28, one_safe (by omega)⟩ = true ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294).tape
        ⟨28, one_safe (by omega)⟩ = false :=
  one_repaired_cell28

theorem check_one_repaired_clock :
    294 ≤ g1Clock (encodeG1 g1BReadExample).length :=
  one_repaired_clock

theorem check_readA_idle_after_one (k : Nat) :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) (294 + k) =
      g1ReadAConfig g1BReadExample true :=
  readA_idle_after_one k

/-! ## `⟨and, 0, 2, [false, true, true]⟩`: two consumed units repaired -/

theorem check_twoExample_steps :
    g1BPassASteps g1WalkExample = 400 ∧
      g1BPassASteps g1WalkExample = 328 + 72 :=
  twoExample_steps

/-- **`400` genuine steps read `vals[2] = true` and repair the tape.** -/
theorem check_two_repaired :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400 =
      g1ReadAConfig g1WalkExample true :=
  two_repaired

theorem check_two_repaired_projections :
    ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          400).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          400).state.snd = g1ReadAState (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          400).state.snd.ctx.vB = true :=
  two_repaired_projections

theorem check_two_selected :
    g1WalkExample.vals[g1WalkExample.arg2]? = some true ∧
      g1WalkExample.vals[0]? = some false ∧
      g1WalkExample.vals = [false, true, true] :=
  two_selected

/-- **The machine reaches Repair-1b's two words from `G1M.initialConfig`** —
those probes ran the sweep between them on a caller-supplied configuration —
and the repaired word is bit-for-bit the initial tape. -/
theorem check_two_repaired_tape :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 328).tape =
        g1ListTape (probeSpentFrames.flatMap G1Frame.bits) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400).tape =
        g1ListTape (probeIndexFrames.flatMap G1Frame.bits) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400).tape =
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))).tape :=
  ⟨two_repaired_kernel_words.1, two_repaired_tape.1, two_repaired_tape.2⟩

/-- **The executed sweep genuinely writes here too**: physical cell `32` flips
between the read's terminal tape and the repaired endpoint. -/
theorem check_two_repaired_cell32 :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 328).tape
        ⟨32, two_safe (by omega)⟩ = true ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400).tape
        ⟨32, two_safe (by omega)⟩ = false :=
  two_repaired_cell32

theorem check_two_repaired_clock :
    400 ≤ g1Clock (encodeG1 g1WalkExample).length :=
  two_repaired_clock

theorem check_readA_idle_after_two (k : Nat) :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) (400 + k) =
      g1ReadAConfig g1WalkExample true :=
  readA_idle_after_two k

/-! ## Both arms of the common capstone, on literals -/

theorem check_common_arms_distinct :
    g1ZeroExample.arg2 = 0 ∧ g1BReadExample.arg2 ≠ 0 ∧
      g1WalkExample.arg2 ≠ 0 :=
  common_arms_distinct

/-- **The branch is not vacuous**: at the zero-index request the other arm would
be `204`, not `172`. -/
theorem check_common_branch_literals :
    (if g1ZeroExample.arg2 = 0 then g1ZPassASteps g1ZeroExample
        else g1BPassASteps g1ZeroExample) = 172 ∧
      (if g1BReadExample.arg2 = 0 then g1ZPassASteps g1BReadExample
        else g1BPassASteps g1BReadExample) = 294 ∧
      (if g1WalkExample.arg2 = 0 then g1ZPassASteps g1WalkExample
        else g1BPassASteps g1WalkExample) = 400 ∧
      g1BPassASteps g1ZeroExample = 204 :=
  common_branch_literals

/-- The zero arm of `g1CS_readB_repaired_common`, on a literal. -/
theorem check_common_zero_arm :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
        (if g1ZeroExample.arg2 = 0 then g1ZPassASteps g1ZeroExample
          else g1BPassASteps g1ZeroExample) =
      g1ReadAConfig g1ZeroExample true :=
  common_zero_arm

/-- The positive arm of `g1CS_readB_repaired_common`, on a literal. -/
theorem check_common_positive_arm :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
        (if g1WalkExample.arg2 = 0 then g1ZPassASteps g1WalkExample
          else g1BPassASteps g1WalkExample) =
      g1ReadAConfig g1WalkExample true :=
  common_positive_arm

/-- Both literal totals fit the **unchanged** public clock. -/
theorem check_common_branch_clock :
    (if g1ZeroExample.arg2 = 0 then g1ZPassASteps g1ZeroExample
        else g1BPassASteps g1ZeroExample) ≤
        g1Clock (encodeG1 g1ZeroExample).length ∧
      (if g1WalkExample.arg2 = 0 then g1ZPassASteps g1WalkExample
        else g1BPassASteps g1WalkExample) ≤
        g1Clock (encodeG1 g1WalkExample).length :=
  common_branch_clock

end Pnp3.Tests.TMGateOneRepairExamplesSurface
