import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverStepTape
import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStepTerminates

/-!
# `driverTapes` — D2t-5b (Block A5c): the iterated tape run and its terminal output

Iterating the total one-step dispatcher (`driverStepTape`, Block A5b) along the abstract small-step
run gives the **semantic tape trajectory** of the driver loop:

* `driverTapes … k` — the tape after `k` micro-steps: each step applies the branch's tape transformer
  at the current abstract state `DriveState.step^[j] st₀`.
* `corridorInv_driverTapes` — the **iterated invariant**: if `driverCorridorInv` holds at the start
  and every step up to `k` has its zone capacities (`DriverStepFits`), the invariant holds after `k`
  steps — the loop-invariant induction of the A5 `loopUntilSink` discharge, settled once and for all
  at the tape level.
* `driverTapes_terminal_output` — **the transcoder's semantic endpoint**: running from the initial
  corridor layout for a certificate `c`, after `3 · c.size` steps (the proven termination bound,
  `driveStep_halts_bound`) the output window spells `encodeGateStream (flatten c).gates` — the exact
  count-prefixed postorder gate stream the row-loop interpreter consumes.

What remains for the machine half of A5 (separate bricks): realise each branch's arm as a composed
`ConstStatePhasedProgram` whose run effects exactly `driverStepTape` (the navigation legs and
read/write cores are merged; the `seq` transfers remain), couple the head/phase to the abstract
state, and discharge the loop's sink/measure at the `Configuration` level — `driveStep_halts_bound`
and this module then pin the final tape.

**Progress classification (AGENTS.md): Infrastructure** — tape-level invariant plumbing over the
verified keystones; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The iterated tape run**: the tape after `k` driver micro-steps, each applying the
branch-dispatched transformer at the current abstract state. -/
def driverTapes {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width) (z : DriverCorridor)
    (st0 : DriveState n) (tape0 : Fin L → Bool) : Nat → Fin L → Bool
  | 0 => tape0
  | k + 1 =>
      driverStepTape width h_width z (DriveState.step^[k] st0)
        (driverTapes width h_width z st0 tape0 k)

/-- **The iterated invariant.**  From `driverCorridorInv` at the start, with every step's zone
capacities up to `k`, the invariant holds after `k` micro-steps — at the iterated tape and the
iterated abstract state. -/
theorem corridorInv_driverTapes {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st0 : DriveState n) (tape0 : Fin L → Bool) (k : Nat)
    (hinv0 : driverCorridorInv width h_width z tape0 st0)
    (hfits : ∀ j, j < k → DriverStepFits z (DriveState.step^[j] st0)) :
    driverCorridorInv width h_width z (driverTapes width h_width z st0 tape0 k)
      (DriveState.step^[k] st0) := by
  induction k with
  | zero => simpa using hinv0
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact corridorInv_driverStep width h_width z (DriveState.step^[k] st0)
        (driverTapes width h_width z st0 tape0 k)
        (ih (fun j hj => hfits j (by omega))) (hfits k (by omega))

/-- **The transcoder's semantic endpoint.**  Starting from the initial corridor layout for the
certificate `c` (the `driverCorridorInv_init` configuration, with the static count prefix planted
at the final gate count `z.outCount = |(flatten c).gates|`), with every step's zone capacities,
after `3 · c.size` micro-steps the output window spells `encodeGateStream (flatten c).gates` — the
count-prefixed postorder gate stream, exactly the decoder/interpreter input format. -/
theorem driverTapes_terminal_output {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (c : CircuitTree n) (tape0 : Fin L → Bool)
    (hN : z.outCount = (CircuitTree.flatten c).gates.length)
    (hinv0 : driverCorridorInv width h_width z tape0
      (⟨preorder c, [], [], [], false⟩ : DriveState n))
    (hfits : ∀ j, j < 3 * c.size →
      DriverStepFits z (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n))) :
    windowSpells
      (driverTapes width h_width z (⟨preorder c, [], [], [], false⟩ : DriveState n) tape0
        (3 * c.size))
      (z.workBase - 1 - (CircuitTree.flatten c).gates.length)
      (encodeGateStream (CircuitTree.flatten c).gates) := by
  have hinv := corridorInv_driverTapes width h_width z _ tape0 (3 * c.size) hinv0 hfits
  obtain ⟨_hterm, hout_eq⟩ := driveStep_halts_bound (n := n) c
  obtain ⟨_, _, _, _, _, hout, _⟩ := hinv
  rw [hout_eq, hN] at hout
  simpa [encodeGateStream] using hout

end ContractExpansion
end Frontier
end Pnp4
