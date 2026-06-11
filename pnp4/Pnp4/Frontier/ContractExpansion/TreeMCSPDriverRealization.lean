import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverFits

/-!
# `DriverRealization` — D2t-5b (Block A5m-9/10 skeleton): the Configuration-level loop discharge

The arms-and-dispatch machine work (A5m-2 … A5m-8) culminates in exactly one statement: *from the
home configuration of an abstract state `st`, one driver iteration reaches the home configuration of
`st.step`, effecting precisely the dispatched tape rewrite `driverStepTape … st`, within a uniform
step budget*.  This module fixes that statement as the **interface** `DriverRealization` (machine +
home-configuration coupling + per-iteration run field) and discharges the **whole loop** from it:

* `DriverRealization.run_simulates` — iterating the per-step field couples the machine run with the
  semantic spine: after `k` abstract steps the machine sits in the home configuration of
  `DriveState.step^[k]` with tape exactly `driverTapes … k`, within `k · stepBudget` machine steps
  (the loop-invariant induction, fed by `corridorInv_driverTapes`).
* `DriverRealization.terminal_output` — at `k := 3 · c.size` (`driveStep_halts_bound`) on a sized
  corridor (`CorridorSized`), the machine's tape spells `encodeGateStream (flatten c).gates` in the
  output window, within `3 · c.size · stepBudget` machine steps — **the Configuration-level D2t-5c**,
  conditional only on the interface instance.

Constructing a `DriverRealization` instance is the remaining machine work (the A5m-2 … A5m-8 arms
and the A5m-9 dispatch); this module turns everything *downstream* of that construction into
theorems, so the transcoder capstone (D2t-6b) reduces to the instance.

**Progress classification (AGENTS.md): Infrastructure** — an interface plus loop-discharge theorems
over the verified semantic spine; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The driver-machine interface.**  A phased program `P`, a home-configuration coupling `home`
(the machine's idle point for an abstract state: in practice "head on the cursor marker, phase the
settling/reading home"), a uniform per-iteration step budget, and the **per-iteration run field**:
from the home configuration of `st`, under the corridor invariant and the branch's zone capacities,
some `t ≤ stepBudget` machine steps reach the home configuration of `st.step` having effected
exactly the dispatched rewrite `driverStepTape … st`.  The A5m-2 … A5m-9 arms-and-dispatch bricks
construct an instance; everything downstream is discharged here. -/
structure DriverRealization (n : Nat) (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (L : Nat) where
  /-- The driver machine, as a phased program. -/
  P : ConstStatePhasedProgram Unit
  /-- The home-configuration coupling: the machine's idle configuration for an abstract state. -/
  home : DriveState n → Configuration (M := P.toPhased.toTM) L → Prop
  /-- The uniform per-iteration step budget. -/
  stepBudget : Nat
  /-- One driver iteration: home-to-home, effecting exactly the dispatched tape rewrite. -/
  step_run : ∀ (st : DriveState n) (c : Configuration (M := P.toPhased.toTM) L),
    home st c →
    driverCorridorInv width h_width z c.tape st →
    DriverStepFits z st →
    ∃ t, t ≤ stepBudget
      ∧ home st.step (TM.runConfig (M := P.toPhased.toTM) c t)
      ∧ (TM.runConfig (M := P.toPhased.toTM) c t).tape
          = driverStepTape width h_width z st c.tape

namespace DriverRealization

variable {n width : Nat} {h_width : n ≤ 2 ^ width} {z : DriverCorridor} {L : Nat}

/-- **The loop simulation.**  Iterating the per-step field: after `k` abstract steps the machine
sits in the home configuration of `DriveState.step^[k] st₀` with tape exactly
`driverTapes … st₀ tape₀ k`, within `k · stepBudget` machine steps. -/
theorem run_simulates (R : DriverRealization n width h_width z L)
    (st0 : DriveState n) (c0 : Configuration (M := R.P.toPhased.toTM) L)
    (h0 : R.home st0 c0)
    (hinv0 : driverCorridorInv width h_width z c0.tape st0)
    (k : Nat) (hfits : ∀ j, j < k → DriverStepFits z (DriveState.step^[j] st0)) :
    ∃ T, T ≤ k * R.stepBudget
      ∧ R.home (DriveState.step^[k] st0) (TM.runConfig (M := R.P.toPhased.toTM) c0 T)
      ∧ (TM.runConfig (M := R.P.toPhased.toTM) c0 T).tape
          = driverTapes width h_width z st0 c0.tape k := by
  induction k with
  | zero =>
      refine ⟨0, Nat.zero_le _, ?_, rfl⟩
      simpa using h0
  | succ k ih =>
      obtain ⟨T, hT, hhome, htape⟩ := ih (fun j hj => hfits j (by omega))
      have hinvk : driverCorridorInv width h_width z
          (TM.runConfig (M := R.P.toPhased.toTM) c0 T).tape (DriveState.step^[k] st0) := by
        rw [htape]
        exact corridorInv_driverTapes width h_width z st0 c0.tape k hinv0
          (fun j hj => hfits j (by omega))
      obtain ⟨t, ht, hhome', htape'⟩ :=
        R.step_run (DriveState.step^[k] st0) _ hhome hinvk (hfits k (by omega))
      have hbudget : (k + 1) * R.stepBudget = k * R.stepBudget + R.stepBudget := by ring
      refine ⟨T + t, by omega, ?_, ?_⟩
      · rw [TM.runConfig_add, Function.iterate_succ_apply']
        exact hhome'
      · rw [TM.runConfig_add, htape', htape]
        rfl

/-- **The Configuration-level terminal output (D2t-5c, conditional on the instance).**  From the
home configuration of the initial state for a certificate `c`, on a sized corridor, within
`3 · c.size · stepBudget` machine steps the machine's tape spells
`encodeGateStream (flatten c).gates` in the output window. -/
theorem terminal_output (R : DriverRealization n width h_width z L)
    (c : CircuitTree n) (c0 : Configuration (M := R.P.toPhased.toTM) L)
    (h0 : R.home (⟨preorder c, [], [], [], false⟩ : DriveState n) c0)
    (hinv0 : driverCorridorInv width h_width z c0.tape
      (⟨preorder c, [], [], [], false⟩ : DriveState n))
    (hz : CorridorSized z c) :
    ∃ T, T ≤ 3 * c.size * R.stepBudget
      ∧ windowSpells (TM.runConfig (M := R.P.toPhased.toTM) c0 T).tape
          (z.workBase - 1 - (CircuitTree.flatten c).gates.length)
          (encodeGateStream (CircuitTree.flatten c).gates) := by
  obtain ⟨T, hT, _, htape⟩ := R.run_simulates _ c0 h0 hinv0 (3 * c.size)
    (fun j hj => reachable_driverStepFits z c hz hj)
  refine ⟨T, hT, ?_⟩
  rw [htape]
  exact driverTapes_terminal_output_sized width h_width z c c0.tape hz hinv0

end DriverRealization

end ContractExpansion
end Frontier
end Pnp4
