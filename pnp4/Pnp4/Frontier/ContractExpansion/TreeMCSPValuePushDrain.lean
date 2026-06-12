import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushPass

/-!
# `valuePushProgram` — D2t-6b (M1 / A5m-V, run II): the drain induction

Iterates the validated fan-out pass (`valuePush_pass`) from `i` to `k`: strong induction on the
remaining passes `k − i`, reusing the per-pass step bound.  The conclusion is the **drained** loop
layout `ValuePushLayout … k` (source empty, the entry carrying `k + 1` ones, the rebuilt block of
`k` ones against its fixed right edge) together with the cumulative untouched clause: everything
left of the entry (count, records, the value stack below) and everything from the shadow
terminator rightward (control stack, certificate) is byte-for-byte unchanged.

This mirrors `unaryTransfer_transfers` (strong induction over the unary count).  The next bricks
are the pre-hop entry, the relocate loop (restoring `SHW` in place), and the epilogue, then the
value-push headline.

**Progress classification (AGENTS.md): Infrastructure** — a machine-component run lemma; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 800000 in
/-- **The drain.**  From the loop layout at `i`, the drained layout at `k` is reached in
`≤ (k − i) · (2·shwBase + 2·k + 38)` steps, with everything outside `[vend + 2, shwBase + k + 3)`
untouched. -/
theorem valuePush_drain {L : Nat}
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k i : Nat) (hlay : ValuePushLayout c0 vend shwBase k i) :
    ∃ T : Nat, T ≤ (k - i) * (2 * shwBase + 2 * k + 38)
      ∧ ValuePushLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T) vend shwBase k k
      ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          ((p : Nat) < vend + 2 ∨ shwBase + k + 3 ≤ (p : Nat)) →
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).tape p = c0.tape p := by
  suffices H : ∀ n (c : Configuration (M := valuePushProgram.toPhased.toTM) L) (i : Nat),
      ValuePushLayout c vend shwBase k i → k - i = n →
      ∃ T : Nat, T ≤ n * (2 * shwBase + 2 * k + 38)
        ∧ ValuePushLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T) vend shwBase k k
        ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
            ((p : Nat) < vend + 2 ∨ shwBase + k + 3 ≤ (p : Nat)) →
            (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape p = c.tape p by
    exact H (k - i) c0 i hlay rfl
  intro n
  induction n with
  | zero =>
      intro c i hlay hn
      have hik : i = k := by have := hlay.hik; omega
      subst hik
      exact ⟨0, by simp, by simpa using hlay, fun p _ => rfl⟩
  | succ n ih =>
      intro c i hlay hn
      have hik : i < k := by omega
      have hD := hlay.hD
      have hvpos := hlay.hvpos
      obtain ⟨T1, hT1, hlay1, hunt1⟩ := valuePush_pass c vend shwBase k i hlay hik
      obtain ⟨T2, hT2, hlay2, hunt2⟩ :=
        ih (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T1) (i + 1) hlay1 (by omega)
      have hmul : (n + 1) * (2 * shwBase + 2 * k + 38)
          = n * (2 * shwBase + 2 * k + 38) + (2 * shwBase + 2 * k + 38) := by ring
      refine ⟨T1 + T2, ?_, ?_, ?_⟩
      · rw [hmul]; omega
      · rw [TM.runConfig_add]; exact hlay2
      · intro p hp
        rw [TM.runConfig_add]
        exact (hunt2 p hp).trans (hunt1 p (by omega) (by omega) (by omega))

end ContractExpansion
end Frontier
end Pnp4
