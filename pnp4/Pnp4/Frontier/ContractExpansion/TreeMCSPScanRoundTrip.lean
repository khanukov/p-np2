import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftSeqP1
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanComposition

/-!
# The corridor scan round trip — D2t-5b (Block A5m-1b)

Splices the two halves of the settle arms' navigation on the composed machine
`seq selfLoopScanLeft gammaSelfLoopScan`:

* **left leg** (A5m-1a): from a phase-`0` start at head `h₀` with a `1`-marker at `k < h₀` and `0`s
  in between, `(h₀ − k) + 2` steps land at the gamma scan's shifted start (phase `2`), head on the
  marker, tape unchanged;
* **right leg** (D2t-3b lift): from phase `2`, `0`s on `[k', k' + m)` and a `1` at `k' + m`, `m + 1`
  steps finish the rightward scan (phase `3`), head on that `1`, tape unchanged.

`scanRoundTrip_runConfig` chains them with `TM.runConfig_add`: one composed machine, end-to-end step
count `((h₀ − k) + 2) + (m + 1)`, tape untouched throughout.  This is the navigation skeleton of the
clear arm (scan to the control top, decide, scan back to the cursor marker) and the template for the
remaining arms' round trips.

**Progress classification (AGENTS.md): Infrastructure** — composition transfer for verifier machine
components; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The corridor scan round trip.**  On `seq selfLoopScanLeft gammaSelfLoopScan`: scan left from
`h₀` onto the `1`-marker at `k`, hand off, then scan right from `k` across the `0`s of
`[k, k + m)`… — stated with the right leg's own window: after the handoff the head sits at `k`; given
`0`s on `[k, k + m)` and a `1` at `k + m`, the whole trip takes `((h₀ − k) + 2) + (m + 1)` steps and
ends at phase `3` (the gamma scan's accept), head at `k + m`, tape unchanged.  (For the degenerate
`m = 0` the right leg halts immediately on the marker itself.) -/
theorem scanRoundTrip_runConfig {L : Nat}
    (c0 : Configuration (M := (seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (k : Nat) (hk : k < (c0.head : Nat))
    (hzeros : ∀ p : Fin ((seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false)
    (hterm : ∀ p : Fin ((seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = true)
    (m : Nat)
    (hroom : k + m ≤ L)
    (hzerosR : ∀ p : Fin ((seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      k ≤ (p : Nat) → (p : Nat) < k + m → c0.tape p = false)
    (htermR : ∀ p : Fin ((seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      (p : Nat) = k + m → c0.tape p = true) :
    (((TM.runConfig (M := (seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM) c0
        ((((c0.head : Nat) - k) + 2) + (m + 1))).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := (seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM) c0
          ((((c0.head : Nat) - k) + 2) + (m + 1))).head : Nat) = k + m
      ∧ (TM.runConfig (M := (seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM) c0
          ((((c0.head : Nat) - k) + 2) + (m + 1))).tape = c0.tape := by
  obtain ⟨hph1, hst1, hhd1, htp1⟩ :=
    selfLoopScanLeft_seq_runConfig_terminator_handoff gammaSelfLoopScan c0 hphase k hk
      hzeros hterm
  rw [TM.runConfig_add]
  set c1 := TM.runConfig (M := (seq selfLoopScanLeft gammaSelfLoopScan).toPhased.toTM) c0
    (((c0.head : Nat) - k) + 2) with hc1
  have hph1' : (c1.state.fst : Nat) = selfLoopScanLeft.numPhases := by
    rw [hph1]; rfl
  obtain ⟨hph2, hhd2, htp2⟩ := gammaSelfLoopScan_seqP2_runConfig_terminator selfLoopScanLeft
    c1 hph1' m
    (by rw [hhd1]; exact hroom)
    (fun p hp1 hp2 => by
      rw [htp1]
      exact hzerosR p (by rw [hhd1] at hp1; exact hp1) (by rw [hhd1] at hp2; exact hp2))
    (fun p hp => by
      rw [htp1]
      exact htermR p (by rw [hhd1] at hp; exact hp))
  refine ⟨?_, ?_, ?_⟩
  · rw [hph2]; rfl
  · rw [hhd2, hhd1]
  · rw [htp2, htp1]

end ContractExpansion
end Frontier
end Pnp4
