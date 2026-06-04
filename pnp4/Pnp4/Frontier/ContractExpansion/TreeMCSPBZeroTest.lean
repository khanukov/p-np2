import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram
import Complexity.TMVerifier.TuringToolkit.BinaryCounter

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-!
# `bZeroTest` — the binary→unary loop-exit decision (NP-verifier track — D2 transcoder, D2t-3c-δ)

The conversion loop (`TM_VERIFIER_STRATEGY.md` §12) must decide, from HOME, whether the little-endian
binary counter `B` is `0` (stop) or `> 0` (run one more `binToUnaryBody` pass).  The documented
mechanism (§12, the "counter-zero test"): the layout places a `1` **rightMarker** just past `B`,

```
[ … | U = 1^|U| | sentinel(0) | B = b_0 … b_{w-1} | rightMarker(1) | … ]
```

and a rightward zero-scan (`gammaSelfLoopScan`, which advances over `0`s and halts on the first `1`)
**halts on the marker iff `B` held no `1` before it** (so `B = 0`), and halts **strictly before** the
marker iff some bit of `B` is set (so `B > 0`).

This module proves that **semantic decision** in its standalone (`initialConfig`) form — the
routing-agnostic core — as two run-lemmas, both direct instances of
`gammaSelfLoopScan_runConfig_terminator`:

* `bZeroTest_zero_halts_on_marker` — all of `B`'s `w` cells `0` (`counterValue = 0`) ⇒ the scan halts
  **on** the marker (head `= w`), after `w + 1` steps;
* `bZeroTest_pos_halts_before_marker` — `B`'s lowest set bit at `j < w` ⇒ the scan halts **before** the
  marker (head `= j < w`), after `j + 1` steps.

Together: *scan halts on the marker ⟺ `B = 0`* — the loop-exit predicate.

**Deferred (the genuine crux):** turning this **positional** decision into a **phase** branch
(`B = 0 →` `loopUntilSink` sink vs `B > 0 →` body-entry) is the marker-free routing problem §12 flags;
both stop-cells are a single `1`, so a one-cell read can't distinguish them.  That mechanism (and the
`loopUntilSink` wiring ε) is the follow-up; this brick fixes only the semantic decision.

Builds no verifier and proves no separation; standard `[propext, Classical.choice, Quot.sound]` triple.
**No `P ≠ NP` claim.**
-/

/-- **`B = 0` ⇒ the zero-scan halts on the rightMarker.**  If all `w` counter cells `[0, w)` are `0`
and cell `w` is the `1` rightMarker, then after `w + 1` steps `gammaSelfLoopScan` rests in its done
phase (`1`) with the head **on the marker** (`head = w`); and `counterValue` of the window is `0`.
Instance of `gammaSelfLoopScan_runConfig_terminator` at `z := w`, with the value read off by
`counterValue_of_all_false`. -/
theorem bZeroTest_zero_halts_on_marker {L : Nat} (x : Boolcube.Point L) (w : Nat) (hw : w ≤ L)
    (hzeros : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) < w → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = false)
    (hmarker : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = w → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
        (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (w + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
          (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (w + 1)).head : Nat) = w
      ∧ counterValue (gammaSelfLoopScan.toPhased.toTM.initialConfig x) 0 w = 0 := by
  obtain ⟨hph, hhd, _⟩ := gammaSelfLoopScan_runConfig_terminator x w hw hzeros hmarker
  refine ⟨hph, hhd, ?_⟩
  exact counterValue_of_all_false (gammaSelfLoopScan.toPhased.toTM.initialConfig x) 0 w
    (fun i hi hb => hzeros ⟨0 + i, hb⟩ (by show 0 + i < w; omega))

/-- **`B > 0` ⇒ the zero-scan halts before the rightMarker.**  If `B`'s lowest set bit is at `j < w`
(cells `[0, j)` are `0`, cell `j` is `1`), then after `j + 1` steps `gammaSelfLoopScan` rests in its
done phase (`1`) with the head on that bit (`head = j`), which is **strictly left of the marker**
(`j < w`).  Instance of `gammaSelfLoopScan_runConfig_terminator` at `z := j`. -/
theorem bZeroTest_pos_halts_before_marker {L : Nat} (x : Boolcube.Point L) (j w : Nat)
    (hjw : j < w) (hw : w ≤ L)
    (hzeros : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = false)
    (hbit : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = j → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
        (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
          (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
          (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) < w := by
  obtain ⟨hph, hhd, _⟩ := gammaSelfLoopScan_runConfig_terminator x j (by omega) hzeros hbit
  exact ⟨hph, hhd, by rw [hhd]; exact hjw⟩

end ContractExpansion
end Frontier
end Pnp4
