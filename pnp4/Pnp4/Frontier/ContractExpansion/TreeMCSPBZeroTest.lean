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

/-!
## The distinguishable-marker discriminating read (fixed-phase routing core)

The positional decision above (`head = w` iff `B = 0`) cannot become a *phase* branch by a local read:
the rightMarker is a single `1`, identical to a B set-bit, and its position `w` is data-dependent, so
a fixed-phase machine can neither read-distinguish it nor compare the head to a hardcoded `w`.

The agreed resolution (the maintainer's "distinguishable end-marker"): make the marker **locally
detectable by reading one extra cell**.  The layout invariant — call it *spread B + double marker* —

* terminates the counter window with a **double `1`** (cells `w` and `w+1` both `1`); and
* **separates** B's set bits, so the lowest set bit `j` is followed by a `0` (cell `j+1 = 0`).

Then the cell **immediately past the scan-stop** decides in a single fixed-phase read:

* `B = 0` ⇒ scan stops on the marker (`head = w`), and cell `head + 1 = w + 1` is the marker's second
  `1` (`bZeroRoute_zero_reads_one`);
* `B > 0` ⇒ scan stops on the lowest set bit (`head = j`), and cell `head + 1 = j + 1` is a separator
  `0` (`bZeroRoute_pos_reads_zero`).

So *read(scan-stop + 1) = `1` ⟺ `B = 0`* — a one-cell read a fixed-phase program can branch on
(`B = 0 →` sink, `B > 0 →` body-entry).  Both lemmas read the post-scan tape off the terminator's
**tape-invariance** clause, so the discriminating cell is whatever the layout placed there.

These state the invariant as **hypotheses** (routing-agnostic, like the lemmas above); the program
wiring (a phase that moves one cell right, reads, and branches) and the concrete spread-B layout
construction are the follow-up assembly.  Still no routing program is built here, and no `P ≠ NP` claim.
-/

/-- **`B = 0`: the cell past the scan-stop is the marker's second `1`.**  Under *spread B + double
marker* — counter cells `[0, w)` all `0`, marker cells `w` and `w + 1` both `1` — `gammaSelfLoopScan`
stops on the marker (`head = w`) and the cell `head + 1 = w + 1` reads `true`.  The discriminating read
sees `1`. -/
theorem bZeroRoute_zero_reads_one {L : Nat} (x : Boolcube.Point L) (w : Nat) (hw1 : w + 1 ≤ L)
    (hzeros : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) < w → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = false)
    (hmark1 : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = w → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = true)
    (hmark2 : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = w + 1 → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = true) :
    ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
        (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (w + 1)).head : Nat) = w
      ∧ ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L), (p : Nat) = w + 1 →
          (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
            (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (w + 1)).tape p = true := by
  obtain ⟨_, hhd, htp⟩ := gammaSelfLoopScan_runConfig_terminator x w (by omega) hzeros hmark1
  exact ⟨hhd, fun p hp => by rw [htp]; exact hmark2 p hp⟩

/-- **`B > 0`: the cell past the scan-stop is a separator `0`.**  Under *spread B + double marker* —
counter cells `[0, j)` all `0`, cell `j` set (`j < w`), and the separator cell `j + 1` is `0` —
`gammaSelfLoopScan` stops on the set bit (`head = j`) and the cell `head + 1 = j + 1` reads `false`.
The discriminating read sees `0`. -/
theorem bZeroRoute_pos_reads_zero {L : Nat} (x : Boolcube.Point L) (j w : Nat)
    (hjw : j < w) (hw1 : w + 1 ≤ L)
    (hzeros : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = false)
    (hbit : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = j → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = true)
    (hsep : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = j + 1 → (gammaSelfLoopScan.toPhased.toTM.initialConfig x).tape p = false) :
    ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
        (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L), (p : Nat) = j + 1 →
          (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
            (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (j + 1)).tape p = false := by
  obtain ⟨_, hhd, htp⟩ := gammaSelfLoopScan_runConfig_terminator x j (by omega) hzeros hbit
  exact ⟨hhd, fun p hp => by rw [htp]; exact hsep p hp⟩

end ContractExpansion
end Frontier
end Pnp4
