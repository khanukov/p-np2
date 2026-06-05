import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroTest

/-!
# Realizability of the `bZeroTest` routing hypotheses (NP-verifier track — D2t-3 routing)

`TreeMCSPBZeroTest.lean` proves the discriminating-read routing decision *routing-agnostically*: the
`spread B + double marker` invariant enters as hypotheses (`hzeros`/`hmark1`/`hmark2` for `B = 0`,
`hzeros`/`hbit`/`hsep` for `B > 0`).  This module discharges those hypotheses against **concrete inputs**,
so the routing lemmas are **non-vacuously instantiable** — the distinguishable-marker layout exists, and
the bound `w + 1 < L` (from #1549's boundary fix) is exactly what makes the second marker realizable.

* `bZeroRoute_zero_realizable` — the input with the **double marker** at cells `w`, `w + 1` (all else `0`)
  drives `gammaSelfLoopScan` to halt **on** the marker (`head = w`) with the next cell reading `1`; and
  its counter window has `counterValue = 0` (the genuine `B = 0`).
* `bZeroRoute_pos_realizable` — the input with a **single set bit** at `j < w` (the minimal `B > 0`, all
  else `0`, so cell `j + 1` is its own separator) drives the scan to halt **before** the marker
  (`head = j`) with the next cell reading `0`.

These are *existence* witnesses (validation that the routing layer isn't vacuous), not the converter's
real layout construction.  **Progress classification (AGENTS.md): Infrastructure.**  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-- **`B = 0` routing is realizable.**  The input whose only `1`s are the double marker at cells `w`,
`w + 1` (`w + 1 < L`, so both lie in the input region) satisfies `bZeroRoute_zero_reads_one`: the scan
halts on the marker (`head = w`), the cell past it reads `1`, and the counter window is `0`. -/
theorem bZeroRoute_zero_realizable {L w : Nat} (hw1 : w + 1 < L) :
    ∃ x : Boolcube.Point L,
      ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
          (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (w + 1)).head : Nat) = w
      ∧ (∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L), (p : Nat) = w + 1 →
          (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
            (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (w + 1)).tape p = true)
      ∧ counterValue (gammaSelfLoopScan.toPhased.toTM.initialConfig x) 0 w = 0 := by
  refine ⟨fun j => decide ((j : Nat) = w ∨ (j : Nat) = w + 1), ?_⟩
  have hmark1 : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = w → (gammaSelfLoopScan.toPhased.toTM.initialConfig
        (fun j => decide ((j : Nat) = w ∨ (j : Nat) = w + 1))).tape p = true := by
    intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  have hmark2 : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = w + 1 → (gammaSelfLoopScan.toPhased.toTM.initialConfig
        (fun j => decide ((j : Nat) = w ∨ (j : Nat) = w + 1))).tape p = true := by
    intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  have hzeros : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) < w → (gammaSelfLoopScan.toPhased.toTM.initialConfig
        (fun j => decide ((j : Nat) = w ∨ (j : Nat) = w + 1))).tape p = false := by
    intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  obtain ⟨hhd, hread⟩ := bZeroRoute_zero_reads_one
    (fun j => decide ((j : Nat) = w ∨ (j : Nat) = w + 1)) w hw1 hzeros hmark1 hmark2
  exact ⟨hhd, hread, counterValue_of_all_false _ 0 w (fun i hi hb => hzeros ⟨0 + i, hb⟩ (by show 0 + i < w; omega))⟩

/-- **`B > 0` routing is realizable.**  The input whose only `1` is a single set bit at `j < w` (the
minimal `B > 0`; cell `j + 1` is then its own `0` separator) satisfies `bZeroRoute_pos_reads_zero`: the
scan halts on that bit (`head = j`), strictly left of the marker, with the cell past it reading `0`. -/
theorem bZeroRoute_pos_realizable {L j w : Nat} (hjw : j < w) (hw1 : w + 1 < L) :
    ∃ x : Boolcube.Point L,
      ((TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
          (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ (∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L), (p : Nat) = j + 1 →
          (TM.runConfig (M := gammaSelfLoopScan.toPhased.toTM)
            (gammaSelfLoopScan.toPhased.toTM.initialConfig x) (j + 1)).tape p = false) := by
  refine ⟨fun q => decide ((q : Nat) = j), ?_⟩
  have hbit : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = j → (gammaSelfLoopScan.toPhased.toTM.initialConfig
        (fun q => decide ((q : Nat) = j))).tape p = true := by
    intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_true_eq]; omega
  have hsep : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) = j + 1 → (gammaSelfLoopScan.toPhased.toTM.initialConfig
        (fun q => decide ((q : Nat) = j))).tape p = false := by
    intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  have hzeros : ∀ p : Fin (gammaSelfLoopScan.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (gammaSelfLoopScan.toPhased.toTM.initialConfig
        (fun q => decide ((q : Nat) = j))).tape p = false := by
    intro p hp
    have hpL : (p : Nat) < L := by omega
    simp only [initialConfig]; rw [dif_pos hpL]; simp only [decide_eq_false_iff_not]; omega
  obtain ⟨hhd, hread⟩ := bZeroRoute_pos_reads_zero
    (fun q => decide ((q : Nat) = j)) j w hjw hw1.le hzeros hbit hsep
  exact ⟨hhd, hread⟩

end ContractExpansion
end Frontier
end Pnp4
