import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckComposition
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanComposition
import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaFillComposition

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Chaining `M`'s first two leading phases: tag check ▸ gamma scan (NP-verifier track)

The two composition modules supply the run behaviour of each leading phase *inside a `seq`*:

* `tagCheckProgramU_seq_runConfig_handoff` — on a matching tag, `seq tagCheckProgramU P2` reaches
  `P2`'s shifted start phase after `tagLen + 1` steps (head at `tagLen`, tape unchanged);
* `gammaSelfLoopScan_seqP2_runConfig_scanning` — from a configuration at phase `P1.numPhases`, the
  gamma scan advances the head across an all-zero window.

Instantiating the first at `P2 := gammaSelfLoopScan` lands control at phase
`tagCheckProgramU.numPhases + gammaSelfLoopScan.startPhase = tagCheckProgramU.numPhases`, which is
exactly the start configuration the second lemma consumes (`P1 := tagCheckProgramU`).  Splicing them
with `TM.runConfig_add` gives the **end-to-end run of `M`'s first two phases**: from the initial
configuration, a matching tag plus an all-zero gamma prefix of length `k` leaves the machine, after
`(tagLen + 1) + k` steps, still in the gamma-scan phase with the head advanced to `tagLen + k` and the
tape untouched.  This is the first result that runs *two distinct phases* of `M` in sequence on one
composed machine, validating the per-instance composition lemmas as a chain.

Scope: the explicit 2-phase composition `seq tagCheckProgramU gammaSelfLoopScan` (M's first two leading
phases).  Chaining the full nested `seqList` of `mSkeletonU` is the documented follow-up.  Builds no
verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` execution triple. -/

/-- End-to-end run of `M`'s first two phases on `seq tagCheckProgramU gammaSelfLoopScan`: if the first
`tagLen` input cells match the tag and the next `k` cells (positions `tagLen .. tagLen + k`) are all
`0`, then after `(tagLen + 1) + k` steps (`tagLen` to scan the tag, one for the handoff, `k` for the
gamma zero-scan) the machine rests in the gamma-scan phase (`tagLen + 2`), with the head advanced to
`tagLen + k` and the tape unchanged.  Splices the tag-check handoff and the gamma-scan invariant via
`TM.runConfig_add`. -/
theorem tagCheckThenGammaScan_runConfig {L : Nat} (x : Boolcube.Point L)
    (hmatch : tagMatchPrefix x tagLen = true)
    (k : Nat) (hk : tagLen + k ≤ L)
    (hzeros : ∀ p : Fin ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      tagLen ≤ (p : Nat) → (p : Nat) < tagLen + k →
      ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x).tape p = false) :
    (((TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
        ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x)
        ((tagLen + 1) + k)).state).fst : Nat) = tagLen + 2
      ∧ ((TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
          ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x)
          ((tagLen + 1) + k)).head : Nat) = tagLen + k
      ∧ (TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
          ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x)
          ((tagLen + 1) + k)).tape
          = ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨hph1, hhd1, htp1⟩ := tagCheckProgramU_seq_runConfig_handoff gammaSelfLoopScan x hmatch
  rw [TM.runConfig_add]
  -- Make the `tagLen + 1`-step config opaque, then run the gamma scan from it.
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
    ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x) (tagLen + 1) = c1
  intro hph1 hhd1 htp1
  have hphase : (c1.state.fst : Nat) = tagCheckProgramU.numPhases := by
    rw [hph1]; simp [gammaSelfLoopScan_startPhase_val, tagCheckProgramU_numPhases]
  obtain ⟨hsp, hsh, hst⟩ :=
    gammaSelfLoopScan_seqP2_runConfig_scanning tagCheckProgramU c1 hphase k
      (by rw [hhd1]; exact hk)
      (by
        intro p hp1 hp2
        rw [htp1]
        rw [hhd1] at hp1 hp2
        exact hzeros p hp1 hp2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsp, tagCheckProgramU_numPhases]
  · rw [hsh, hhd1]
  · rw [hst, htp1]

/-- Tag check ▸ gamma scan ▸ terminator on `seq tagCheckProgramU gammaSelfLoopScan`: if the first
`tagLen` cells match the tag, the next `z` cells (positions `tagLen .. tagLen + z`) are `0`, and the
cell at `tagLen + z` is `1` (the gamma terminator), then after `(tagLen + 1) + (z + 1)` steps the scan
has stopped at the gamma scan's shifted accept phase (`tagLen + 3`), the head rests **exactly on the
gamma terminator** (`tagLen + z`), and the tape is unchanged.  Extends `tagCheckThenGammaScan_runConfig`
by one terminator step: this pins the head at the launch point for the gamma payload decode (the next,
genuinely data-dependent, phase of `M`). -/
theorem tagCheckThenGammaScanTerminator_runConfig {L : Nat} (x : Boolcube.Point L)
    (hmatch : tagMatchPrefix x tagLen = true)
    (z : Nat) (hz : tagLen + z ≤ L)
    (hzeros : ∀ p : Fin ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      tagLen ≤ (p : Nat) → (p : Nat) < tagLen + z →
      ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x).tape p = false)
    (hterm : ∀ p : Fin ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.tapeLength L),
      (p : Nat) = tagLen + z →
      ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
        ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x)
        ((tagLen + 1) + (z + 1))).state).fst : Nat) = tagLen + 3
      ∧ ((TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
          ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x)
          ((tagLen + 1) + (z + 1))).head : Nat) = tagLen + z
      ∧ (TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
          ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x)
          ((tagLen + 1) + (z + 1))).tape
          = ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨hph1, hhd1, htp1⟩ := tagCheckProgramU_seq_runConfig_handoff gammaSelfLoopScan x hmatch
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM)
    ((seq tagCheckProgramU gammaSelfLoopScan).toPhased.toTM.initialConfig x) (tagLen + 1) = c1
  intro hph1 hhd1 htp1
  have hphase : (c1.state.fst : Nat) = tagCheckProgramU.numPhases := by
    rw [hph1]; simp [gammaSelfLoopScan_startPhase_val, tagCheckProgramU_numPhases]
  obtain ⟨hsp, hsh, hst⟩ :=
    gammaSelfLoopScan_seqP2_runConfig_terminator tagCheckProgramU c1 hphase z
      (by rw [hhd1]; exact hz)
      (by
        intro p hp1 hp2
        rw [htp1]
        rw [hhd1] at hp1 hp2
        exact hzeros p hp1 hp2)
      (by
        intro p hp
        rw [htp1]
        rw [hhd1] at hp
        exact hterm p hp)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsp, tagCheckProgramU_numPhases]
  · rw [hsh, hhd1]
  · rw [hst, htp1]

/-- **Transitively-nested** chain (`seqList` length ≥ 3): tag check ▸ handoff ▸ gamma zero-scan, where
the gamma scan sits in the *doubly-nested* P2∘P1 position `seq tagCheckProgramU (seq gammaSelfLoopScan
R)` (the shape of `mSkeletonU`'s first two phases, with `R` carrying the remaining phases).  On a
matching tag and an all-zero gamma prefix of length `k`, after `(tagLen + 1) + k` steps the machine
rests in the gamma-scan phase (`tagLen + 2`), head advanced to `tagLen + k`, tape unchanged.  Splices
the tag-check handoff (`P2 := seq gammaSelfLoopScan R`) with the nested scanning invariant via
`TM.runConfig_add`, proving the per-phase composition lemmas chain to *any* `seqList` depth. -/
theorem tagCheckThenNestedGammaScan_runConfig (R : ConstStatePhasedProgram Unit) {L : Nat}
    (x : Boolcube.Point L) (hmatch : tagMatchPrefix x tagLen = true)
    (k : Nat) (hk : tagLen + k ≤ L)
    (hzeros : ∀ p : Fin ((seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM.tapeLength L),
      tagLen ≤ (p : Nat) → (p : Nat) < tagLen + k →
      ((seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM.initialConfig x).tape p = false) :
    (((TM.runConfig (M := (seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM)
        ((seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM.initialConfig x)
        ((tagLen + 1) + k)).state).fst : Nat) = tagLen + 2
      ∧ ((TM.runConfig (M := (seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM)
          ((seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM.initialConfig x)
          ((tagLen + 1) + k)).head : Nat) = tagLen + k
      ∧ (TM.runConfig (M := (seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM)
          ((seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM.initialConfig x)
          ((tagLen + 1) + k)).tape
          = ((seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨hph1, hhd1, htp1⟩ :=
    tagCheckProgramU_seq_runConfig_handoff (seq gammaSelfLoopScan R) x hmatch
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := (seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM)
    ((seq tagCheckProgramU (seq gammaSelfLoopScan R)).toPhased.toTM.initialConfig x) (tagLen + 1) = c1
  intro hph1 hhd1 htp1
  have hphase : (c1.state.fst : Nat) = tagCheckProgramU.numPhases := by
    rw [hph1]
    simp [seq_startPhase_val, gammaSelfLoopScan_startPhase_val, tagCheckProgramU_numPhases]
  obtain ⟨hsp, hsh, hst⟩ :=
    gammaSelfLoopScan_seqNested_runConfig_scanning tagCheckProgramU R c1 hphase k
      (by rw [hhd1]; exact hk)
      (by
        intro p hp1 hp2
        rw [htp1]
        rw [hhd1] at hp1 hp2
        exact hzeros p hp1 hp2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsp, tagCheckProgramU_numPhases]
  · rw [hsh, hhd1]
  · rw [hst, htp1]

/-- Tag check ▸ gamma fill on `seq tagCheckProgramU gammaSelfLoopFill`: the genuine first two leading
phases of `M` in the counter-materializing variant.  If the first `tagLen` cells match the tag and the
next `k` cells (`tagLen .. tagLen + k`) are `0`, then after `(tagLen + 1) + k` steps control rests in
the fill phase (`tagLen + 2`), the head has advanced to `tagLen + k`, and the window `[tagLen, tagLen+k)`
has been **filled with `1`** in place (rest of tape unchanged) — i.e. a length-`k` unary counter is now
materialized just past the tag.  The fill-tape analogue of `tagCheckThenGammaScan_runConfig`: verify the
tag, then turn the gamma leading-zero block into the loop counter the `repeatBody` combinator consumes
for the payload read. -/
theorem tagCheckThenGammaFill_runConfig {L : Nat} (x : Boolcube.Point L)
    (hmatch : tagMatchPrefix x tagLen = true)
    (k : Nat) (hk : tagLen + k ≤ L)
    (hzeros : ∀ p : Fin ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.tapeLength L),
      tagLen ≤ (p : Nat) → (p : Nat) < tagLen + k →
      ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.initialConfig x).tape p = false) :
    (((TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM)
        ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.initialConfig x)
        ((tagLen + 1) + k)).state).fst : Nat) = tagLen + 2
      ∧ ((TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM)
          ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.initialConfig x)
          ((tagLen + 1) + k)).head : Nat) = tagLen + k
      ∧ ∀ p : Fin ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM)
            ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.initialConfig x)
            ((tagLen + 1) + k)).tape p
            = (if tagLen ≤ (p : Nat) ∧ (p : Nat) < tagLen + k
                then true
                else ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.initialConfig x).tape p) := by
  obtain ⟨hph1, hhd1, htp1⟩ := tagCheckProgramU_seq_runConfig_handoff gammaSelfLoopFill x hmatch
  rw [TM.runConfig_add]
  revert hph1 hhd1 htp1
  generalize TM.runConfig (M := (seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM)
    ((seq tagCheckProgramU gammaSelfLoopFill).toPhased.toTM.initialConfig x) (tagLen + 1) = c1
  intro hph1 hhd1 htp1
  have hphase : (c1.state.fst : Nat) = tagCheckProgramU.numPhases := by
    rw [hph1]; simp [gammaSelfLoopFill_startPhase_val, tagCheckProgramU_numPhases]
  obtain ⟨hfp, hfh, hft⟩ :=
    gammaSelfLoopFill_seqP2_runConfig_fill tagCheckProgramU c1 hphase k
      (by rw [hhd1]; exact hk)
      (by
        intro p hp1 hp2
        rw [htp1]
        rw [hhd1] at hp1 hp2
        exact hzeros p hp1 hp2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfp, tagCheckProgramU_numPhases]
  · rw [hfh, hhd1]
  · intro p
    rw [hft p, hhd1, htp1]

end ContractExpansion
end Frontier
end Pnp4
