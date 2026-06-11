import Pnp4.Frontier.ContractExpansion.TreeMCSPClearIterRun

/-!
# The write segment — D2t-5b (Block A5m-U6): fixed-block writes, host-generic

The write half of the dec/node/const arms: any machine hosting `writeBits bs` as a region performs
the block write in `|bs| + 1` steps (one per cell, one redirect), ending at the region's exit with
the head one past the block and the tape **exactly `writeBlockTape tape h bs`** — the literal
transformer of the A4 keystones (`corridorInv_decStep`'s frame rewrite, the node arm's frame push,
the value-entry writes).  One instantiation per fixed-block write at assembly.

**Progress classification (AGENTS.md): Infrastructure** — a host-generic run segment; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

namespace RegionEmbedded

variable {U : ConstStatePhasedProgram Unit} {base next : Nat}

/-- **The write segment, writing half**: from the region's phase `base` at head `h` (with room for
the whole block), `k ≤ |bs|` steps write the block's first `k` cells rightward: phase `base + k`,
head `h + k`, and the tape is the partial block overlay. -/
theorem run_writeBits_writing {bs : List Bool} (hUP : RegionEmbedded U (writeBits bs) base next)
    {L : Nat} (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + bs.length < U.toPhased.toTM.tapeLength L) :
    ∀ k : Nat, k ≤ bs.length →
      (((TM.runConfig (M := U.toPhased.toTM) c0 k).state).fst : Nat) = base + k
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) + k
      ∧ ∀ q : Fin (U.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := U.toPhased.toTM) c0 k).tape q
            = if (c0.head : Nat) ≤ (q : Nat) ∧ (q : Nat) < (c0.head : Nat) + k
              then bs.getD ((q : Nat) - (c0.head : Nat)) false
              else c0.tape q := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨by simpa using hphase, by simp, fun q => ?_⟩
      rw [if_neg (by omega)]
      rfl
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := U.toPhased.toTM) c0 k with hc
      have hkb : k < bs.length := by omega
      have hij : (c.state.fst : Nat) = base + (⟨k, by simp [writeBits]; omega⟩
          : Fin (writeBits bs).numPhases).val := by simpa using hph
      have hjne : (⟨k, by simp [writeBits]; omega⟩ : Fin (writeBits bs).numPhases).val
          ≠ ((writeBits bs).acceptPhase : Nat) := by
        simp [writeBits]
        omega
      have hbroom : (c.head : Nat) + 1 < U.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hUP.stepConfig_normal_phase c rfl _ hij hjne]
        simp [writeBits, dif_pos hkb]
      · rw [hUP.stepConfig_normal_head c rfl _ hij hjne]
        have hm : ((writeBits bs).transition ⟨k, by simp [writeBits]; omega⟩ ()
            (c.tape c.head)).snd.snd.snd = Move.right := by
          simp [writeBits, dif_pos hkb]
        rw [hm]
        simp only [Configuration.moveHead, dif_pos hbroom]
        rw [hhd]
        omega
      · intro q
        rw [hUP.stepConfig_normal_tape c rfl _ hij hjne]
        have hb : ((writeBits bs).transition ⟨k, by simp [writeBits]; omega⟩ ()
            (c.tape c.head)).snd.snd.fst = bs.getD k false := by
          simp [writeBits, dif_pos hkb]
        rw [hb]
        by_cases hq : q = c.head
        · subst hq
          have hL : (c.write c.head (bs.getD k false)) c.head = bs.getD k false := by
            simp [Configuration.write]
          rw [hL, if_pos (show (c0.head : Nat) ≤ (c.head : Nat)
              ∧ (c.head : Nat) < (c0.head : Nat) + (k + 1) from by omega),
            show ((c.head : Nat) - (c0.head : Nat)) = k from by omega]
        · have hL : (c.write c.head (bs.getD k false)) q = c.tape q := by
            simp [Configuration.write, hq]
          rw [hL, htp q]
          have hqv : (q : Nat) ≠ (c.head : Nat) := fun hc' => hq (Fin.ext hc')
          by_cases hin : (c0.head : Nat) ≤ (q : Nat) ∧ (q : Nat) < (c0.head : Nat) + k
          · rw [if_pos hin, if_pos (show (c0.head : Nat) ≤ (q : Nat)
                ∧ (q : Nat) < (c0.head : Nat) + (k + 1) from by omega)]
          · rw [if_neg hin, if_neg (show ¬ ((c0.head : Nat) ≤ (q : Nat)
                ∧ (q : Nat) < (c0.head : Nat) + (k + 1)) from by omega)]

/-- **The write-segment hop**: from the region's phase `base` at head `h` (with room), `|bs| + 1`
steps (the block write plus the redirect) end at the absolute phase `next`, head `h + |bs|`, and
tape **exactly `writeBlockTape tape h bs`** — the keystones' write transformer. -/
theorem run_writeBits_hop {bs : List Bool} (hUP : RegionEmbedded U (writeBits bs) base next)
    {L : Nat} (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + bs.length < U.toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (bs.length + 1)).state).fst : Nat) = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (bs.length + 1)).head : Nat)
          = (c0.head : Nat) + bs.length
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (bs.length + 1)).tape
          = writeBlockTape c0.tape (c0.head : Nat) bs := by
  obtain ⟨hph, hhd, htp⟩ := run_writeBits_writing hUP c0 hphase hroom bs.length (le_refl _)
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := U.toPhased.toTM) c0 bs.length with hc
  have hij : (c.state.fst : Nat) = base + ((writeBits bs).acceptPhase : Nat) := by
    rw [hph]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_accept_phase c rfl hij
  · rw [hUP.stepConfig_accept_head c rfl hij]
    exact hhd
  · rw [hUP.stepConfig_accept_tape c rfl hij]
    funext q
    rw [htp q]
    unfold writeBlockTape
    split_ifs <;> rfl

end RegionEmbedded

end ContractExpansion
end Frontier
end Pnp4
