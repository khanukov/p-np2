import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushDrain
import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushEpilogue

/-!
# `valuePushProgram` — D2t-6b (M1 / A5m-V, headline): value-push correctness

The capstone of the value-push machine: from the start contract `ValuePushStart`, the machine
reaches its sink (phase `80`) parked on the home anchor, with the tape equal to the start tape with
the value entry `encodeNatEntryR k = 0·1^(k+2)` written at `vend + 1` — **and nothing else changed**
(the shadow count is drained and rebuilt back in place, so it is byte-for-byte restored).

`valuePush_correct` composes the five run phases —
`valuePush_prehop → valuePush_drain → valuePush_drain_to_reloc → valuePush_relocate →
valuePush_reloc_to_epilogue → valuePush_epilogue` — and reconciles the final tape with the start
tape cell by cell: outside the entry block everything is restored (the corridor, the shadow source,
the work cells, and everything the loops never touch), and the entry block carries exactly the
`k + 2` ones of `encodeNatEntryR k`.

This is the `A5m-V` deliverable consumed by the leaf/const/pop keystones (the `writeBlockTape`
image they demand), unblocking M2/M3/M4.

**Progress classification (AGENTS.md): Infrastructure** — the value-push machine's headline run
lemma; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 2000000 in
/-- **Value-push correctness.**  From the start contract, the machine reaches the sink (phase `80`,
head on the home anchor) with the value entry `encodeNatEntryR k` written at `vend + 1` and the rest
of the tape (in particular the shadow count) restored. -/
theorem valuePush_correct {L : Nat}
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k : Nat) (hstart : ValuePushStart c0 vend shwBase k) :
    ∃ T : Nat,
      T ≤ (2 * shwBase + 10) + (k * (2 * shwBase + 2 * k + 38)
            + (3 + (k * 15 + (5 + (2 * shwBase + 12)))))
      ∧ (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).state).fst : Nat) = 80
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).head : Nat) = shwBase
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).tape
          = writeBlockTape c0.tape (vend + 1) (encodeNatEntryR k) := by
  have hvpos := hstart.hvpos
  have hD := hstart.hD
  -- Phase 1: pre-hop.
  obtain ⟨T1, hT1, layA, untA⟩ := valuePush_prehop c0 vend shwBase k hstart
  set cA := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T1 with hcA
  -- Phase 2: drain.
  obtain ⟨T2, hT2, layB, untB⟩ := valuePush_drain cA vend shwBase k 0 layA
  set cB := TM.runConfig (M := valuePushProgram.toPhased.toTM) cA T2 with hcB
  -- Phase 3: route into relocate.
  obtain ⟨T3, hT3, locC, untC⟩ := valuePush_drain_to_reloc cB vend shwBase k layB
  set cC := TM.runConfig (M := valuePushProgram.toPhased.toTM) cB T3 with hcC
  -- Phase 4: relocate.
  obtain ⟨T4, hT4, locD, untD⟩ := valuePush_relocate cC shwBase k 0 locC
  set cD := TM.runConfig (M := valuePushProgram.toPhased.toTM) cC T4 with hcD
  -- The value entry and right corridor survive into cD (both lie left of the shadow anchor).
  have hentryD : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      vend + 2 ≤ (p : Nat) → (p : Nat) < vend + 3 + k → cD.tape p = true := by
    intro p hp1 hp2
    rw [untD p (by omega), untC p]
    exact layB.hentry p hp1 hp2
  have hcorrD : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      vend + 3 + k ≤ (p : Nat) → (p : Nat) < shwBase → cD.tape p = false := by
    intro p hp1 hp2
    rw [untD p (by omega), untC p]
    exact layB.hcorr p hp1 hp2
  -- Phase 5: route into the epilogue.
  obtain ⟨T5, hT5, epiE, untE⟩ :=
    valuePush_reloc_to_epilogue cD vend shwBase k locD hvpos hD hentryD hcorrD
  set cE := TM.runConfig (M := valuePushProgram.toPhased.toTM) cD T5 with hcE
  -- Phase 6: epilogue.
  obtain ⟨T6, hT6, hph6, hhd6, htape6⟩ := valuePush_epilogue cE vend shwBase k epiE
  set cF := TM.runConfig (M := valuePushProgram.toPhased.toTM) cE T6 with hcF
  -- Compose the six phases.
  have hcompose : TM.runConfig (M := valuePushProgram.toPhased.toTM) c0
      (T1 + (T2 + (T3 + (T4 + (T5 + T6))))) = cF := by
    rw [TM.runConfig_add, ← hcA]
    rw [TM.runConfig_add, ← hcB]
    rw [TM.runConfig_add, ← hcC]
    rw [TM.runConfig_add, ← hcD]
    rw [TM.runConfig_add, ← hcE]
  -- `cE` agrees with `c0` everywhere outside the entry block `[vend+2, vend+3+k)`.
  have hErest : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ((p : Nat) < vend + 2 ∨ vend + 3 + k ≤ (p : Nat)) → cE.tape p = c0.tape p := by
    intro p hp
    rcases hp with hlt | hge
    · -- left of the entry: pure untouched chain
      rw [untE p, untD p (by omega), untC p, untB p (by omega), untA p (by omega)]
    · rcases Nat.lt_or_ge (p : Nat) (shwBase + k + 3) with hsmall | hbig
      · -- the shadow region: compare the epilogue layout with the start layout
        rcases Nat.lt_or_ge (p : Nat) shwBase with hcorr | hsh
        · rw [epiE.hcorrR p (by omega) hcorr, hstart.hcorr p (by omega) hcorr]
        · rcases Nat.lt_or_ge (p : Nat) (shwBase + k + 1) with hsrc | hwork
          · rw [epiE.hsrcAll p hsh hsrc]
            rcases Nat.lt_or_ge (p : Nat) (shwBase + 1) with h0 | h1
            · rw [hstart.hanchor p (by omega)]
            · rw [hstart.hsrc p (by omega) (by omega)]
          · rw [epiE.hwork3 p (by omega) (by omega), hstart.hgap p (by omega) (by omega)]
      · -- right of the shadow terminator: pure untouched chain
        rw [untE p, untD p (by omega), untC p, untB p (by omega), untA p (by omega)]
  refine ⟨T1 + (T2 + (T3 + (T4 + (T5 + T6)))),
    Nat.add_le_add hT1 (Nat.add_le_add hT2 (Nat.add_le_add hT3
      (Nat.add_le_add hT4 (Nat.add_le_add hT5 hT6)))), ?_, ?_, ?_⟩
  · rw [hcompose]; exact hph6
  · rw [hcompose]; exact hhd6
  · rw [hcompose, htape6]
    funext p
    have hlen : (encodeNatEntryR k).length = k + 3 := encodeNatEntryR_length k
    by_cases hwrite : (p : Nat) = vend + 3 + k
    · -- the entry's last one (written by the epilogue)
      rw [writeBlockTape_singleton_eq _ _ _ _ hwrite]
      unfold writeBlockTape
      rw [if_pos (by rw [hlen]; omega)]
      have hidx : (p : Nat) - (vend + 1) = (k + 1) + 1 := by omega
      rw [hidx]
      have hb : k + 1 < k + 2 := by omega
      simp only [encodeNatEntryR, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_replicate, hb, if_true, Option.getD_some]
    · rw [writeBlockTape_singleton_ne _ _ _ _ hwrite]
      by_cases hin : vend + 2 ≤ (p : Nat) ∧ (p : Nat) < vend + 3 + k
      · -- the entry block built during the run
        rw [epiE.hentry p hin.1 hin.2]
        unfold writeBlockTape
        rw [if_pos (by rw [hlen]; omega)]
        obtain ⟨j, hj⟩ : ∃ j, (p : Nat) - (vend + 1) = j + 1 := ⟨(p : Nat) - (vend + 2), by omega⟩
        rw [hj]
        have hb : j < k + 2 := by omega
        simp only [encodeNatEntryR, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
          List.getElem?_replicate, hb, if_true, Option.getD_some]
      · -- everything else: restored to the start tape
        rw [hErest p (by omega)]
        unfold writeBlockTape
        by_cases hframe : (p : Nat) = vend + 1
        · rw [if_pos (by rw [hlen]; omega), hstart.hcorr p (by omega) (by omega)]
          have hz : (p : Nat) - (vend + 1) = 0 := by omega
          rw [hz]
          simp [encodeNatEntryR]
        · rw [if_neg (by rw [hlen]; omega)]

end ContractExpansion
end Frontier
end Pnp4
