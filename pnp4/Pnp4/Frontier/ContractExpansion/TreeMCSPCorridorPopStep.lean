import Pnp4.Frontier.ContractExpansion.TreeMCSPValReplaceTop
import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorDecStep

/-!
# The settle-POP-EMIT keystone — D2t-5b (Block A4e): `DriveState.step`'s `rem = 1` branch on tape

The settling arm with a top control frame `(tag, 1)` completes that gate: it pops the gate's operands
off the value stack, appends the gate record to WORK, pops the (now-complete) control frame, and
pushes the new gate's WORK index — staying settling (the new index settles into *its* parent):

```
⟨toks, out, (tag, 1) :: ctrl', vpop ++ vs, true⟩
  → ⟨toks, out ++ [gate], ctrl', out.length :: vs, true⟩
```

(`vpop = [i]` for `tnot`; `vpop = [i₂, i₁]` for `tand`/`tor`; `gate` the corresponding `SLGate`.)

On tape **three disjoint regions** change, all left of the untouched certificate (settling consumes
no token, so the cursor/cert region is unchanged):

* **output (emit):** the leaf-arm emit — grow the unary count one cell left, append `encodeGateRecord
  gate` at the frontier `FM`, replant `FM` (`emitTape`, reused verbatim);
* **value (pop + push):** overwrite the popped operand block `vpop.reverse.flatMap encodeNatEntryR`
  by the new entry `encodeNatEntryR out.length` zero-padded to the popped block's width
  (`valReplaceTop_window`, the A4d core), so the window spells `encodeNatStackR (out.length :: vs)`;
* **control (erase frame):** overwrite the top frame `(tag, 1)`'s cells with `0`s, so the control
  window shrinks to `ctrl'` and the freed cells join the consumed/dead corridor.

`corridorInv_popStep` re-establishes `driverCorridorInv` for the stepped state.  Generic over `tag`,
`gate`, `vpop`, `vs` (the per-`ITag` instances are read off in the A5 assembly).

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### Small list facts -/

/-- `getD` into an all-`false` block is `false` at every index (so the value-pop pad and the
control-erase block both read `false`).  Proved by structural recursion; Mathlib's `getD_replicate`
has a different argument convention, so we keep this local form. -/
theorem getD_replicate_false (m i : Nat) : (List.replicate m false).getD i false = false := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
      cases i with
      | zero => simp [List.replicate_succ]
      | succ i => rw [List.replicate_succ, List.getD_cons_succ]; exact ih i

/-- Right-anchored value-stack split off the bottom: `encodeNatStackR (a ++ b)` shares the suffix
`encodeNatStackR b` and appends `a`'s entries (reversed, bottom-to-top).  The pop core's window
hypothesis (`encodeNatStackR vs ++ oldTop`) is `encodeNatStackR (vpop ++ vs)` read through this. -/
theorem encodeNatStackR_append (a b : List Nat) :
    encodeNatStackR (a ++ b) = encodeNatStackR b ++ a.reverse.flatMap encodeNatEntryR := by
  induction a with
  | nil => simp [encodeNatStackR]
  | cons x xs ih =>
      rw [List.cons_append, encodeNatStackR_cons, ih, List.reverse_cons,
        List.flatMap_append, List.append_assoc]
      simp

/-! ### The composed settle-emit tape transformer and its off-factory -/

/-- The settle-emit tape transformer over explicit anchors: control-frame erase (innermost, block
`cblock` at `cfb`), value pop-then-push (middle, block `vblock` at `pb`), output emit (outermost,
count cell `oc − 1`, record `rec` at `fm`). -/
def popStepTape {L : Nat} (tape : Fin L → Bool) (cfb : Nat) (cblock : List Bool)
    (pb : Nat) (vblock : List Bool) (oc fm : Nat) (rec : List Bool) : Fin L → Bool :=
  emitTape (writeBlockTape (writeBlockTape tape cfb cblock) pb vblock) oc fm rec

/-- Off all three regions, `popStepTape` is the identity. -/
theorem popStepTape_eq_id {L : Nat} (tape : Fin L → Bool) (cfb : Nat) (cblock : List Bool)
    (pb : Nat) (vblock : List Bool) (oc fm : Nat) (rec : List Bool) (q : Fin L)
    (he1 : (q : Nat) ≠ oc - 1) (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length)
    (hv : ¬ (pb ≤ (q : Nat) ∧ (q : Nat) < pb + vblock.length))
    (hc : ¬ (cfb ≤ (q : Nat) ∧ (q : Nat) < cfb + cblock.length)) :
    popStepTape tape cfb cblock pb vblock oc fm rec q = tape q := by
  unfold popStepTape
  rw [emitTape_off _ _ _ _ q he1 he2 he3]
  unfold writeBlockTape
  rw [if_neg hv, if_neg hc]

/-- On the output region, `popStepTape` is `emitTape` of the original tape. -/
theorem popStepTape_eq_emit {L : Nat} (tape : Fin L → Bool) (cfb : Nat) (cblock : List Bool)
    (pb : Nat) (vblock : List Bool) (oc fm : Nat) (rec : List Bool) (q : Fin L)
    (hv : ¬ (pb ≤ (q : Nat) ∧ (q : Nat) < pb + vblock.length))
    (hc : ¬ (cfb ≤ (q : Nat) ∧ (q : Nat) < cfb + cblock.length)) :
    popStepTape tape cfb cblock pb vblock oc fm rec q = emitTape tape oc fm rec q := by
  unfold popStepTape emitTape
  by_cases hq1 : (q : Nat) = oc - 1
  · rw [if_pos hq1, if_pos hq1]
  · rw [if_neg hq1, if_neg hq1]
    by_cases hq2 : fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length
    · rw [if_pos hq2, if_pos hq2]
    · rw [if_neg hq2, if_neg hq2]
      by_cases hq3 : (q : Nat) = fm + rec.length
      · rw [if_pos hq3, if_pos hq3]
      · rw [if_neg hq3, if_neg hq3]
        unfold writeBlockTape
        rw [if_neg hv, if_neg hc]

/-- On the value block, `popStepTape` is the value `writeBlockTape` of the original tape. -/
theorem popStepTape_eq_valwrite {L : Nat} (tape : Fin L → Bool) (cfb : Nat) (cblock : List Bool)
    (pb : Nat) (vblock : List Bool) (oc fm : Nat) (rec : List Bool) (q : Fin L)
    (he1 : (q : Nat) ≠ oc - 1) (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length)
    (hc : ¬ (cfb ≤ (q : Nat) ∧ (q : Nat) < cfb + cblock.length)) :
    popStepTape tape cfb cblock pb vblock oc fm rec q = writeBlockTape tape pb vblock q := by
  unfold popStepTape
  rw [emitTape_off _ _ _ _ q he1 he2 he3]
  unfold writeBlockTape
  by_cases hq : pb ≤ (q : Nat) ∧ (q : Nat) < pb + vblock.length
  · rw [if_pos hq, if_pos hq]
  · rw [if_neg hq, if_neg hq, if_neg hc]

/-- On the control block, `popStepTape` is the control `writeBlockTape` of the original tape. -/
theorem popStepTape_eq_ctrlwrite {L : Nat} (tape : Fin L → Bool) (cfb : Nat) (cblock : List Bool)
    (pb : Nat) (vblock : List Bool) (oc fm : Nat) (rec : List Bool) (q : Fin L)
    (he1 : (q : Nat) ≠ oc - 1) (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length)
    (hv : ¬ (pb ≤ (q : Nat) ∧ (q : Nat) < pb + vblock.length)) :
    popStepTape tape cfb cblock pb vblock oc fm rec q = writeBlockTape tape cfb cblock q := by
  unfold popStepTape
  rw [emitTape_off _ _ _ _ q he1 he2 he3]
  unfold writeBlockTape
  rw [if_neg hv]

/-! ### The keystone -/

/-- **The settle-pop-emit keystone.**  For a settling state whose top control frame is `(tag, 1)`,
with output / value-zone / shadow-count capacity, `popStepTape` (emit `encodeGateRecord gate`, pop
`vpop` and push `out.length` on the value stack, erase the top control frame) followed by the
**shadow-count tick** re-establishes `driverCorridorInv` for the stepped state
`⟨toks, out ++ [gate], ctrl', out.length :: vs, true⟩`. -/
theorem corridorInv_popStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (tag : ITag) (gate : SLGate n) (vpop vs : List Nat)
    (toks : List (PreToken n)) (out : List (SLGate n)) (ctrl' : List (ITag × Nat))
    (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨toks, out, (tag, 1) :: ctrl', vpop ++ vs, true⟩ : DriveState n))
    (hocap : z.outBase + out.length + 2 ≤ z.workBase)
    (hwcap : z.workBase + (encodeGateRecordStream out).length
        + (encodeGateRecord gate).length + 1 ≤ z.workEnd)
    (hvcap : z.valBase + (encodeNatStackR vs).length + (out.length + 3) ≤ z.valEnd)
    (hscap : z.shwBase + out.length + 2 ≤ z.shwEnd) :
    driverCorridorInv width h_width z
      (writeBlockTape
        (popStepTape tape
          (z.ctrlBase + (encodeCtrlStackR ctrl').length)
          (List.replicate (encodeCtrlFrameR (tag, 1)).length false)
          (z.valBase + (encodeNatStackR vs).length)
          (encodeNatEntryR out.length
            ++ List.replicate ((vpop.reverse.flatMap encodeNatEntryR).length - (out.length + 3)) false)
          (z.workBase - 1 - out.length)
          (z.workBase + (encodeGateRecordStream out).length)
          (encodeGateRecord gate))
        (z.shwBase + out.length + 1) [true])
      (⟨toks, out ++ [gate], ctrl', out.length :: vs, true⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hwf
  replace hcert : windowSpells tape
      (z.certEnd - (encodePreorder width h_width toks).length)
      (encodePreorder width h_width toks) := hcert
  replace hcfit : z.certBase + (encodePreorder width h_width toks).length ≤ z.certEnd := hcfit
  replace hmark : ∀ p : Fin L,
      (p : Nat) = z.certEnd - (encodePreorder width h_width toks).length - 1 → tape p = true := hmark
  replace hcorr : ∀ p : Fin L,
      z.ctrlBase + (encodeCtrlStackR ((tag, 1) :: ctrl')).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width toks).length - 1 →
      tape p = false := hcorr
  replace hout : windowSpells tape (z.workBase - 1 - out.length)
      (unaryField out.length ++ encodeGateRecordStream out) := hout
  replace hofit : z.outBase + out.length + 1 ≤ z.workBase := hofit
  replace hFM : ∀ p : Fin L,
      (p : Nat) = z.workBase + (encodeGateRecordStream out).length → tape p = true := hFM
  replace hffit : z.workBase + (encodeGateRecordStream out).length + 1 ≤ z.workEnd := hffit
  replace hfzeros : ∀ p : Fin L,
      z.workBase + (encodeGateRecordStream out).length + 1 ≤ (p : Nat) →
      (p : Nat) < z.valBase → tape p = false := hfzeros
  replace hval : windowSpells tape z.valBase (encodeNatStackR (vpop ++ vs)) := hval
  replace hvfit : z.valBase + (encodeNatStackR (vpop ++ vs)).length ≤ z.valEnd := hvfit
  replace hvzeros : ∀ p : Fin L, z.valBase + (encodeNatStackR (vpop ++ vs)).length ≤ (p : Nat) →
      (p : Nat) < z.shwBase → tape p = false := hvzeros
  replace hshw : windowSpells tape z.shwBase (List.replicate (out.length + 1) true) := hshw
  replace hsfit : z.shwBase + out.length + 1 ≤ z.shwEnd := hsfit
  replace hszeros : ∀ p : Fin L, z.shwBase + out.length + 1 ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → tape p = false := hszeros
  replace hctrl : windowSpells tape z.ctrlBase (encodeCtrlStackR ((tag, 1) :: ctrl')) := hctrl
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ((tag, 1) :: ctrl')).length ≤ z.ctrlEnd := hcfit2
  replace hvalid : ValidCertTokens toks := hvalid
  -- Structure / length facts.
  have hstack_decomp : encodeNatStackR (vpop ++ vs)
      = encodeNatStackR vs ++ vpop.reverse.flatMap encodeNatEntryR := encodeNatStackR_append vpop vs
  have hnewval : encodeNatStackR (out.length :: vs)
      = encodeNatStackR vs ++ encodeNatEntryR out.length := encodeNatStackR_cons out.length vs
  have hrecstream := encodeGateRecordStream_snoc out gate
  have hlen1 : (out ++ [gate]).length = out.length + 1 := by simp
  have hstreamlen : (encodeGateRecordStream (out ++ [gate])).length
      = (encodeGateRecordStream out).length + (encodeGateRecord gate).length := by
    rw [hrecstream, List.length_append]
  have hventrylen : (encodeNatEntryR out.length).length = out.length + 3 :=
    encodeNatEntryR_length out.length
  have hcblocklen : (List.replicate (encodeCtrlFrameR (tag, 1)).length false).length
      = (encodeCtrlFrameR (tag, 1)).length := List.length_replicate ..
  have holdvallen : (encodeNatStackR (vpop ++ vs)).length
      = (encodeNatStackR vs).length + (vpop.reverse.flatMap encodeNatEntryR).length := by
    rw [hstack_decomp, List.length_append]
  have holdctrllen : (encodeCtrlStackR ((tag, 1) :: ctrl')).length
      = (encodeCtrlStackR ctrl').length + (encodeCtrlFrameR (tag, 1)).length := by
    rw [encodeCtrlStackR_cons, List.length_append]
  have hvblocklen : (encodeNatEntryR out.length
        ++ List.replicate ((vpop.reverse.flatMap encodeNatEntryR).length - (out.length + 3)) false).length
      = (out.length + 3) + ((vpop.reverse.flatMap encodeNatEntryR).length - (out.length + 3)) := by
    rw [List.length_append, hventrylen, List.length_replicate]
  -- Derived capacities (old fits, re-expressed for the split stacks).
  have hvfit' : z.valBase + (encodeNatStackR vs).length
      + (vpop.reverse.flatMap encodeNatEntryR).length ≤ z.valEnd := by
    have := hvfit; rw [holdvallen] at this; omega
  have hcfit2' : z.ctrlBase + (encodeCtrlStackR ctrl').length
      + (encodeCtrlFrameR (tag, 1)).length ≤ z.ctrlEnd := by
    have := hcfit2; rw [holdctrllen] at this; omega
  -- Write-region tops (for the off-region transports).
  have hvaltop : z.valBase + (encodeNatStackR vs).length
      + (encodeNatEntryR out.length
        ++ List.replicate ((vpop.reverse.flatMap encodeNatEntryR).length - (out.length + 3)) false).length
      ≤ z.valEnd := by rw [hvblocklen]; omega
  have hctrltop : z.ctrlBase + (encodeCtrlStackR ctrl').length
      + (List.replicate (encodeCtrlFrameR (tag, 1)).length false).length ≤ z.ctrlEnd := by
    rw [hcblocklen]; omega
  -- The shadow-count tick peels: below / above the single written cell.
  have htickB : ∀ (T : Fin L → Bool) (q : Fin L), (q : Nat) < z.shwBase + out.length + 1 →
      writeBlockTape T (z.shwBase + out.length + 1) [true] q = T q :=
    fun T q hq => writeBlockTape_below T _ _ q hq
  have htickA : ∀ (T : Fin L → Bool) (q : Fin L), z.shwBase + out.length + 2 ≤ (q : Nat) →
      writeBlockTape T (z.shwBase + out.length + 1) [true] q = T q := by
    intro T q hq
    apply writeBlockTape_above
    simp only [List.length_singleton]
    omega
  dsimp only [driverCorridorInv]
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. cert suffix window (untouched: cert is right of every write).
  · refine windowSpells_congr _ _ _ _ hcert (fun q hlo hhi => ?_)
    have hqlo : z.certBase ≤ (q : Nat) := by have := hcert.1; omega
    rw [htickA _ q (by omega)]
    exact popStepTape_eq_id tape _ _ _ _ _ _ _ q
      (by omega) (by omega) (by omega) (by omega) (by omega)
  -- 2. cert fit (toks unchanged).
  · exact hcfit
  -- 3. cursor marker (untouched).
  · intro p hp
    rw [htickA _ p (by omega),
      popStepTape_eq_id tape _ _ _ _ _ _ _ p
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hmark p hp
  -- 4. consumed/dead corridor (new ctrl'); freed top-frame cells now read 0.
  · intro p hlo hhi
    rw [htickA _ p (by omega)]
    by_cases hframe : (p : Nat) < z.ctrlBase + (encodeCtrlStackR ctrl').length
        + (encodeCtrlFrameR (tag, 1)).length
    · -- inside the erased frame zone: ctrl write, block all-false.
      rw [popStepTape_eq_ctrlwrite tape _ _ _ _ _ _ _ p
        (by omega) (by omega) (by omega) (by omega)]
      unfold writeBlockTape
      rw [if_pos ⟨by omega, by rw [hcblocklen]; omega⟩]
      exact getD_replicate_false _ _
    · -- at or past the old frame end: untouched, old hcorr.
      rw [popStepTape_eq_id tape _ _ _ _ _ _ _ p
        (by omega) (by omega) (by omega) (by omega) (by rw [hcblocklen]; omega)]
      exact hcorr p (by rw [holdctrllen]; omega) hhi
  -- 5. output window (emit).
  · have hemit := emitTape_output_window tape (z.workBase - 1 - out.length) out gate (by omega) hout
      (by rw [List.length_append, unaryField_length]; omega)
      (by rw [List.length_append, unaryField_length]
          have := hval.1; rw [holdvallen] at this; omega)
    rw [hlen1, show z.workBase - 1 - (out.length + 1)
        = z.workBase - 1 - out.length - 1 from by omega]
    have hocfm : z.workBase - 1 - out.length
        + (unaryField out.length ++ encodeGateRecordStream out).length
        = z.workBase + (encodeGateRecordStream out).length := by
      rw [List.length_append, unaryField_length]; omega
    rw [show z.workBase - 1 - out.length - 1 + 1 = z.workBase - 1 - out.length from by omega,
      hocfm] at hemit
    refine windowSpells_congr _ _ _ _ hemit (fun q hlo hhi => ?_)
    rw [List.length_append, unaryField_length, hstreamlen] at hhi
    rw [htickB _ q (by omega)]
    exact popStepTape_eq_emit tape _ _ _ _ _ _ _ q (by omega) (by omega)
  -- 6. output left fit.
  · rw [hlen1]; omega
  -- 7. new frontier marker.
  · intro p hp
    rw [hstreamlen] at hp
    rw [htickB _ p (by omega),
      popStepTape_eq_emit tape _ _ _ _ _ _ _ p (by omega) (by omega)]
    exact emitTape_FM tape _ _ _ (by omega) p (by omega)
  -- 8. frontier fit.
  · rw [hstreamlen]; omega
  -- 9. FM→val dead corridor.
  · intro p hlo hhi
    rw [hstreamlen] at hlo
    rw [htickB _ p (by omega),
      popStepTape_eq_id tape _ _ _ _ _ _ _ p
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hfzeros p (by omega) hhi
  -- 10. value window (pop + push).
  · have hvw := valReplaceTop_window tape z.valBase vs (vpop.reverse.flatMap encodeNatEntryR)
      out.length (by rw [← hstack_decomp]; exact hval)
      (by rw [encodeNatEntryR_length]; omega)
    rw [hventrylen] at hvw
    refine windowSpells_congr _ _ _ _ hvw (fun q hlo hhi => ?_)
    rw [hnewval, List.length_append, hventrylen] at hhi
    rw [htickB _ q (by omega)]
    exact popStepTape_eq_valwrite tape _ _ _ _ _ _ _ q (by omega) (by omega) (by omega) (by omega)
  -- 11. value fit.
  · rw [hnewval, List.length_append, hventrylen]; omega
  -- 12. val→SHW dead corridor.
  · intro p hlo hhi
    rw [hnewval, List.length_append, hventrylen] at hlo
    rw [htickB _ p (by omega)]
    by_cases hpv : (p : Nat) < z.valBase + (encodeNatStackR vs).length
        + (encodeNatEntryR out.length
          ++ List.replicate ((vpop.reverse.flatMap encodeNatEntryR).length - (out.length + 3)) false).length
    · -- inside the written block, past the new entry: the pad reads 0.
      rw [popStepTape_eq_valwrite tape _ _ _ _ _ _ _ p (by omega) (by omega) (by omega) (by omega)]
      unfold writeBlockTape
      rw [if_pos ⟨by omega, by omega⟩,
        List.getD_append_right _ _ _ _ (by rw [hventrylen]; omega), getD_replicate_false]
    · -- past the written block: untouched, old hvzeros.
      rw [popStepTape_eq_id tape _ _ _ _ _ _ _ p
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hvzeros p (by rw [holdvallen]; omega) hhi
  -- 12a. SHW window: the tick appends one `1` to the spelled `1`-block.
  · rw [hlen1, show List.replicate (out.length + 1 + 1) true
        = List.replicate (out.length + 1) true ++ [true] from List.replicate_succ' ..]
    have hshw' : windowSpells
        (popStepTape tape
          (z.ctrlBase + (encodeCtrlStackR ctrl').length)
          (List.replicate (encodeCtrlFrameR (tag, 1)).length false)
          (z.valBase + (encodeNatStackR vs).length)
          (encodeNatEntryR out.length
            ++ List.replicate ((vpop.reverse.flatMap encodeNatEntryR).length - (out.length + 3)) false)
          (z.workBase - 1 - out.length)
          (z.workBase + (encodeGateRecordStream out).length)
          (encodeGateRecord gate))
        z.shwBase (List.replicate (out.length + 1) true) := by
      refine windowSpells_congr _ _ _ _ hshw (fun q hlo hhi => ?_)
      rw [List.length_replicate] at hhi
      exact popStepTape_eq_id tape _ _ _ _ _ _ _ q
        (by omega) (by omega) (by omega) (by omega) (by omega)
    have happ := windowSpells_writeAppend _ z.shwBase (List.replicate (out.length + 1) true)
      [true] hshw' (by rw [List.length_replicate, List.length_singleton]; omega)
    rw [List.length_replicate,
      show z.shwBase + (out.length + 1) = z.shwBase + out.length + 1 from by omega] at happ
    exact happ
  -- 12b. SHW fit (one tick of room).
  · rw [hlen1]; omega
  -- 12c. SHW→ctrl dead corridor (right of the ticked cell).
  · intro p hlo hhi
    rw [hlen1] at hlo
    rw [htickA _ p (by omega),
      popStepTape_eq_id tape _ _ _ _ _ _ _ p
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hszeros p (by omega) hhi
  -- 13. control window (shrunk to ctrl').
  · have hpre := windowSpells_append_left tape z.ctrlBase (encodeCtrlStackR ctrl')
      (encodeCtrlFrameR (tag, 1)) (by rw [← encodeCtrlStackR_cons]; exact hctrl)
    refine windowSpells_congr _ _ _ _ hpre (fun q hlo hhi => ?_)
    have hqend : (q : Nat) < z.ctrlBase + (encodeCtrlStackR ctrl').length := by
      have := hpre.1; omega
    rw [htickA _ q (by omega)]
    exact popStepTape_eq_id tape _ _ _ _ _ _ _ q
      (by omega) (by omega) (by omega) (by omega) (by omega)
  -- 14. control fit.
  · omega
  -- 15. validity (toks unchanged).
  · exact hvalid
  -- 16. settling coherence.
  · intro _; exact List.cons_ne_nil _ _

end ContractExpansion
end Frontier
end Pnp4
