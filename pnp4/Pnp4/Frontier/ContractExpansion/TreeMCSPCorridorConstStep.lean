import Pnp4.Frontier.ContractExpansion.TreeMCSPCursorStep
import Pnp4.Frontier.ContractExpansion.TreeMCSPEmitTape
import Pnp4.Frontier.ContractExpansion.TreeMCSPValPush

/-!
# The const-leaf keystone — D2t-5b (Block A4a): `DriveState.step`'s `const` branch on tape

The `const b` reading arm touches three **disjoint** tape regions: the cursor area (consume the
4-cell token `[0,0,1,b]`, replant the marker — `cursorStepTape`), the output region (count `++`,
append the record `[1,0,b]` at `FM`, replant `FM` — `emitTape`), and the value zone (push the WORK
index `out.length` — `writeBlockTape`/`valPush`).  `constStepTape` composes those three proven
transformers, and `corridorInv_constStep` proves it re-establishes `driverCorridorInv` for the stepped
state `⟨toks', out ++ [const b], ctrl, out.length :: val, true⟩` — the on-tape realisation of
`DriveState.step`'s `leaf (const b)` branch, invariant preserved clause by clause (each routed to the
region whose transformer touches it; the other two transformers are the identity there).

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- `emitTape` is the identity off the count cell `oc − 1`, the record window `[fm, fm + |rec|)`, and
the new frontier `fm + |rec|`. -/
theorem emitTape_off {L : Nat} (tape : Fin L → Bool) (oc fm : Nat) (rec : List Bool) (q : Fin L)
    (h1 : (q : Nat) ≠ oc - 1) (h2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (h3 : (q : Nat) ≠ fm + rec.length) : emitTape tape oc fm rec q = tape q := by
  unfold emitTape
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- The const-leaf tape transformer: value push (innermost), output emit (middle), cursor-marker
update (outermost), on three disjoint regions; `cur` is the (token-list-dependent) cursor. -/
def constStepTape {n L : Nat} (z : DriverCorridor) (out : List (SLGate n)) (val : List Nat)
    (b : Bool) (cur : Nat) (tape : Fin L → Bool) : Fin L → Bool :=
  cursorStepTape
    (emitTape
      (writeBlockTape tape (z.valBase + (encodeNatStackR val).length) (encodeNatEntryR out.length))
      (z.workBase - 1 - out.length)
      (z.workBase + (encodeGateRecordStream out).length)
      (encodeGateRecord (SLGate.const b : SLGate n)))
    cur 4

/-- **The const-leaf keystone.**  For a reading state whose next token is `leaf (const b)` (tail
nonempty), with room for the grown count/record (output) and the pushed index (value zone), the
`constStepTape` re-establishes `driverCorridorInv` for the stepped state. -/
theorem corridorInv_constStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (b : Bool) (toks' : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨PreToken.leaf (SLGate.const b) :: toks', out, ctrl, val, false⟩ : DriveState n))
    (htoks : toks' ≠ [])
    (hocap : z.outBase + out.length + 1 + 1 ≤ z.workBase)
    (hwcap : z.workBase + (encodeGateRecordStream out).length
        + (encodeGateRecord (SLGate.const b)).length + 1 ≤ z.workEnd)
    (hvcap : z.valBase + (encodeNatStackR val).length + (encodeNatEntryR out.length).length
        ≤ z.valEnd) :
    driverCorridorInv width h_width z
      (constStepTape z out val b
        (z.certEnd - (encodePreorder width h_width
          (PreToken.leaf (SLGate.const b) :: toks')).length) tape)
      (⟨toks', out ++ [SLGate.const b], ctrl, out.length :: val, true⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hwf
  replace hcert : windowSpells tape
      (z.certEnd - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length)
      (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')) := hcert
  replace hcfit : z.certBase
      + (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length
        ≤ z.certEnd := hcfit
  replace hmark : ∀ p : Fin L, (p : Nat) = z.certEnd
      - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length - 1 →
      tape p = true := hmark
  replace hcorr : ∀ p : Fin L, z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd
        - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length - 1 →
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
  replace hval : windowSpells tape z.valBase (encodeNatStackR val) := hval
  replace hvfit : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
  replace hvzeros : ∀ p : Fin L, z.valBase + (encodeNatStackR val).length ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → tape p = false := hvzeros
  replace hctrl : windowSpells tape z.ctrlBase (encodeCtrlStackR ctrl) := hctrl
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ z.ctrlEnd := hcfit2
  -- Abbreviations for the three transformers' parameters.
  set cur := z.certEnd - (encodePreorder width h_width
    (PreToken.leaf (SLGate.const b) :: toks')).length with hcur
  set vtop := z.valBase + (encodeNatStackR val).length with hvtop
  set ventry := encodeNatEntryR out.length with hventry
  set oc := z.workBase - 1 - out.length with hoc
  set fm := z.workBase + (encodeGateRecordStream out).length with hfm
  set rec := encodeGateRecord (SLGate.const b) with hrec
  set t1 := writeBlockTape tape vtop ventry with ht1
  set t2 := emitTape t1 oc fm rec with ht2
  -- geometry / lengths
  have hreclen : rec.length = 3 := by rw [hrec]; rfl
  have hventrylen : ventry.length = out.length + 3 := by
    rw [hventry, encodeNatEntryR_length]
  have hnatlen : (encodeNatStackR val).length ≤ z.valEnd - z.valBase := by omega
  have hbits : encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')
      = [false, false, true, b] ++ encodePreorder width h_width toks' := by
    rw [encodePreorder_cons]; rfl
  have htag4 : (encodePreToken width h_width (PreToken.leaf (SLGate.const b))).length = 4 := rfl
  have htail1 : 1 ≤ (encodePreorder width h_width toks').length := by
    have hv : ValidCertTokens toks' := fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
    have := validCertTokens_length_le width h_width hv
    have : 1 ≤ toks'.length := by cases toks' with
      | nil => exact absurd rfl htoks
      | cons a l => simp
    omega
  have hlenc : (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length
      = 4 + (encodePreorder width h_width toks').length := by
    rw [hbits, List.length_append]; rfl
  -- cursor area is far right: cur ≥ certBase ≥ ctrlEnd + 3 > val/out regions.
  have hcurge : z.ctrlEnd + 2 < cur := by rw [hcur]; omega
  -- t1 = tape off the value block [vtop, vtop+|ventry|).
  have ht1_below : ∀ q : Fin L, (q : Nat) < vtop → t1 q = tape q := fun q hq =>
    writeBlockTape_below tape vtop ventry q hq
  have ht1_above : ∀ q : Fin L, vtop + ventry.length ≤ (q : Nat) → t1 q = tape q := fun q hq =>
    writeBlockTape_above tape vtop ventry q hq
  -- t2 = t1 off the emit cells (oc-1, [fm,fm+|rec|), fm+|rec|).
  have ht2_off : ∀ q : Fin L, (q : Nat) ≠ oc - 1 →
      ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length) → (q : Nat) ≠ fm + rec.length →
      t2 q = t1 q := fun q h1' h2' h3' => emitTape_off t1 oc fm rec q h1' h2' h3'
  -- The output region (≤ workEnd) and cursor region (> ctrlEnd) bracket everything.
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  -- The cursor clauses (1–4) via cursorStepTape_cert on t2, with t2 = tape on cert + corridor.
  · -- 1. cert suffix window
    have hcertt2 : windowSpells t2 cur
        (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')) := by
      refine windowSpells_congr t2 tape cur _ hcert (fun q hlo hhi => ?_)
      rw [ht2_off q (by omega) (by rw [hfm]; omega) (by rw [hfm]; omega),
        ht1_above q (by rw [hvtop, hventrylen]; omega)]
    obtain ⟨hc1, _, _, _⟩ := cursorStepTape_cert width h_width t2 z.certEnd
      (z.ctrlBase + (encodeCtrlStackR ctrl).length) 4 (PreToken.leaf (SLGate.const b)) toks'
      htag4 (by omega) (by rw [← hcur]; omega) (by rw [← hcur]; exact hcertt2)
      (by rw [← hcur]; omega)
      (fun q hlo hhi => by
        rw [ht2_off q (by rw [← hcur] at hhi; omega) (by rw [hfm]; omega)
            (by rw [hfm]; omega),
          ht1_above q (by rw [hvtop, hventrylen]; omega)]
        exact hcorr q hlo (by rw [← hcur] at hhi ⊢; omega))
    show windowSpells (constStepTape z out val b cur tape)
      (z.certEnd - (encodePreorder width h_width toks').length)
      (encodePreorder width h_width toks')
    rw [show z.certEnd - (encodePreorder width h_width toks').length = cur + 4 from by
      rw [hcur]; omega]
    exact hc1
  · -- 2. cert fit
    show z.certBase + (encodePreorder width h_width toks').length ≤ z.certEnd
    omega
  · -- 3. new marker
    intro p hp
    have hpp : (p : Nat) = cur + 4 - 1 := by rw [hcur] at hp ⊢; omega
    show constStepTape z out val b cur tape p = true
    unfold constStepTape
    unfold cursorStepTape
    rw [if_pos (by rw [← ht1, ← ht2]; omega)]
  · -- 4. consumed/dead corridor
    intro p hlo hhi
    show constStepTape z out val b cur tape p = false
    have hhi' : (p : Nat) < cur + 4 - 1 := by rw [hcur] at hhi ⊢; omega
    unfold constStepTape
    unfold cursorStepTape
    rw [← ht1, ← ht2]
    rw [if_neg (by omega)]
    by_cases hband : cur - 1 ≤ (p : Nat) ∧ (p : Nat) < cur + 4 - 1
    · rw [if_pos hband]
    · rw [if_neg hband]
      rw [ht2_off p (by omega) (by rw [hfm]; omega) (by rw [hfm]; omega),
        ht1_above p (by rw [hvtop, hventrylen]; omega)]
      exact hcorr p hlo (by rw [hcur]; omega)
  -- The output clauses (5–9) via emitTape on t1, lifted through cursorStepTape (identity on output).
  · -- 5. output window
    have ht1out : windowSpells t1 (z.workBase - 1 - out.length)
        (unaryField out.length ++ encodeGateRecordStream out) := by
      refine windowSpells_congr t1 tape _ _ hout (fun q hlo hhi => ?_)
      apply ht1_below
      have := hout.1; rw [hvtop]; omega
    have hemit := emitTape_output_window t1 (z.workBase - 1 - out.length) out (SLGate.const b)
      (by omega) ht1out (by rw [List.length_append, unaryField_length]) (by
        rw [List.length_append, unaryField_length]; omega)
    show windowSpells (constStepTape z out val b cur tape)
      (z.workBase - 1 - (out ++ [SLGate.const b]).length)
      (unaryField (out ++ [SLGate.const b]).length
        ++ encodeGateRecordStream (out ++ [SLGate.const b]))
    rw [List.length_append, List.length_singleton]
    refine windowSpells_congr _ t2 _ _ ?_ (fun q hlo hhi => ?_)
    · -- t2 = emitTape t1 ... is exactly the emit window (oc anchor); reconcile oc = workBase-1-|out|
      have : z.workBase - 1 - out.length - 1 + 1 = z.workBase - 1 - out.length := by omega
      rw [ht2]
      have hrw : (z.workBase - 1 - out.length)
          + (unaryField out.length ++ encodeGateRecordStream out).length
          = fm := by rw [hfm, List.length_append, unaryField_length]; omega
      have := hemit
      rw [hoc, ← hfm] at this
      rw [show out.length + 1 = out.length + 1 from rfl]
      convert this using 2 <;> omega
    · -- lift through cursorStepTape (cursor band is right of the output window)
      show constStepTape z out val b cur tape q = t2 q
      unfold constStepTape
      apply cursorStepTape_off
      · have := hemit.1; rw [hoc] at this; omega
      · have := hemit.1; rw [hoc] at this
        refine fun hb => ?_
        rw [List.length_append, unaryField_length] at hhi
        omega
  · -- 6. output left fit
    show z.outBase + (out ++ [SLGate.const b]).length + 1 ≤ z.workBase
    rw [List.length_append, List.length_singleton]; omega
  · -- 7. new frontier marker
    intro p hp
    have hrecstream : (encodeGateRecordStream (out ++ [SLGate.const b])).length
        = (encodeGateRecordStream out).length + rec.length := by
      have : encodeGateRecordStream (out ++ [SLGate.const b])
          = encodeGateRecordStream out ++ rec := by
        rw [hrec]
        induction out with
        | nil => simp [encodeGateRecordStream]
        | cons a l ih => simp only [List.cons_append, encodeGateRecordStream, ih, List.append_assoc]
      rw [this, List.length_append]
    show constStepTape z out val b cur tape p = true
    rw [hrecstream] at hp
    unfold constStepTape
    rw [← ht1, ← ht2]
    rw [cursorStepTape_off _ _ _ p (by rw [← ht1, ← ht2] at *; omega) (by
      refine fun hb => ?_; omega)]
    rw [ht2]
    exact emitTape_FM t1 oc fm rec (by rw [hoc, hfm]; omega) p (by rw [hfm]; omega)
  · -- 8. frontier fit
    have hrecstream : (encodeGateRecordStream (out ++ [SLGate.const b])).length
        = (encodeGateRecordStream out).length + rec.length := by
      have : encodeGateRecordStream (out ++ [SLGate.const b])
          = encodeGateRecordStream out ++ rec := by
        rw [hrec]
        induction out with
        | nil => simp [encodeGateRecordStream]
        | cons a l ih => simp only [List.cons_append, encodeGateRecordStream, ih, List.append_assoc]
      rw [this, List.length_append]
    show z.workBase + (encodeGateRecordStream (out ++ [SLGate.const b])).length + 1 ≤ z.workEnd
    rw [hrecstream, hreclen]; rw [hreclen] at hwcap; omega
  · -- 9. FM→val dead corridor (the cells past the new FM up to valBase, untouched)
    intro p hlo hhi
    have hrecstream : (encodeGateRecordStream (out ++ [SLGate.const b])).length
        = (encodeGateRecordStream out).length + rec.length := by
      have : encodeGateRecordStream (out ++ [SLGate.const b])
          = encodeGateRecordStream out ++ rec := by
        rw [hrec]
        induction out with
        | nil => simp [encodeGateRecordStream]
        | cons a l ih => simp only [List.cons_append, encodeGateRecordStream, ih, List.append_assoc]
      rw [this, List.length_append]
    rw [hrecstream] at hlo
    show constStepTape z out val b cur tape p = false
    unfold constStepTape
    rw [← ht1, ← ht2]
    rw [cursorStepTape_off _ _ _ p (by omega) (by refine fun hb => ?_; omega)]
    rw [ht2_off p (by rw [hoc]; omega) (by rw [hfm, hreclen] at hlo ⊢; omega)
      (by rw [hfm, hreclen] at hlo ⊢; omega)]
    rw [ht1_above p (by rw [hvtop, hventrylen]; omega)]
    exact hfzeros p (by omega) hhi
  -- The value clauses (10–12).
  · -- 10. value window
    show windowSpells (constStepTape z out val b cur tape) z.valBase
      (encodeNatStackR (out.length :: val))
    have hvw := valPush_window tape z.valBase out.length val hval (by rw [hventry] at hvcap; omega)
    rw [← hvtop, ← hventry, ← ht1] at hvw
    refine windowSpells_congr _ t1 _ _ hvw (fun q hlo hhi => ?_)
    show constStepTape z out val b cur tape q = t1 q
    have hqval : (q : Nat) < z.valEnd := by
      have := hvw.1; rw [encodeNatStackR_cons, List.length_append] at this
      omega
    unfold constStepTape
    rw [cursorStepTape_off _ _ _ q (by omega) (by refine fun hb => ?_; omega)]
    exact ht2_off q (by rw [hoc]; omega) (by rw [hfm]; omega) (by rw [hfm]; omega)
  · -- 11. value fit
    show z.valBase + (encodeNatStackR (out.length :: val)).length ≤ z.valEnd
    rw [encodeNatStackR_cons, List.length_append]
    rw [hventry, encodeNatEntryR_length] at hvcap
    rw [encodeNatEntryR_length]; omega
  · -- 12. val→ctrl dead corridor
    intro p hlo hhi
    rw [encodeNatStackR_cons, List.length_append] at hlo
    show constStepTape z out val b cur tape p = false
    unfold constStepTape
    rw [cursorStepTape_off _ _ _ p (by omega) (by refine fun hb => ?_; omega)]
    rw [ht2_off p (by rw [hoc]; omega) (by rw [hfm]; omega) (by rw [hfm]; omega)]
    rw [ht1_above p (by rw [hvtop, hventrylen] at hlo ⊢; omega)]
    exact hvzeros p (by omega) hhi
  -- The control clauses (13–14): untouched.
  · -- 13. control window
    refine windowSpells_congr _ tape _ _ hctrl (fun q hlo hhi => ?_)
    have hqc : (q : Nat) < z.ctrlEnd := by have := hctrl.1; omega
    show constStepTape z out val b cur tape q = tape q
    unfold constStepTape
    rw [cursorStepTape_off _ _ _ q (by omega) (by refine fun hb => ?_; omega)]
    rw [ht2_off q (by rw [hoc]; omega) (by rw [hfm]; omega) (by rw [hfm]; omega)]
    exact ht1_above q (by rw [hvtop, hventrylen]; omega)
  · -- 14. control fit
    exact hcfit2
  · -- 15. validity
    exact fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
  · -- 16. settling coherence
    intro _; exact List.cons_ne_nil _ _

end ContractExpansion
end Frontier
end Pnp4
