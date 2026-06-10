import Pnp4.Frontier.ContractExpansion.TreeMCSPConstStepTape

/-!
# The const-leaf keystone — D2t-5b (Block A4a, part 2): `DriveState.step`'s `const` branch on tape

`corridorInv_constStep`: applying `constStepTape` (the composed cursor/emit/val-push transformer,
off-factory in `TreeMCSPConstStepTape`) to a tape satisfying `driverCorridorInv` for a reading state
with next token `leaf (const b)` yields a tape satisfying the invariant for the **stepped** state
`⟨toks', out ++ [const b], ctrl, out.length :: val, true⟩` — the on-tape const arm realises
`DriveState.step`'s `const` branch, invariant preserved.  Each of the 16 clauses is routed through one
off-lemma (`constStepTape_eq_*`) and one already-proven core (`cursorStepTape_cert` /
`emitTape_output_window` / `valPush_window`).

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The record stream over a snoc: the new gate's record is appended on the right. -/
theorem encodeGateRecordStream_snoc {n : Nat} (out : List (SLGate n)) (g : SLGate n) :
    encodeGateRecordStream (out ++ [g]) = encodeGateRecordStream out ++ encodeGateRecord g := by
  induction out with
  | nil => simp [encodeGateRecordStream]
  | cons a l ih => simp only [List.cons_append, encodeGateRecordStream, ih, List.append_assoc]

/-- **The const-leaf keystone.**  For a reading state whose next token is `leaf (const b)` (tail
nonempty), with output and value-zone capacity, `constStepTape` re-establishes `driverCorridorInv`
for the stepped state. -/
theorem corridorInv_constStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (b : Bool) (toks' : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨PreToken.leaf (SLGate.const b) :: toks', out, ctrl, val, false⟩ : DriveState n))
    (htoks : toks' ≠ [])
    (hocap : z.outBase + out.length + 2 ≤ z.workBase)
    (hwcap : z.workBase + (encodeGateRecordStream out).length + 4 ≤ z.workEnd)
    (hvcap : z.valBase + (encodeNatStackR val).length + (out.length + 3) ≤ z.valEnd) :
    driverCorridorInv width h_width z
      (constStepTape tape
        (z.certEnd - (encodePreorder width h_width
          (PreToken.leaf (SLGate.const b) :: toks')).length)
        (z.valBase + (encodeNatStackR val).length)
        (z.workBase - 1 - out.length)
        (z.workBase + (encodeGateRecordStream out).length)
        (encodeNatEntryR out.length)
        (encodeGateRecord (SLGate.const b : SLGate n)))
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
  replace hcorr : ∀ p : Fin L, z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd
        - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length - 1 →
      tape p = false := hcorr
  replace hout : windowSpells tape (z.workBase - 1 - out.length)
      (unaryField out.length ++ encodeGateRecordStream out) := hout
  replace hofit : z.outBase + out.length + 1 ≤ z.workBase := hofit
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
  replace hvalid : ValidCertTokens (PreToken.leaf (SLGate.const b) :: toks') := hvalid
  -- Length facts.
  have hreclen : (encodeGateRecord (SLGate.const b : SLGate n)).length = 3 := rfl
  have hventrylen : (encodeNatEntryR out.length).length = out.length + 3 :=
    encodeNatEntryR_length out.length
  have hbits : encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')
      = [false, false, true, b] ++ encodePreorder width h_width toks' := by
    rw [encodePreorder_cons]; rfl
  have htag4 : (encodePreToken width h_width (PreToken.leaf (SLGate.const b))).length = 4 := rfl
  have htail1 : 1 ≤ (encodePreorder width h_width toks').length := by
    have hv : ValidCertTokens toks' := fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
    have := validCertTokens_length_le width h_width hv
    have : 1 ≤ toks'.length := by cases toks' with
      | nil => exact absurd rfl htoks
      | cons a l => simp only [List.length_cons]; omega
    omega
  have hlenc : (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length
      = 4 + (encodePreorder width h_width toks').length := by
    rw [hbits, List.length_append]; rfl
  have hrecstream := encodeGateRecordStream_snoc out (SLGate.const b : SLGate n)
  have hlen1 : (out ++ [(SLGate.const b : SLGate n)]).length = out.length + 1 := by simp
  have hstreamlen : (encodeGateRecordStream (out ++ [(SLGate.const b : SLGate n)])).length
      = (encodeGateRecordStream out).length + 3 := by
    rw [hrecstream, List.length_append, hreclen]
  -- Numeric anchors (plain definitions, no `set`).
  have hcurdef : z.certEnd
      - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length
      + 4 = z.certEnd - (encodePreorder width h_width toks').length := by omega
  -- Region order: oc-1 < fm ≤ fm+3 < workEnd < valBase ≤ vtop < vtop+|ventry| ≤ valEnd < ctrlBase
  --               ≤ ctrl-end ≤ ctrlEnd < cur-1.
  have hsep1 : z.workBase - 1 - out.length - 1 < z.workBase
      + (encodeGateRecordStream out).length := by omega
  have hsepcur : z.ctrlEnd + 2 < z.certEnd
      - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length := by
    omega
  -- Shorthand for the off-side conditions at a cell q in a given region.
  -- (Each clause discharges them by omega from the region bounds.)
  dsimp only [driverCorridorInv]
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  -- 1. cert suffix window (cursor region: constStepTape = cursorStepTape tape).
  · obtain ⟨hc1, _, _, _⟩ := cursorStepTape_cert width h_width tape z.certEnd
      (z.ctrlBase + (encodeCtrlStackR ctrl).length) 4 (PreToken.leaf (SLGate.const b)) toks'
      htag4 (by omega) (by omega) hcert (by omega) hcorr
    rw [show z.certEnd - (encodePreorder width h_width toks').length
        = z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.const b) :: toks')).length + 4 from by omega]
    refine windowSpells_congr _ _ _ _ hc1 (fun q hlo hhi => ?_)
    rw [constStepTape_eq_cursor tape _ _ _ _ _ _ q
      (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
  -- 2. cert fit.
  · omega
  -- 3. new marker.
  · intro p hp
    rw [show (z.certEnd - (encodePreorder width h_width toks').length) - 1
        = z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.const b) :: toks')).length + 4 - 1 from by omega] at hp
    rw [constStepTape_eq_cursor tape _ _ _ _ _ _ p
      (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    unfold cursorStepTape
    rw [if_pos hp]
  -- 4. consumed/dead corridor.
  · intro p hlo hhi
    rw [show (z.certEnd - (encodePreorder width h_width toks').length) - 1
        = z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.const b) :: toks')).length + 4 - 1 from by omega] at hhi
    rw [constStepTape_eq_cursor tape _ _ _ _ _ _ p
      (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    unfold cursorStepTape
    rw [if_neg (by omega)]
    by_cases hband : z.certEnd - (encodePreorder width h_width
        (PreToken.leaf (SLGate.const b) :: toks')).length - 1 ≤ (p : Nat)
      ∧ (p : Nat) < z.certEnd - (encodePreorder width h_width
        (PreToken.leaf (SLGate.const b) :: toks')).length + 4 - 1
    · rw [if_pos hband]
    · rw [if_neg hband]
      exact hcorr p hlo (by omega)
  -- 5. output window (emit region: constStepTape = emitTape tape; reuse the core).
  · have hemit := emitTape_output_window tape (z.workBase - 1 - out.length) out
      (SLGate.const b : SLGate n) (by omega) hout
      (by rw [List.length_append, unaryField_length]; omega)
      (by
        rw [List.length_append, unaryField_length, hreclen]
        have := hval.1
        omega)
    rw [hlen1, show z.workBase - 1 - (out.length + 1)
        = z.workBase - 1 - out.length - 1 from by omega]
    have hocfm : z.workBase - 1 - out.length
        + (unaryField out.length ++ encodeGateRecordStream out).length
        = z.workBase + (encodeGateRecordStream out).length := by
      rw [List.length_append, unaryField_length]; omega
    rw [show z.workBase - 1 - out.length - 1 + 1 = z.workBase - 1 - out.length from by omega,
      hocfm] at hemit
    refine windowSpells_congr _ _ _ _ hemit (fun q hlo hhi => ?_)
    · rw [constStepTape_eq_emit tape _ _ _ _ _ _ q
        (by rw [List.length_append, unaryField_length, hstreamlen] at hhi; omega)
        (by rw [List.length_append, unaryField_length, hstreamlen] at hhi; omega)
        (by rw [List.length_append, unaryField_length, hstreamlen] at hhi
            rw [hventrylen]; omega)]
  -- 6. output left fit.
  · rw [hlen1]
    omega
  -- 7. new frontier marker.
  · intro p hp
    rw [hstreamlen] at hp
    rw [constStepTape_eq_emit tape _ _ _ _ _ _ p
      (by omega) (by omega) (by rw [hventrylen]; omega)]
    exact emitTape_FM tape _ _ _ (by omega) p (by rw [hreclen]; omega)
  -- 8. frontier fit.
  · rw [hstreamlen]
    omega
  -- 9. FM→val dead corridor.
  · intro p hlo hhi
    rw [hstreamlen] at hlo
    rw [constStepTape_eq_id tape _ _ _ _ _ _ p
      (by omega) (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    exact hfzeros p (by omega) hhi
  -- 10. value window (write region: constStepTape = writeBlockTape tape; reuse the core).
  · have hvw := valPush_window tape z.valBase out.length val hval
      (by rw [encodeNatEntryR_length]; omega)
    refine windowSpells_congr _ _ _ _ hvw (fun q hlo hhi => ?_)
    rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length] at hhi
    rw [constStepTape_eq_write tape _ _ _ _ _ _ q
      (by omega) (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)]
  -- 11. value fit.
  · rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length]
    omega
  -- 12. val→ctrl dead corridor.
  · intro p hlo hhi
    rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length] at hlo
    rw [constStepTape_eq_id tape _ _ _ _ _ _ p
      (by omega) (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    exact hvzeros p (by omega) hhi
  -- 13. control window (untouched).
  · refine windowSpells_congr _ _ _ _ hctrl (fun q hlo hhi => ?_)
    have hq : (q : Nat) < z.ctrlEnd := by have := hctrl.1; omega
    rw [constStepTape_eq_id tape _ _ _ _ _ _ q
      (by omega) (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
  -- 14. control fit.
  · exact hcfit2
  -- 15. validity.
  · exact fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
  -- 16. settling coherence.
  · intro _; exact List.cons_ne_nil _ _

end ContractExpansion
end Frontier
end Pnp4
