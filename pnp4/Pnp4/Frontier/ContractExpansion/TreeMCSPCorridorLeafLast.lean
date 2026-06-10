import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorTerminalStep

/-!
# Totality-gap keystones — D2t-5b (Block A5a): the last leaf and the generic flag drop

Assembling the total per-`DriveState.step` tape dispatcher (Block A5) surfaced two gaps in the
keystone layer:

* **The last leaf.**  Every reading keystone (`corridorInv_constStep` / `corridorInv_inputStep` /
  `corridorInv_nodeStep`) requires a **nonempty tail** `toks' ≠ []` — but every valid preorder stream
  *ends* with a leaf, so the driver's final step is a leaf read with `toks' = []`, covered by none of
  them.  `corridorInv_leafStep_last` fills it, **generically over the leaf gate** `g` (covering both
  `const` and `input` at once — the cursor bookkeeping no longer needs the per-token length, only
  `1 ≤ |encodePreToken (leaf g)|`, which `ValidCertTokens` supplies): after the last token the unread
  suffix is empty, the new cursor marker lands on `certEnd − 1`, and the consumed cells join the dead
  corridor.

* **The generic flag drop.**  `DriveState.step`'s settle arm has two residual branches that change
  *only* the `settling` flag: the operand-underflow catch-all (`val` too short for the frame's tag —
  unreachable on real certificates) and the `rem = 0` frame (also unreachable; `0 − 1 = 0` keeps the
  frame).  On tape both are the identity.  `corridorInv_clearFlag` transports the invariant across
  *any* `true → false` flag flip on the same tape (generalising `corridorInv_settleClearStep`, which
  is the `ctrl = []` instance): no clause mentions `settling` except the coherence clause, which
  becomes vacuous.

**Progress classification (AGENTS.md): Infrastructure** — tape-level invariant-preservation keystones
over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The generic flag drop.**  `driverCorridorInv` transports across clearing the `settling` flag on
the same tape, for any stack contents: no region clause mentions the flag, and the settling-coherence
clause becomes vacuous.  (The `ctrl = []` instance is `corridorInv_settleClearStep`; this general form
also covers `DriveState.step`'s unreachable operand-underflow and `rem = 0` settle branches.) -/
theorem corridorInv_clearFlag {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (toks : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨toks, out, ctrl, val, true⟩ : DriveState n)) :
    driverCorridorInv width h_width z tape
      (⟨toks, out, ctrl, val, false⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hctrl, hcfit2, hvalid, _hcoh⟩ := hinv
  dsimp only [driverCorridorInv]
  exact ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hctrl, hcfit2, hvalid, fun hs => by cases hs⟩

/-- **The last-leaf keystone.**  For a reading state whose next token is the **final** token
`leaf g` (empty tail), with output and value-zone capacity, `leafStepTape` (token length
`|encodePreToken (leaf g)|`) re-establishes `driverCorridorInv` for the stepped state: the unread
suffix becomes empty, the new cursor marker lands on `certEnd − 1`, and the consumed token cells join
the dead corridor.  Generic over the leaf gate `g` — covering both `const` and `input` (validity
supplies `1 ≤ |encodePreToken (leaf g)|`). -/
theorem corridorInv_leafStep_last {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (g : SLGate n) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨[PreToken.leaf g], out, ctrl, val, false⟩ : DriveState n))
    (hocap : z.outBase + out.length + 2 ≤ z.workBase)
    (hwcap : z.workBase + (encodeGateRecordStream out).length
        + (encodeGateRecord g).length + 1 ≤ z.workEnd)
    (hvcap : z.valBase + (encodeNatStackR val).length + (out.length + 3) ≤ z.valEnd) :
    driverCorridorInv width h_width z
      (leafStepTape tape
        (z.certEnd - (encodePreorder width h_width [PreToken.leaf g]).length)
        (encodePreToken width h_width (PreToken.leaf g)).length
        (z.valBase + (encodeNatStackR val).length)
        (z.workBase - 1 - out.length)
        (z.workBase + (encodeGateRecordStream out).length)
        (encodeNatEntryR out.length)
        (encodeGateRecord g))
      (⟨[], out ++ [g], ctrl, out.length :: val, true⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hwf
  replace hcert : windowSpells tape
      (z.certEnd - (encodePreorder width h_width [PreToken.leaf g]).length)
      (encodePreorder width h_width [PreToken.leaf g]) := hcert
  replace hcfit : z.certBase
      + (encodePreorder width h_width [PreToken.leaf g]).length ≤ z.certEnd := hcfit
  replace hcorr : ∀ p : Fin L, z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd
        - (encodePreorder width h_width [PreToken.leaf g]).length - 1 →
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
  replace hvalid : ValidCertTokens [PreToken.leaf g] := hvalid
  -- Length facts.
  have htpos : 1 ≤ (encodePreToken width h_width (PreToken.leaf g)).length :=
    validCertToken_one_le_length width h_width (hvalid _ (List.mem_cons_self ..))
  have hlenc : (encodePreorder width h_width [PreToken.leaf g]).length
      = (encodePreToken width h_width (PreToken.leaf g)).length := by
    rw [encodePreorder_cons, encodePreorder_nil, List.append_nil]
  have hventrylen : (encodeNatEntryR out.length).length = out.length + 3 :=
    encodeNatEntryR_length out.length
  have hrecstream := encodeGateRecordStream_snoc out g
  have hlen1 : (out ++ [g]).length = out.length + 1 := by simp
  have hstreamlen : (encodeGateRecordStream (out ++ [g])).length
      = (encodeGateRecordStream out).length + (encodeGateRecord g).length := by
    rw [hrecstream, List.length_append]
  dsimp only [driverCorridorInv]
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  -- 1. cert suffix window (empty suffix: vacuous cells).
  · refine ⟨?_, fun q hlo hhi => ?_⟩
    · simp only [encodePreorder_nil, List.length_nil]
      omega
    · simp only [encodePreorder_nil, List.length_nil, Nat.add_zero] at hlo hhi
      exact absurd hhi (by omega)
  -- 2. cert fit (empty suffix).
  · simp only [encodePreorder_nil, List.length_nil]
    omega
  -- 3. new marker at certEnd - 1 (the consumed token's last cell).
  · intro p hp
    simp only [encodePreorder_nil, List.length_nil, Nat.sub_zero] at hp
    unfold leafStepTape cursorStepTape
    rw [if_pos (by omega)]
  -- 4. consumed/dead corridor up to certEnd - 1.
  · intro p hlo hhi
    simp only [encodePreorder_nil, List.length_nil, Nat.sub_zero] at hhi
    unfold leafStepTape cursorStepTape
    rw [if_neg (by omega)]
    by_cases hband : z.certEnd - (encodePreorder width h_width [PreToken.leaf g]).length - 1
        ≤ (p : Nat)
      ∧ (p : Nat) < z.certEnd - (encodePreorder width h_width [PreToken.leaf g]).length
        + (encodePreToken width h_width (PreToken.leaf g)).length - 1
    · rw [if_pos hband]
    · rw [if_neg hband]
      rw [emitTape_off _ _ _ _ p (by omega) (by omega) (by omega)]
      show writeBlockTape tape _ _ p = false
      unfold writeBlockTape
      rw [if_neg (by rw [hventrylen]; omega)]
      exact hcorr p hlo (by omega)
  -- 5. output window.
  · have hemit := emitTape_output_window tape (z.workBase - 1 - out.length) out g
      (by omega) hout
      (by rw [List.length_append, unaryField_length]; omega)
      (by
        rw [List.length_append, unaryField_length]
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
    rw [List.length_append, unaryField_length, hstreamlen] at hhi
    rw [leafStepTape_eq_emit tape _ _ _ _ _ _ _ q
      (by omega) (by omega) (by rw [hventrylen]; omega)]
  -- 6. output left fit.
  · rw [hlen1]
    omega
  -- 7. new frontier marker.
  · intro p hp
    rw [hstreamlen] at hp
    rw [leafStepTape_eq_emit tape _ _ _ _ _ _ _ p
      (by omega) (by omega) (by rw [hventrylen]; omega)]
    exact emitTape_FM tape _ _ _ (by omega) p (by omega)
  -- 8. frontier fit.
  · rw [hstreamlen]
    omega
  -- 9. FM→val dead corridor.
  · intro p hlo hhi
    rw [hstreamlen] at hlo
    rw [leafStepTape_eq_id tape _ _ _ _ _ _ _ p
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hventrylen]; omega)]
    exact hfzeros p (by omega) hhi
  -- 10. value window.
  · have hvw := valPush_window tape z.valBase out.length val hval
      (by rw [encodeNatEntryR_length]; omega)
    refine windowSpells_congr _ _ _ _ hvw (fun q hlo hhi => ?_)
    rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length] at hhi
    rw [leafStepTape_eq_write tape _ _ _ _ _ _ _ q
      (by omega) (by omega) (by omega) (by omega) (by omega)]
  -- 11. value fit.
  · rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length]
    omega
  -- 12. val→ctrl dead corridor.
  · intro p hlo hhi
    rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length] at hlo
    rw [leafStepTape_eq_id tape _ _ _ _ _ _ _ p
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hventrylen]; omega)]
    exact hvzeros p (by omega) hhi
  -- 13. control window (untouched).
  · refine windowSpells_congr _ _ _ _ hctrl (fun q hlo hhi => ?_)
    have hq : (q : Nat) < z.ctrlEnd := by have := hctrl.1; omega
    rw [leafStepTape_eq_id tape _ _ _ _ _ _ _ q
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hventrylen]; omega)]
  -- 14. control fit.
  · exact hcfit2
  -- 15. validity (empty stream).
  · exact fun t ht => absurd ht (by simp)
  -- 16. settling coherence.
  · intro _; exact List.cons_ne_nil _ _

end ContractExpansion
end Frontier
end Pnp4
