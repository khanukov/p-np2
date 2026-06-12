import Pnp4.Frontier.ContractExpansion.TreeMCSPConstIterProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPConstWriteChain
import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorRoutes

/-!
# The const iteration, end to end (tail) — D2t-5b (Block A5m-6, run, part 1)

The shared tail of the const-arm run: from the post-record configuration (phase `103`, head one
right of the new frontier marker, tape = the marker and record writes over the home tape), the
machine returns rightward to the value frontier (γ-scan to the value sentinel, walk the value
zone, one step left onto the frontier `vtop`), runs the **whole A5m-V value-push region** (the
entry `0·1^(k+2)` fan-out from the `SHW` source, restored in place), and returns home with the
**`SHW` tick** (cross the entry, γ-scan to `shwBase`, cross `SHW`, write the tick `1`, γ-scan to
the control sentinel, walk the control zone, γ-scan onto the **new** cursor marker) — ending at
the home-read out (phase `168`) with the tape exactly the four-write chain (marker, record, value
entry, tick) over the home tape.  The two `b`-fronts (marker walk, the six leftward legs, the
record write — differing only in phase numbers) both land here; `constIter_run` composes a front
with this tail and rewrites the chain to the keystone transformer via
`writeConstChain_eq_constStepTape`.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine's run; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The const machine's tape length, evaluated. -/
private theorem constIter_len (L : Nat) :
    constIterProgram.toPhased.toTM.tapeLength L = L + (L + 1) + 1 := rfl

/-- Components with `timeBound ≤ n + 1` fit inside the const machine's tape. -/
private theorem hlen_of_le {P : ConstStatePhasedProgram Unit} {L : Nat}
    (h : P.timeBound L ≤ L + 1) :
    P.toPhased.toTM.tapeLength L ≤ constIterProgram.toPhased.toTM.tapeLength L := by
  rw [constIter_len]
  simp only [PhasedProgram.toTM_tapeLength, toPhased_timeBound]
  omega

private theorem walkR_len (L : Nat) :
    zoneWalkRight.toPhased.toTM.tapeLength L = L + L + 1 := rfl

private theorem vpush_len (L : Nat) :
    valuePushProgram.toPhased.toTM.tapeLength L = L + L + 1 := rfl

private theorem sum_map_add_two (ks : List Nat) :
    (ks.map (· + 2)).sum = (ks.map (· + 1)).sum + ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [ih]; omega

private theorem length_le_sum_map_add_one (ks : List Nat) :
    ks.length ≤ (ks.map (· + 1)).sum := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp; omega

/-- The rightward walk budget, bounded by the zone length. -/
theorem walkZoneStepsR_le (ks : List Nat) :
    walkZoneStepsR ks ≤ 2 * (walkZone ks).length + 1 := by
  unfold walkZoneStepsR
  have h1 := walkZone_length ks
  have h2 := sum_map_add_two ks
  have h3 := length_le_sum_map_add_one ks
  omega


private theorem walkL_len (L : Nat) :
    zoneWalkLeft.toPhased.toTM.tapeLength L = L + L + 1 := rfl

private theorem sum_map_add_three (ks : List Nat) :
    (ks.map (· + 3)).sum = (ks.map (· + 1)).sum + 2 * ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [ih]; omega

/-- The leftward walk budget, bounded by the zone length. -/
theorem walkZoneSteps_le (ks : List Nat) :
    walkZoneSteps ks ≤ 3 * (walkZone ks).length := by
  unfold walkZoneSteps
  have h1 := walkZone_length ks
  have h2 := sum_map_add_three ks
  have h3 := length_le_sum_map_add_one ks
  omega

set_option maxHeartbeats 4000000 in
/-- **The const-arm shared tail.**  From phase `103` at `FM + 4` with the marker and record
written, the machine reaches the home-read out (`168`) on the **new** marker with the value entry
and the `SHW` tick written — the four-write chain over the home tape. -/
theorem constIter_run_tail {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (b : Bool) (toks' : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat)
    (tape0 : Fin (constIterProgram.toPhased.toTM.tapeLength L) → Bool)
    (c2 : Configuration (M := constIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z tape0
      (⟨PreToken.leaf (SLGate.const b) :: toks', out, ctrl, val, false⟩ : DriveState n))
    (hrem : ∀ f ∈ ctrl, 1 ≤ f.2)
    (hLfit : z.certEnd + 2 ≤ L)
    (hwcap : z.workBase + (encodeGateRecordStream out).length + 4 ≤ z.workEnd)
    (hvcap : z.valBase + (encodeNatStackR val).length + (out.length + 3) ≤ z.valEnd)
    (hscratch : z.shwBase + 2 * out.length + 2 < z.ctrlBase)
    (htape2 : c2.tape = writeBlockTape
        (writeBlockTape tape0
          (z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.const b) :: toks')).length - 1) constMarkBlock)
        (z.workBase + (encodeGateRecordStream out).length) (constRecBlock b))
    (hphase2 : (c2.state.fst : Nat) = 103)
    (hhead2 : (c2.head : Nat) = z.workBase + (encodeGateRecordStream out).length + 4) :
    ∃ T : Nat,
      T ≤ (out.length + 2) * (2 * z.certEnd + 6 * out.length + 20)
          + 12 * z.certEnd + 8 * out.length + 60
      ∧ (((TM.runConfig (M := constIterProgram.toPhased.toTM) c2 T).state).fst : Nat) = 168
      ∧ ((TM.runConfig (M := constIterProgram.toPhased.toTM) c2 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width toks').length - 1
      ∧ (TM.runConfig (M := constIterProgram.toPhased.toTM) c2 T).tape
          = writeBlockTape
              (writeBlockTape
                (writeBlockTape
                  (writeBlockTape tape0
                    (z.certEnd - (encodePreorder width h_width
                      (PreToken.leaf (SLGate.const b) :: toks')).length - 1) constMarkBlock)
                  (z.workBase + (encodeGateRecordStream out).length) (constRecBlock b))
                (z.valBase + (encodeNatStackR val).length) (encodeNatEntryR out.length))
              (z.shwBase + out.length + 1) [true] := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hFM : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.workBase + (encodeGateRecordStream out).length → tape0 p = true := hFM
  replace hffit : z.workBase + (encodeGateRecordStream out).length + 1 ≤ z.workEnd := hffit
  replace hfzeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      z.workBase + (encodeGateRecordStream out).length + 1 ≤ (p : Nat) →
      (p : Nat) < z.valBase → tape0 p = false := hfzeros
  replace hval : windowSpells tape0 z.valBase (encodeNatStackR val) := hval
  replace hvfit : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
  replace hvzeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      z.valBase + (encodeNatStackR val).length ≤ (p : Nat) →
      (p : Nat) < z.shwBase → tape0 p = false := hvzeros
  replace hshw : windowSpells tape0 z.shwBase (List.replicate (out.length + 1) true) := hshw
  replace hsfit : z.shwBase + out.length + 1 ≤ z.shwEnd := hsfit
  replace hszeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      z.shwBase + out.length + 1 ≤ (p : Nat) → (p : Nat) < z.ctrlBase → tape0 p = false := hszeros
  replace hctrlw : windowSpells tape0 z.ctrlBase (encodeCtrlStackR ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hmark : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd
        - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length - 1 →
      tape0 p = true := hmark
  replace hcorr : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd
        - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length - 1 →
      tape0 p = false := hcorr
  replace hcfit : z.certBase + (encodePreorder width h_width
      (PreToken.leaf (SLGate.const b) :: toks')).length ≤ z.certEnd := hcfit
  have henc_len : (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length
      = 4 + (encodePreorder width h_width toks').length := by
    rw [show encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')
        = [false, false, true, b] ++ encodePreorder width h_width toks' from by
      rw [encodePreorder_cons]; rfl]
    rw [List.length_append]
    rfl
  set CUR := z.certEnd
      - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length
    with hCUR
  set fm := z.workBase + (encodeGateRecordStream out).length with hfm
  set vtop := z.valBase + (encodeNatStackR val).length with hvtop
  set k := out.length with hk
  -- Geometry shells.
  have hvallen1 : 1 ≤ (encodeNatStackR val).length := by
    cases hv : encodeNatStackR val with
    | nil =>
        have := encodeNatStackR_getLast_true val
        rw [hv] at this; simp at this
    | cons a l => simp
  have hctrllen1 : 1 ≤ (encodeCtrlStackR ctrl).length := by
    cases hv : encodeCtrlStackR ctrl with
    | nil =>
        have := encodeCtrlStackR_getLast_true ctrl
        rw [hv] at this; simp at this
    | cons a l => simp
  have hgapMC : z.ctrlBase + (encodeCtrlStackR ctrl).length + 2 ≤ CUR - 1 := by omega
  have hgapRV : fm + 4 ≤ z.valBase := by omega
  have hgeomV : vtop + k + 4 ≤ z.shwBase := by omega
  have hentry_len : (encodeNatEntryR k).length = k + 3 := encodeNatEntryR_length k
  -- `c2`'s tape agrees with `tape0` outside the two written windows.
  have htape2_off : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      ¬ (fm ≤ (p : Nat) ∧ (p : Nat) < fm + 4) →
      ¬ (CUR - 1 ≤ (p : Nat) ∧ (p : Nat) < CUR + 4) →
      c2.tape p = tape0 p := by
    intro p hp1 hp2
    rw [htape2]
    unfold writeBlockTape
    rw [if_neg (by rw [constRecBlock_length]; omega),
      if_neg (by rw [constMarkBlock_length]; omega)]
  -- L19 (γ-scan 103 → 105): from `fm + 4` to the value sentinel.
  obtain ⟨p19, h19, t19⟩ := constIter_region_scanR_103.run_scanRight_hop c2 hphase2
    (z.valBase - (fm + 4))
    (by have := constIter_len L; omega)
    (fun p hlo hhi => by
      rw [htape2_off p (by omega) (by omega)]
      exact hfzeros p (by omega) (by omega))
    (fun p hp => by
      rw [htape2_off p (by omega) (by omega)]
      obtain ⟨hf, hc⟩ := hval
      have := hc p (by omega) (by omega)
      rw [this, show (p : Nat) - z.valBase = 0 from by omega]
      rw [show encodeNatStackR val = true :: val.reverse.flatMap encodeNatEntryR from rfl]
      rfl)
  set c3 := TM.runConfig (M := constIterProgram.toPhased.toTM) c2
    ((z.valBase - (fm + 4)) + 2) with hc3
  have hh3 : (c3.head : Nat) = z.valBase := by rw [h19]; omega
  -- L20 (walk the value zone rightward 105 → 111): to the second dead cell `vtop + 1`.
  have hvalwz : (walkZone (val.map (· + 2))).length = (encodeNatStackR val).length := by
    rw [encodeNatStackR_eq_walkZone]
  obtain ⟨p20, h20, t20⟩ := constIter_region_walkR_105.run_walkZoneRight_hop
    (by intro j hj; unfold exitAt; rw [if_neg (by omega)])
    (by unfold exitAt; rw [if_pos rfl])
    c3 (hlen_of_le (Nat.le_succ L)) p19
    (val.map (· + 2))
    (by intro x hx; rw [List.mem_map] at hx; obtain ⟨v, -, rfl⟩ := hx; omega)
    z.valBase hh3
    (by rw [hvalwz]; have := walkR_len L; omega)
    (by
      rw [t19]
      refine ⟨by rw [hvalwz]; have := constIter_len L; omega, fun q hlo hhi => ?_⟩
      rw [hvalwz] at hhi
      rw [htape2_off q (by omega) (by omega),
        show walkZone (val.map (· + 2)) = encodeNatStackR val from
          (encodeNatStackR_eq_walkZone val).symm]
      exact hval.2 q hlo (by omega))
    (by
      intro p hp
      rw [hvalwz] at hp
      rw [t19, htape2_off p (by omega) (by omega)]
      exact hvzeros p (by omega) (by omega))
    (by
      intro p hp
      rw [hvalwz] at hp
      rw [t19, htape2_off p (by omega) (by omega)]
      exact hvzeros p (by omega) (by omega))
  rw [hvalwz] at h20
  set c4 := TM.runConfig (M := constIterProgram.toPhased.toTM) c3
    (walkZoneStepsR (val.map (· + 2)) + 1) with hc4
  have hh4 : (c4.head : Nat) = vtop + 1 := by rw [h20]
  have ht4 : c4.tape = c2.tape := by rw [t20, t19]
  -- L21 (step left 111 → 113): onto the value frontier `vtop`.
  obtain ⟨p21, h21, t21⟩ := constIter_region_sL13_111.run_stepLeft_hop c4 p20 (by omega)
  set c5 := TM.runConfig (M := constIterProgram.toPhased.toTM) c4 2 with hc5
  have hh5 : (c5.head : Nat) = vtop := by rw [h21]; omega
  have ht5 : c5.tape = c2.tape := by rw [t21, ht4]
  -- L22 (the value-push region 113 → 148): the entry fan-out, `SHW` restored in place.
  obtain ⟨t, htb, p22, h22, t22⟩ := constIter_region_vpush_113.run_valuePush_hop
    (by intro j hj; unfold exitAt; rw [if_neg (by omega)])
    (by unfold exitAt; rw [if_pos rfl])
    c5 (hlen_of_le (Nat.le_succ L)) p21 vtop z.shwBase k hh5 hgeomV
    (by have := vpush_len L; omega)
    (fun p hp1 hp2 => by
      rw [ht5, htape2_off p (by omega) (by omega)]
      exact hvzeros p (by omega) (by omega))
    (fun p hp => by
      rw [ht5, htape2_off p (by omega) (by omega)]
      obtain ⟨hf, hc⟩ := hshw
      have := hc p (by omega) (by rw [List.length_replicate]; omega)
      rw [this]
      exact getD_replicate_of_lt true false (by omega))
    (fun p hp1 hp2 => by
      rw [ht5, htape2_off p (by omega) (by omega)]
      obtain ⟨hf, hc⟩ := hshw
      have := hc p (by omega) (by rw [List.length_replicate]; omega)
      rw [this]
      exact getD_replicate_of_lt true false (by omega))
    (fun p hp1 hp2 => by
      rw [ht5, htape2_off p (by omega) (by omega)]
      exact hszeros p (by omega) (by omega))
  set c6 := TM.runConfig (M := constIterProgram.toPhased.toTM) c5 t with hc6
  have ht6 : c6.tape = writeBlockTape c2.tape vtop (encodeNatEntryR k) := by
    rw [t22, ht5]
  -- The post-push tape, off and on the entry window.
  have ht6_off : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      ¬ (fm ≤ (p : Nat) ∧ (p : Nat) < fm + 4) →
      ¬ (CUR - 1 ≤ (p : Nat) ∧ (p : Nat) < CUR + 4) →
      ¬ (vtop ≤ (p : Nat) ∧ (p : Nat) < vtop + k + 3) →
      c6.tape p = tape0 p := by
    intro p hp1 hp2 hp3
    rw [ht6]
    unfold writeBlockTape
    rw [if_neg (by rw [hentry_len]; omega)]
    exact htape2_off p hp1 hp2
  have ht6_entry_ones : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      vtop + 1 ≤ (p : Nat) → (p : Nat) < vtop + k + 3 → c6.tape p = true := by
    intro p hp1 hp2
    rw [ht6]
    unfold writeBlockTape
    rw [if_pos (by rw [hentry_len]; omega)]
    rw [show encodeNatEntryR k = false :: List.replicate (k + 2) true from rfl]
    rw [show (p : Nat) - vtop = ((p : Nat) - vtop - 1) + 1 from by omega, List.getD_cons_succ]
    exact getD_replicate_of_lt true false (by omega)
  -- L23 (step right 148 → 150): off the entry's leading 0 onto its first 1.
  obtain ⟨p23, h23, t23⟩ := constIter_region_sR2_148.run_stepRight_hop c6 p22
    (by have := constIter_len L; omega)
  set c7 := TM.runConfig (M := constIterProgram.toPhased.toTM) c6 2 with hc7
  have hh7 : (c7.head : Nat) = vtop + 1 := by rw [h23]; omega
  have ht7 : c7.tape = c6.tape := t23
  -- L24 (ones-scan right 150 → 152): across the entry's `1^(k+2)` onto the dead cell.
  obtain ⟨p24, h24, t24⟩ := constIter_region_scanR1_150.run_scanRightOne_hop c7 p23 (k + 2)
    (by have := constIter_len L; omega)
    (fun p hp1 hp2 => by
      rw [ht7]
      exact ht6_entry_ones p (by omega) (by omega))
    (fun p hp => by
      rw [ht7, ht6_off p (by omega) (by omega) (by omega)]
      exact hvzeros p (by omega) (by omega))
  set c8 := TM.runConfig (M := constIterProgram.toPhased.toTM) c7 ((k + 2) + 2) with hc8
  have hh8 : (c8.head : Nat) = vtop + k + 3 := by rw [h24]; omega
  have ht8 : c8.tape = c6.tape := by rw [t24, ht7]
  -- L25 (γ-scan 152 → 154): across the val→SHW dead corridor onto the `SHW` anchor.
  obtain ⟨p25, h25, t25⟩ := constIter_region_scanR2_152.run_scanRight_hop c8 p24
    (z.shwBase - (vtop + k + 3))
    (by have := constIter_len L; omega)
    (fun p hlo hhi => by
      rw [ht8, ht6_off p (by omega) (by omega) (by omega)]
      exact hvzeros p (by omega) (by omega))
    (fun p hp => by
      rw [ht8, ht6_off p (by omega) (by omega) (by omega)]
      obtain ⟨hf, hc⟩ := hshw
      have := hc p (by omega) (by rw [List.length_replicate]; omega)
      rw [this, show (p : Nat) - z.shwBase = 0 from by omega]
      rfl)
  set c9 := TM.runConfig (M := constIterProgram.toPhased.toTM) c8
    ((z.shwBase - (vtop + k + 3)) + 2) with hc9
  have hh9 : (c9.head : Nat) = z.shwBase := by rw [h25]; omega
  have ht9 : c9.tape = c6.tape := by rw [t25, ht8]
  -- L26 (ones-scan right 154 → 156): across `SHW`'s `1^(k+1)` onto the tick cell.
  obtain ⟨p26, h26, t26⟩ := constIter_region_scanR12_154.run_scanRightOne_hop c9 p25 (k + 1)
    (by have := constIter_len L; omega)
    (fun p hp1 hp2 => by
      rw [ht9, ht6_off p (by omega) (by omega) (by omega)]
      obtain ⟨hf, hc⟩ := hshw
      have := hc p (by omega) (by rw [List.length_replicate]; omega)
      rw [this]
      exact getD_replicate_of_lt true false (by omega))
    (fun p hp => by
      rw [ht9, ht6_off p (by omega) (by omega) (by omega)]
      exact hszeros p (by omega) (by omega))
  set c10 := TM.runConfig (M := constIterProgram.toPhased.toTM) c9 ((k + 1) + 2) with hc10
  have hh10 : (c10.head : Nat) = z.shwBase + k + 1 := by rw [h26]; omega
  have ht10 : c10.tape = c6.tape := by rw [t26, ht9]
  -- L27 (the tick 156 → 158): one `1` at the `SHW` window's right end.
  obtain ⟨p27, h27, t27⟩ := constIter_region_tick_156.run_writeBits_hop c10 p26
    (by simp only [List.length_singleton]; have := constIter_len L; omega)
  set c11 := TM.runConfig (M := constIterProgram.toPhased.toTM) c10
    ((List.length [true]) + 1) with hc11
  have hh11 : (c11.head : Nat) = z.shwBase + k + 2 := by
    rw [h27]
    simp only [List.length_singleton]
    omega
  have ht11 : c11.tape = writeBlockTape c6.tape (z.shwBase + k + 1) [true] := by
    rw [t27, hh10, ht10]
  have ht11_off : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) ≠ z.shwBase + k + 1 →
      c11.tape p = c6.tape p := by
    intro p hp
    rw [ht11]
    unfold writeBlockTape
    rw [if_neg (by simp only [List.length_singleton]; omega)]
  -- L28 (γ-scan 158 → 160): across the SHW→ctrl dead corridor onto the control sentinel.
  obtain ⟨p28, h28, t28⟩ := constIter_region_scanR3_158.run_scanRight_hop c11 p27
    (z.ctrlBase - (z.shwBase + k + 2))
    (by have := constIter_len L; omega)
    (fun p hlo hhi => by
      rw [ht11_off p (by omega), ht6_off p (by omega) (by omega) (by omega)]
      exact hszeros p (by omega) (by omega))
    (fun p hp => by
      rw [ht11_off p (by omega), ht6_off p (by omega) (by omega) (by omega)]
      obtain ⟨hf, hc⟩ := hctrlw
      have := hc p (by omega) (by omega)
      rw [this, show (p : Nat) - z.ctrlBase = 0 from by omega]
      rw [show encodeCtrlStackR ctrl = true :: ctrl.reverse.flatMap encodeCtrlFrameR from rfl]
      rfl)
  set c12 := TM.runConfig (M := constIterProgram.toPhased.toTM) c11
    ((z.ctrlBase - (z.shwBase + k + 2)) + 2) with hc12
  have hh12 : (c12.head : Nat) = z.ctrlBase := by rw [h28]; omega
  have ht12 : c12.tape = c11.tape := t28
  -- L29 (walk the control zone rightward 160 → 166): to the second dead cell past its content.
  have hctrlwz : (walkZone (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])).length
      = (encodeCtrlStackR ctrl).length := by
    rw [encodeCtrlStackR_eq_walkZone]
  obtain ⟨p29, h29, t29⟩ := constIter_region_walkR2_160.run_walkZoneRight_hop
    (by intro j hj; unfold exitAt; rw [if_neg (by omega)])
    (by unfold exitAt; rw [if_pos rfl])
    c12 (hlen_of_le (Nat.le_succ L)) p28
    (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
    (by
      intro x hx
      rw [List.mem_flatMap] at hx
      obtain ⟨f, hf, hxf⟩ := hx
      have := hrem f hf
      simp only [List.mem_cons] at hxf
      rcases hxf with rfl | rfl | hfalse
      · omega
      · omega
      · simp at hfalse)
    z.ctrlBase hh12
    (by rw [hctrlwz]; have := walkR_len L; omega)
    (by
      rw [ht12]
      refine ⟨by rw [hctrlwz]; have := constIter_len L; omega, fun q hlo hhi => ?_⟩
      rw [hctrlwz] at hhi
      rw [ht11_off q (by omega), ht6_off q (by omega) (by omega) (by omega),
        show walkZone (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
          = encodeCtrlStackR ctrl from (encodeCtrlStackR_eq_walkZone ctrl).symm]
      exact hctrlw.2 q hlo (by omega))
    (by
      intro p hp
      rw [hctrlwz] at hp
      rw [ht12, ht11_off p (by omega), ht6_off p (by omega) (by omega) (by omega)]
      exact hcorr p (by omega) (by omega))
    (by
      intro p hp
      rw [hctrlwz] at hp
      rw [ht12, ht11_off p (by omega), ht6_off p (by omega) (by omega) (by omega)]
      exact hcorr p (by omega) (by omega))
  rw [hctrlwz] at h29
  set c13 := TM.runConfig (M := constIterProgram.toPhased.toTM) c12
    (walkZoneStepsR (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1) with hc13
  have hh13 : (c13.head : Nat) = z.ctrlBase + (encodeCtrlStackR ctrl).length + 1 := by
    rw [h29]
  have ht13 : c13.tape = c11.tape := by rw [t29, ht12]
  -- The mark window on the final tape: four zeros then the new marker.
  have ht13_mark_zeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 3 → c13.tape p = false := by
    intro p hp1 hp2
    rw [ht13, ht11_off p (by omega), ht6, htape2]
    unfold writeBlockTape
    rw [if_neg (by rw [hentry_len]; omega), if_neg (by rw [constRecBlock_length]; omega),
      if_pos (by rw [constMarkBlock_length]; omega)]
    have h4 : (p : Nat) - (CUR - 1) = 0 ∨ (p : Nat) - (CUR - 1) = 1
        ∨ (p : Nat) - (CUR - 1) = 2 ∨ (p : Nat) - (CUR - 1) = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;> rfl
  have ht13_marker : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 3 → c13.tape p = true := by
    intro p hp
    rw [ht13, ht11_off p (by omega), ht6, htape2]
    unfold writeBlockTape
    rw [if_neg (by rw [hentry_len]; omega), if_neg (by rw [constRecBlock_length]; omega),
      if_pos (by rw [constMarkBlock_length]; omega),
      show (p : Nat) - (CUR - 1) = 4 from by omega]
    rfl
  -- L30 (γ-scan 166 → 168): across the dead corridor and the consumed token onto the new marker.
  obtain ⟨p30, h30, t30⟩ := constIter_region_scanR4_166.run_scanRight_hop c13 p29
    ((CUR + 3) - (z.ctrlBase + (encodeCtrlStackR ctrl).length + 1))
    (by have := constIter_len L; omega)
    (fun p hlo hhi => by
      rw [hh13] at hlo hhi
      by_cases hp : (p : Nat) < CUR - 1
      · rw [ht13, ht11_off p (by omega), ht6_off p (by omega) (by omega) (by omega)]
        exact hcorr p (by omega) (by omega)
      · exact ht13_mark_zeros p (by omega) (by omega))
    (fun p hp => by
      rw [hh13] at hp
      exact ht13_marker p (by omega))
  set c14 := TM.runConfig (M := constIterProgram.toPhased.toTM) c13
    (((CUR + 3) - (z.ctrlBase + (encodeCtrlStackR ctrl).length + 1)) + 2) with hc14
  have hh14 : (c14.head : Nat) = CUR + 3 := by rw [h30]; omega
  have ht14 : c14.tape = c11.tape := by rw [t30, ht13]
  -- Assemble the chain.
  have hfinal : TM.runConfig (M := constIterProgram.toPhased.toTM) c2
      (((z.valBase - (fm + 4)) + 2) + ((walkZoneStepsR (val.map (· + 2)) + 1) + (2 + (t + (2 + (((k + 2) + 2) + (((z.shwBase - (vtop + k + 3)) + 2) + (((k + 1) + 2) + (((List.length [true]) + 1) + (((z.ctrlBase - (z.shwBase + k + 2)) + 2) + ((walkZoneStepsR (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1) + ((((CUR + 3) - (z.ctrlBase + (encodeCtrlStackR ctrl).length + 1)) + 2)))))))))))))
      = c14 := by
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
    rw [TM.runConfig_add, ← hc6]
    rw [TM.runConfig_add, ← hc7]
    rw [TM.runConfig_add, ← hc8]
    rw [TM.runConfig_add, ← hc9]
    rw [TM.runConfig_add, ← hc10]
    rw [TM.runConfig_add, ← hc11]
    rw [TM.runConfig_add, ← hc12]
    rw [TM.runConfig_add, ← hc13]
  -- The budget.
  have hwzv := walkZoneStepsR_le (val.map (· + 2))
  have hwzc := walkZoneStepsR_le (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
  rw [hvalwz] at hwzv
  rw [hctrlwz] at hwzc
  have hmul : t ≤ (k + 2) * (2 * z.certEnd + 6 * k + 20) + 1 := by
    refine le_trans htb ?_
    have hmono := Nat.mul_le_mul_left (k + 2)
      (show 2 * (z.shwBase - vtop) + 6 * k + 20 ≤ 2 * z.certEnd + 6 * k + 20 from by omega)
    omega
  refine ⟨((z.valBase - (fm + 4)) + 2) + ((walkZoneStepsR (val.map (· + 2)) + 1) + (2 + (t + (2 + (((k + 2) + 2) + (((z.shwBase - (vtop + k + 3)) + 2) + (((k + 1) + 2) + (((List.length [true]) + 1) + (((z.ctrlBase - (z.shwBase + k + 2)) + 2) + ((walkZoneStepsR (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1) + ((((CUR + 3) - (z.ctrlBase + (encodeCtrlStackR ctrl).length + 1)) + 2)))))))))))), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_singleton]
    omega
  · rw [hfinal, p30]
  · rw [hfinal, hh14]
    omega
  · rw [hfinal, ht14, ht11, ht6, htape2]

set_option maxHeartbeats 4000000 in
/-- **The const-arm front** (per value bit): from the read home, the machine reads the tag and
the value bit, rewrites the marker block, travels the six leftward legs to the WORK frontier and
writes the record-plus-replant block — landing at the shared-tail entry (phase `103`, head
`FM + 4`) with the marker and record written over the home tape. -/
theorem constIter_run_front {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (b : Bool) (toks' : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat)
    (c0 : Configuration (M := constIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape
      (⟨PreToken.leaf (SLGate.const b) :: toks', out, ctrl, val, false⟩ : DriveState n))
    (hrem : ∀ f ∈ ctrl, 1 ≤ f.2)
    (hLfit : z.certEnd + 2 ≤ L)
    (hphase0 : (c0.state.fst : Nat) = 0)
    (hhead0 : (c0.head : Nat) = z.certEnd
      - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length - 1) :
    ∃ F : Nat, F ≤ 10 * z.certEnd + out.length + 80
      ∧ (((TM.runConfig (M := constIterProgram.toPhased.toTM) c0 F).state).fst : Nat) = 103
      ∧ ((TM.runConfig (M := constIterProgram.toPhased.toTM) c0 F).head : Nat)
          = z.workBase + (encodeGateRecordStream out).length + 4
      ∧ (TM.runConfig (M := constIterProgram.toPhased.toTM) c0 F).tape
          = writeBlockTape
              (writeBlockTape c0.tape
                (z.certEnd - (encodePreorder width h_width
                  (PreToken.leaf (SLGate.const b) :: toks')).length - 1) constMarkBlock)
              (z.workBase + (encodeGateRecordStream out).length) (constRecBlock b) := by
  cases b with
  | false =>
      obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
        hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
      replace hcert : windowSpells c0.tape
          (z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.const false) :: toks')).length)
          (encodePreorder width h_width (PreToken.leaf (SLGate.const false) :: toks')) := hcert
      replace hcfit : z.certBase + (encodePreorder width h_width
          (PreToken.leaf (SLGate.const false) :: toks')).length ≤ z.certEnd := hcfit
      replace hcorr : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
          (p : Nat) < z.certEnd
            - (encodePreorder width h_width
                (PreToken.leaf (SLGate.const false) :: toks')).length - 1 →
          c0.tape p = false := hcorr
      replace hFM : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = z.workBase + (encodeGateRecordStream out).length → c0.tape p = true := hFM
      replace hffit : z.workBase + (encodeGateRecordStream out).length + 1 ≤ z.workEnd := hffit
      replace hfzeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.workBase + (encodeGateRecordStream out).length + 1 ≤ (p : Nat) →
          (p : Nat) < z.valBase → c0.tape p = false := hfzeros
      replace hval : windowSpells c0.tape z.valBase (encodeNatStackR val) := hval
      replace hvfit : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
      replace hvzeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.valBase + (encodeNatStackR val).length ≤ (p : Nat) →
          (p : Nat) < z.shwBase → c0.tape p = false := hvzeros
      replace hshw : windowSpells c0.tape z.shwBase
          (List.replicate (out.length + 1) true) := hshw
      replace hsfit : z.shwBase + out.length + 1 ≤ z.shwEnd := hsfit
      replace hszeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.shwBase + out.length + 1 ≤ (p : Nat) → (p : Nat) < z.ctrlBase →
          c0.tape p = false := hszeros
      replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR ctrl) := hctrlw
      replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ z.ctrlEnd := hcfit2
      have henc_len : (encodePreorder width h_width
          (PreToken.leaf (SLGate.const false) :: toks')).length
          = 4 + (encodePreorder width h_width toks').length := by
        rw [show encodePreorder width h_width (PreToken.leaf (SLGate.const false) :: toks')
            = [false, false, true, false] ++ encodePreorder width h_width toks' from by
          rw [encodePreorder_cons]; rfl]
        rw [List.length_append]
        rfl
      set CUR := z.certEnd - (encodePreorder width h_width
          (PreToken.leaf (SLGate.const false) :: toks')).length with hCUR
      set fm := z.workBase + (encodeGateRecordStream out).length with hfm
      set vtop := z.valBase + (encodeNatStackR val).length with hvtop
      set k := out.length with hk
      have hvallen1 : 1 ≤ (encodeNatStackR val).length := by
        cases hv : encodeNatStackR val with
        | nil =>
            have := encodeNatStackR_getLast_true val
            rw [hv] at this; simp at this
        | cons a l => simp
      have hctrllen1 : 1 ≤ (encodeCtrlStackR ctrl).length := by
        cases hv : encodeCtrlStackR ctrl with
        | nil =>
            have := encodeCtrlStackR_getLast_true ctrl
            rw [hv] at this; simp at this
        | cons a l => simp
      have hgapMC : z.ctrlBase + (encodeCtrlStackR ctrl).length + 2 ≤ CUR - 1 := by omega
      have hbits : encodePreorder width h_width (PreToken.leaf (SLGate.const false) :: toks')
          = [false, false, true, false] ++ encodePreorder width h_width toks' := by
        rw [encodePreorder_cons]; rfl
      have hcl0 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR → c0.tape p = false := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 0 from by omega]
        rfl
      have hcl1 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR + 1 → c0.tape p = false := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 1 from by omega]
        rfl
      have hcl2 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR + 2 → c0.tape p = true := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 2 from by omega]
        rfl
      have hcl3 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR + 3 → c0.tape p = false := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 3 from by omega]
        rfl
      -- L1 (step right 0 → 2): off the marker onto the token's first cell.
      obtain ⟨p1, h1c, t1⟩ := constIter_region_sR_0.run_stepRight_hop c0 hphase0
        (by have := constIter_len L; omega)
      set d1 := TM.runConfig (M := constIterProgram.toPhased.toTM) c0 2 with hd1
      have hh1 : (d1.head : Nat) = CUR := by rw [h1c]; omega
      -- L2 (certTrie const hop 2 → 14): read `fft`, land on the value bit.
      obtain ⟨p2, h2c, t2⟩ := constIter_region_trie_2.run_certTrie_const_hop
        rfl rfl rfl rfl
        d1 p1 (by have := constIter_len L; omega)
        (by rw [t1]; exact hcl0 d1.head (by omega))
        (fun p hp => by rw [t1]; exact hcl1 p (by omega))
        (fun p hp => by rw [t1]; exact hcl2 p (by omega))
      set d2 := TM.runConfig (M := constIterProgram.toPhased.toTM) d1 4 with hd2
      have hh2 : (d2.head : Nat) = CUR + 3 := by rw [h2c]; omega
      have ht2 : d2.tape = c0.tape := by rw [t2, t1]
      -- L3 (bit probe 14 → chain): read the value bit in place.
      obtain ⟨p3, h3c, t3⟩ := constIter_region_probe_14.run_bitProbe_zero_hop
        rfl rfl
        d2 p2
        (by rw [ht2]; exact hcl3 d2.head (by omega))
      set d3 := TM.runConfig (M := constIterProgram.toPhased.toTM) d2 2 with hd3
      have hh3 : (d3.head : Nat) = CUR + 3 := by rw [h3c]; omega
      have ht3 : d3.tape = c0.tape := by rw [t3, ht2]
      -- L4–L7 (4 × step left): back across the consumed token onto the old marker.
      obtain ⟨p4, h4c, t4⟩ := constIter_region_sL_17.run_stepLeft_hop d3 p3 (by omega)
      set d4 := TM.runConfig (M := constIterProgram.toPhased.toTM) d3 2 with hd4
      have hh4 : (d4.head : Nat) = CUR + 2 := by rw [h4c]; omega
      obtain ⟨p5, h5c, t5⟩ := constIter_region_sL2_19.run_stepLeft_hop d4 p4 (by omega)
      set d5 := TM.runConfig (M := constIterProgram.toPhased.toTM) d4 2 with hd5
      have hh5 : (d5.head : Nat) = CUR + 1 := by rw [h5c]; omega
      obtain ⟨p6, h6c, t6⟩ := constIter_region_sL3_21.run_stepLeft_hop d5 p5 (by omega)
      set d6 := TM.runConfig (M := constIterProgram.toPhased.toTM) d5 2 with hd6
      have hh6 : (d6.head : Nat) = CUR := by rw [h6c]; omega
      obtain ⟨p7, h7c, t7⟩ := constIter_region_sL4_23.run_stepLeft_hop d6 p6 (by omega)
      set d7 := TM.runConfig (M := constIterProgram.toPhased.toTM) d6 2 with hd7
      have hh7 : (d7.head : Nat) = CUR - 1 := by rw [h7c]; omega
      have ht7 : d7.tape = c0.tape := by rw [t7, t6, t5, t4, ht3]
      -- L8 (the marker block 25/68 → next): `[0,0,0,0,1]` from the old marker.
      obtain ⟨p8, h8c, t8⟩ := constIter_region_mark_25.run_writeBits_hop d7 p7
        (by simp only [constMarkBlock_length]; have := constIter_len L; omega)
      set d8 := TM.runConfig (M := constIterProgram.toPhased.toTM) d7
        (constMarkBlock.length + 1) with hd8
      have hh8 : (d8.head : Nat) = CUR + 4 := by
        rw [h8c]
        simp only [constMarkBlock_length]
        omega
      have ht8 : d8.tape = writeBlockTape c0.tape (CUR - 1) constMarkBlock := by
        rw [t8, hh7, ht7]
      have ht8_off : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          ¬ (CUR - 1 ≤ (p : Nat) ∧ (p : Nat) < CUR + 4) →
          d8.tape p = c0.tape p := by
        intro p hp
        rw [ht8]
        unfold writeBlockTape
        rw [if_neg (by rw [constMarkBlock_length]; omega)]
      have ht8_zeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 3 → d8.tape p = false := by
        intro p hp1 hp2
        rw [ht8]
        unfold writeBlockTape
        rw [if_pos (by rw [constMarkBlock_length]; omega)]
        have h4 : (p : Nat) - (CUR - 1) = 0 ∨ (p : Nat) - (CUR - 1) = 1
            ∨ (p : Nat) - (CUR - 1) = 2 ∨ (p : Nat) - (CUR - 1) = 3 := by omega
        rcases h4 with h | h | h | h <;> rw [h] <;> rfl
      -- L9–L10 (2 × step left): off the rewritten block onto the dead cell `CUR + 2`.
      obtain ⟨p9, h9c, t9⟩ := constIter_region_sL5_31.run_stepLeft_hop d8 p8 (by omega)
      set d9 := TM.runConfig (M := constIterProgram.toPhased.toTM) d8 2 with hd9
      have hh9 : (d9.head : Nat) = CUR + 3 := by rw [h9c]; omega
      obtain ⟨p10, h10c, t10⟩ := constIter_region_sL6_33.run_stepLeft_hop d9 p9 (by omega)
      set d10 := TM.runConfig (M := constIterProgram.toPhased.toTM) d9 2 with hd10
      have hh10 : (d10.head : Nat) = CUR + 2 := by rw [h10c]; omega
      have ht10 : d10.tape = d8.tape := by rw [t10, t9]
      -- L11 (scan left 35/78 → next): onto the control stack's top content cell.
      obtain ⟨p11, h11c, t11⟩ := constIter_region_scanL_35.run_scanLeft_hop d10 p10
        (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht10]
          by_cases hp : (p : Nat) < CUR - 1
          · rw [ht8_off p (by omega)]
            exact hcorr p (by omega) (by omega)
          · exact ht8_zeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht10, ht8_off p (by omega)]
          exact windowSpells_getLast_true c0.tape z.ctrlBase _ hctrlw
            (encodeCtrlStackR_getLast_true ctrl) p (by omega))
      set d11 := TM.runConfig (M := constIterProgram.toPhased.toTM) d10
        (((d10.head : Nat) - (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)) + 2) with hd11
      have hh11 : (d11.head : Nat) = z.ctrlBase + (encodeCtrlStackR ctrl).length - 1 := by
        rw [h11c]
      have ht11 : d11.tape = d8.tape := by rw [t11, ht10]
      -- L12 (walk the control zone leftward 37/80 → next): park on `ctrlBase − 1`.
      have hctrlwz : (walkZone (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])).length
          = (encodeCtrlStackR ctrl).length := by
        rw [encodeCtrlStackR_eq_walkZone]
      obtain ⟨p12, h12c, t12⟩ := constIter_region_walkL_37.run_walkZoneLeft_hop
        (by intro j hj; unfold exitAt; rw [if_neg (by omega)])
        (by unfold exitAt; rw [if_pos rfl])
        d11 (hlen_of_le (Nat.le_succ L)) p11
        (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
        (by
          intro x hx
          rw [List.mem_flatMap] at hx
          obtain ⟨f, hf, hxf⟩ := hx
          have := hrem f hf
          simp only [List.mem_cons] at hxf
          rcases hxf with rfl | rfl | hfalse
          · omega
          · omega
          · simp at hfalse)
        z.ctrlBase (by omega)
        (by rw [hh11, hctrlwz])
        (by have := walkL_len L; omega)
        (by
          rw [ht11]
          refine ⟨by rw [hctrlwz]; have := constIter_len L; omega, fun q hlo hhi => ?_⟩
          rw [hctrlwz] at hhi
          rw [ht8_off q (by omega),
            show walkZone (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
              = encodeCtrlStackR ctrl from (encodeCtrlStackR_eq_walkZone ctrl).symm]
          exact hctrlw.2 q hlo (by omega))
        (fun p hp => by
          rw [ht11, ht8_off p (by omega)]
          exact hszeros p (by omega) (by omega))
      set d12 := TM.runConfig (M := constIterProgram.toPhased.toTM) d11
        (walkZoneSteps (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1) with hd12
      have hh12 : (d12.head : Nat) = z.ctrlBase - 1 := by rw [h12c]
      have ht12 : d12.tape = d8.tape := by rw [t12, ht11]
      -- L13 (scan left 42/85 → next): onto the `SHW` window's top `1`.
      obtain ⟨p13, h13c, t13⟩ := constIter_region_scanL2_42.run_scanLeft_hop d12 p12
        (z.shwBase + k)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht12, ht8_off p (by omega)]
          exact hszeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht12, ht8_off p (by omega)]
          obtain ⟨hf, hc⟩ := hshw
          have := hc p (by omega) (by rw [List.length_replicate]; omega)
          rw [this]
          exact getD_replicate_of_lt true false (by omega))
      set d13 := TM.runConfig (M := constIterProgram.toPhased.toTM) d12
        (((d12.head : Nat) - (z.shwBase + k)) + 2) with hd13
      have hh13 : (d13.head : Nat) = z.shwBase + k := by rw [h13c]
      have ht13 : d13.tape = d8.tape := by rw [t13, ht12]
      -- L14 (ones-scan left 44/87 → next): across `SHW` onto the dead cell `shwBase − 1`.
      obtain ⟨p14, h14c, t14⟩ := constIter_region_scanL1_44.run_scanLeftOne_hop d13 p13
        (z.shwBase - 1)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht13, ht8_off p (by omega)]
          obtain ⟨hf, hc⟩ := hshw
          have := hc p (by omega) (by rw [List.length_replicate]; omega)
          rw [this]
          exact getD_replicate_of_lt true false (by omega))
        (fun p hp => by
          rw [ht13, ht8_off p (by omega)]
          exact hvzeros p (by omega) (by omega))
      set d14 := TM.runConfig (M := constIterProgram.toPhased.toTM) d13
        (((d13.head : Nat) - (z.shwBase - 1)) + 2) with hd14
      have hh14 : (d14.head : Nat) = z.shwBase - 1 := by rw [h14c]
      have ht14 : d14.tape = d8.tape := by rw [t14, ht13]
      -- L15 (scan left 46/89 → next): onto the value stack's top content cell.
      obtain ⟨p15, h15c, t15⟩ := constIter_region_scanL3_46.run_scanLeft_hop d14 p14
        (vtop - 1)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht14, ht8_off p (by omega)]
          exact hvzeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht14, ht8_off p (by omega)]
          exact windowSpells_getLast_true c0.tape z.valBase _ hval
            (encodeNatStackR_getLast_true val) p (by omega))
      set d15 := TM.runConfig (M := constIterProgram.toPhased.toTM) d14
        (((d14.head : Nat) - (vtop - 1)) + 2) with hd15
      have hh15 : (d15.head : Nat) = vtop - 1 := by rw [h15c]
      have ht15 : d15.tape = d8.tape := by rw [t15, ht14]
      -- L16 (walk the value zone leftward 48/91 → next): park on `valBase − 1`.
      have hvalwz : (walkZone (val.map (· + 2))).length = (encodeNatStackR val).length := by
        rw [encodeNatStackR_eq_walkZone]
      obtain ⟨p16, h16c, t16⟩ := constIter_region_walkL2_48.run_walkZoneLeft_hop
        (by intro j hj; unfold exitAt; rw [if_neg (by omega)])
        (by unfold exitAt; rw [if_pos rfl])
        d15 (hlen_of_le (Nat.le_succ L)) p15
        (val.map (· + 2))
        (by intro x hx; rw [List.mem_map] at hx; obtain ⟨v, -, rfl⟩ := hx; omega)
        z.valBase (by omega)
        (by rw [hh15, hvalwz])
        (by have := walkL_len L; omega)
        (by
          rw [ht15]
          refine ⟨by rw [hvalwz]; have := constIter_len L; omega, fun q hlo hhi => ?_⟩
          rw [hvalwz] at hhi
          rw [ht8_off q (by omega),
            show walkZone (val.map (· + 2)) = encodeNatStackR val from
              (encodeNatStackR_eq_walkZone val).symm]
          exact hval.2 q hlo (by omega))
        (fun p hp => by
          rw [ht15, ht8_off p (by omega)]
          exact hfzeros p (by omega) (by omega))
      set d16 := TM.runConfig (M := constIterProgram.toPhased.toTM) d15
        (walkZoneSteps (val.map (· + 2)) + 1) with hd16
      have hh16 : (d16.head : Nat) = z.valBase - 1 := by rw [h16c]
      have ht16 : d16.tape = d8.tape := by rw [t16, ht15]
      -- L17 (scan left 53/96 → next): onto the frontier marker `FM`.
      obtain ⟨p17, h17c, t17⟩ := constIter_region_scanL4_53.run_scanLeft_hop d16 p16
        fm
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht16, ht8_off p (by omega)]
          exact hfzeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht16, ht8_off p (by omega)]
          exact hFM p (by omega))
      set d17 := TM.runConfig (M := constIterProgram.toPhased.toTM) d16
        (((d16.head : Nat) - fm) + 2) with hd17
      have hh17 : (d17.head : Nat) = fm := by rw [h17c]
      have ht17 : d17.tape = d8.tape := by rw [t17, ht16]
      -- L18 (the record-plus-replant block 55/98 → 103): `[1,0,b,1]` at `FM`.
      obtain ⟨p18, h18c, t18⟩ := constIter_region_rec0_55.run_writeBits_hop d17 p17
        (by simp only [constRecBlock_length]; have := constIter_len L; omega)
      set d18 := TM.runConfig (M := constIterProgram.toPhased.toTM) d17
        ((constRecBlock false).length + 1) with hd18
      have hh18 : (d18.head : Nat) = fm + 4 := by
        rw [h18c, hh17]
        simp only [constRecBlock_length]
      have ht18 : d18.tape = writeBlockTape
          (writeBlockTape c0.tape (CUR - 1) constMarkBlock) fm (constRecBlock false) := by
        rw [t18, hh17, ht17, ht8]
      -- Assemble the chain.
      have hfinal : TM.runConfig (M := constIterProgram.toPhased.toTM) c0
          (2 + (4 + (2 + (2 + (2 + (2 + (2 + ((constMarkBlock.length + 1) + (2 + (2
            + ((((d10.head : Nat) - (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)) + 2)
            + ((walkZoneSteps (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1)
            + ((((d12.head : Nat) - (z.shwBase + k)) + 2)
            + ((((d13.head : Nat) - (z.shwBase - 1)) + 2)
            + ((((d14.head : Nat) - (vtop - 1)) + 2)
            + ((walkZoneSteps (val.map (· + 2)) + 1)
            + ((((d16.head : Nat) - fm) + 2)
            + ((constRecBlock false).length + 1))))))))))))))))))
          = d18 := by
        rw [TM.runConfig_add, ← hd1]
        rw [TM.runConfig_add, ← hd2]
        rw [TM.runConfig_add, ← hd3]
        rw [TM.runConfig_add, ← hd4]
        rw [TM.runConfig_add, ← hd5]
        rw [TM.runConfig_add, ← hd6]
        rw [TM.runConfig_add, ← hd7]
        rw [TM.runConfig_add, ← hd8]
        rw [TM.runConfig_add, ← hd9]
        rw [TM.runConfig_add, ← hd10]
        rw [TM.runConfig_add, ← hd11]
        rw [TM.runConfig_add, ← hd12]
        rw [TM.runConfig_add, ← hd13]
        rw [TM.runConfig_add, ← hd14]
        rw [TM.runConfig_add, ← hd15]
        rw [TM.runConfig_add, ← hd16]
        rw [TM.runConfig_add, ← hd17]
      -- The budget.
      have hwzc := walkZoneSteps_le (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
      have hwzv := walkZoneSteps_le (val.map (· + 2))
      rw [hctrlwz] at hwzc
      rw [hvalwz] at hwzv
      refine ⟨2 + (4 + (2 + (2 + (2 + (2 + (2 + ((constMarkBlock.length + 1) + (2 + (2
            + ((((d10.head : Nat) - (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)) + 2)
            + ((walkZoneSteps (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1)
            + ((((d12.head : Nat) - (z.shwBase + k)) + 2)
            + ((((d13.head : Nat) - (z.shwBase - 1)) + 2)
            + ((((d14.head : Nat) - (vtop - 1)) + 2)
            + ((walkZoneSteps (val.map (· + 2)) + 1)
            + ((((d16.head : Nat) - fm) + 2)
            + ((constRecBlock false).length + 1))))))))))))))))), ?_, ?_, ?_, ?_⟩
      · simp only [constMarkBlock_length, constRecBlock_length]
        omega
      · rw [hfinal, p18]
      · rw [hfinal, hh18]
      · rw [hfinal, ht18]

  | true =>
      obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
        hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
      replace hcert : windowSpells c0.tape
          (z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.const true) :: toks')).length)
          (encodePreorder width h_width (PreToken.leaf (SLGate.const true) :: toks')) := hcert
      replace hcfit : z.certBase + (encodePreorder width h_width
          (PreToken.leaf (SLGate.const true) :: toks')).length ≤ z.certEnd := hcfit
      replace hcorr : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
          (p : Nat) < z.certEnd
            - (encodePreorder width h_width
                (PreToken.leaf (SLGate.const true) :: toks')).length - 1 →
          c0.tape p = false := hcorr
      replace hFM : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = z.workBase + (encodeGateRecordStream out).length → c0.tape p = true := hFM
      replace hffit : z.workBase + (encodeGateRecordStream out).length + 1 ≤ z.workEnd := hffit
      replace hfzeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.workBase + (encodeGateRecordStream out).length + 1 ≤ (p : Nat) →
          (p : Nat) < z.valBase → c0.tape p = false := hfzeros
      replace hval : windowSpells c0.tape z.valBase (encodeNatStackR val) := hval
      replace hvfit : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
      replace hvzeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.valBase + (encodeNatStackR val).length ≤ (p : Nat) →
          (p : Nat) < z.shwBase → c0.tape p = false := hvzeros
      replace hshw : windowSpells c0.tape z.shwBase
          (List.replicate (out.length + 1) true) := hshw
      replace hsfit : z.shwBase + out.length + 1 ≤ z.shwEnd := hsfit
      replace hszeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          z.shwBase + out.length + 1 ≤ (p : Nat) → (p : Nat) < z.ctrlBase →
          c0.tape p = false := hszeros
      replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR ctrl) := hctrlw
      replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ z.ctrlEnd := hcfit2
      have henc_len : (encodePreorder width h_width
          (PreToken.leaf (SLGate.const true) :: toks')).length
          = 4 + (encodePreorder width h_width toks').length := by
        rw [show encodePreorder width h_width (PreToken.leaf (SLGate.const true) :: toks')
            = [false, false, true, true] ++ encodePreorder width h_width toks' from by
          rw [encodePreorder_cons]; rfl]
        rw [List.length_append]
        rfl
      set CUR := z.certEnd - (encodePreorder width h_width
          (PreToken.leaf (SLGate.const true) :: toks')).length with hCUR
      set fm := z.workBase + (encodeGateRecordStream out).length with hfm
      set vtop := z.valBase + (encodeNatStackR val).length with hvtop
      set k := out.length with hk
      have hvallen1 : 1 ≤ (encodeNatStackR val).length := by
        cases hv : encodeNatStackR val with
        | nil =>
            have := encodeNatStackR_getLast_true val
            rw [hv] at this; simp at this
        | cons a l => simp
      have hctrllen1 : 1 ≤ (encodeCtrlStackR ctrl).length := by
        cases hv : encodeCtrlStackR ctrl with
        | nil =>
            have := encodeCtrlStackR_getLast_true ctrl
            rw [hv] at this; simp at this
        | cons a l => simp
      have hgapMC : z.ctrlBase + (encodeCtrlStackR ctrl).length + 2 ≤ CUR - 1 := by omega
      have hbits : encodePreorder width h_width (PreToken.leaf (SLGate.const true) :: toks')
          = [false, false, true, true] ++ encodePreorder width h_width toks' := by
        rw [encodePreorder_cons]; rfl
      have hcl0 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR → c0.tape p = false := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 0 from by omega]
        rfl
      have hcl1 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR + 1 → c0.tape p = false := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 1 from by omega]
        rfl
      have hcl2 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR + 2 → c0.tape p = true := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 2 from by omega]
        rfl
      have hcl3 : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          (p : Nat) = CUR + 3 → c0.tape p = true := by
        intro p hp
        have := hcert.2 p (by omega) (by omega)
        rw [this, hbits, show (p : Nat) - CUR = 3 from by omega]
        rfl
      -- L1 (step right 0 → 2): off the marker onto the token's first cell.
      obtain ⟨p1, h1c, t1⟩ := constIter_region_sR_0.run_stepRight_hop c0 hphase0
        (by have := constIter_len L; omega)
      set d1 := TM.runConfig (M := constIterProgram.toPhased.toTM) c0 2 with hd1
      have hh1 : (d1.head : Nat) = CUR := by rw [h1c]; omega
      -- L2 (certTrie const hop 2 → 14): read `fft`, land on the value bit.
      obtain ⟨p2, h2c, t2⟩ := constIter_region_trie_2.run_certTrie_const_hop
        rfl rfl rfl rfl
        d1 p1 (by have := constIter_len L; omega)
        (by rw [t1]; exact hcl0 d1.head (by omega))
        (fun p hp => by rw [t1]; exact hcl1 p (by omega))
        (fun p hp => by rw [t1]; exact hcl2 p (by omega))
      set d2 := TM.runConfig (M := constIterProgram.toPhased.toTM) d1 4 with hd2
      have hh2 : (d2.head : Nat) = CUR + 3 := by rw [h2c]; omega
      have ht2 : d2.tape = c0.tape := by rw [t2, t1]
      -- L3 (bit probe 14 → chain): read the value bit in place.
      obtain ⟨p3, h3c, t3⟩ := constIter_region_probe_14.run_bitProbe_one_hop
        rfl rfl
        d2 p2
        (by rw [ht2]; exact hcl3 d2.head (by omega))
      set d3 := TM.runConfig (M := constIterProgram.toPhased.toTM) d2 2 with hd3
      have hh3 : (d3.head : Nat) = CUR + 3 := by rw [h3c]; omega
      have ht3 : d3.tape = c0.tape := by rw [t3, ht2]
      -- L4–L7 (4 × step left): back across the consumed token onto the old marker.
      obtain ⟨p4, h4c, t4⟩ := constIter_region_sL7_60.run_stepLeft_hop d3 p3 (by omega)
      set d4 := TM.runConfig (M := constIterProgram.toPhased.toTM) d3 2 with hd4
      have hh4 : (d4.head : Nat) = CUR + 2 := by rw [h4c]; omega
      obtain ⟨p5, h5c, t5⟩ := constIter_region_sL8_62.run_stepLeft_hop d4 p4 (by omega)
      set d5 := TM.runConfig (M := constIterProgram.toPhased.toTM) d4 2 with hd5
      have hh5 : (d5.head : Nat) = CUR + 1 := by rw [h5c]; omega
      obtain ⟨p6, h6c, t6⟩ := constIter_region_sL9_64.run_stepLeft_hop d5 p5 (by omega)
      set d6 := TM.runConfig (M := constIterProgram.toPhased.toTM) d5 2 with hd6
      have hh6 : (d6.head : Nat) = CUR := by rw [h6c]; omega
      obtain ⟨p7, h7c, t7⟩ := constIter_region_sL10_66.run_stepLeft_hop d6 p6 (by omega)
      set d7 := TM.runConfig (M := constIterProgram.toPhased.toTM) d6 2 with hd7
      have hh7 : (d7.head : Nat) = CUR - 1 := by rw [h7c]; omega
      have ht7 : d7.tape = c0.tape := by rw [t7, t6, t5, t4, ht3]
      -- L8 (the marker block 25/68 → next): `[0,0,0,0,1]` from the old marker.
      obtain ⟨p8, h8c, t8⟩ := constIter_region_mark2_68.run_writeBits_hop d7 p7
        (by simp only [constMarkBlock_length]; have := constIter_len L; omega)
      set d8 := TM.runConfig (M := constIterProgram.toPhased.toTM) d7
        (constMarkBlock.length + 1) with hd8
      have hh8 : (d8.head : Nat) = CUR + 4 := by
        rw [h8c]
        simp only [constMarkBlock_length]
        omega
      have ht8 : d8.tape = writeBlockTape c0.tape (CUR - 1) constMarkBlock := by
        rw [t8, hh7, ht7]
      have ht8_off : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          ¬ (CUR - 1 ≤ (p : Nat) ∧ (p : Nat) < CUR + 4) →
          d8.tape p = c0.tape p := by
        intro p hp
        rw [ht8]
        unfold writeBlockTape
        rw [if_neg (by rw [constMarkBlock_length]; omega)]
      have ht8_zeros : ∀ p : Fin (constIterProgram.toPhased.toTM.tapeLength L),
          CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 3 → d8.tape p = false := by
        intro p hp1 hp2
        rw [ht8]
        unfold writeBlockTape
        rw [if_pos (by rw [constMarkBlock_length]; omega)]
        have h4 : (p : Nat) - (CUR - 1) = 0 ∨ (p : Nat) - (CUR - 1) = 1
            ∨ (p : Nat) - (CUR - 1) = 2 ∨ (p : Nat) - (CUR - 1) = 3 := by omega
        rcases h4 with h | h | h | h <;> rw [h] <;> rfl
      -- L9–L10 (2 × step left): off the rewritten block onto the dead cell `CUR + 2`.
      obtain ⟨p9, h9c, t9⟩ := constIter_region_sL11_74.run_stepLeft_hop d8 p8 (by omega)
      set d9 := TM.runConfig (M := constIterProgram.toPhased.toTM) d8 2 with hd9
      have hh9 : (d9.head : Nat) = CUR + 3 := by rw [h9c]; omega
      obtain ⟨p10, h10c, t10⟩ := constIter_region_sL12_76.run_stepLeft_hop d9 p9 (by omega)
      set d10 := TM.runConfig (M := constIterProgram.toPhased.toTM) d9 2 with hd10
      have hh10 : (d10.head : Nat) = CUR + 2 := by rw [h10c]; omega
      have ht10 : d10.tape = d8.tape := by rw [t10, t9]
      -- L11 (scan left 35/78 → next): onto the control stack's top content cell.
      obtain ⟨p11, h11c, t11⟩ := constIter_region_scanL5_78.run_scanLeft_hop d10 p10
        (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht10]
          by_cases hp : (p : Nat) < CUR - 1
          · rw [ht8_off p (by omega)]
            exact hcorr p (by omega) (by omega)
          · exact ht8_zeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht10, ht8_off p (by omega)]
          exact windowSpells_getLast_true c0.tape z.ctrlBase _ hctrlw
            (encodeCtrlStackR_getLast_true ctrl) p (by omega))
      set d11 := TM.runConfig (M := constIterProgram.toPhased.toTM) d10
        (((d10.head : Nat) - (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)) + 2) with hd11
      have hh11 : (d11.head : Nat) = z.ctrlBase + (encodeCtrlStackR ctrl).length - 1 := by
        rw [h11c]
      have ht11 : d11.tape = d8.tape := by rw [t11, ht10]
      -- L12 (walk the control zone leftward 37/80 → next): park on `ctrlBase − 1`.
      have hctrlwz : (walkZone (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])).length
          = (encodeCtrlStackR ctrl).length := by
        rw [encodeCtrlStackR_eq_walkZone]
      obtain ⟨p12, h12c, t12⟩ := constIter_region_walkL3_80.run_walkZoneLeft_hop
        (by intro j hj; unfold exitAt; rw [if_neg (by omega)])
        (by unfold exitAt; rw [if_pos rfl])
        d11 (hlen_of_le (Nat.le_succ L)) p11
        (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
        (by
          intro x hx
          rw [List.mem_flatMap] at hx
          obtain ⟨f, hf, hxf⟩ := hx
          have := hrem f hf
          simp only [List.mem_cons] at hxf
          rcases hxf with rfl | rfl | hfalse
          · omega
          · omega
          · simp at hfalse)
        z.ctrlBase (by omega)
        (by rw [hh11, hctrlwz])
        (by have := walkL_len L; omega)
        (by
          rw [ht11]
          refine ⟨by rw [hctrlwz]; have := constIter_len L; omega, fun q hlo hhi => ?_⟩
          rw [hctrlwz] at hhi
          rw [ht8_off q (by omega),
            show walkZone (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
              = encodeCtrlStackR ctrl from (encodeCtrlStackR_eq_walkZone ctrl).symm]
          exact hctrlw.2 q hlo (by omega))
        (fun p hp => by
          rw [ht11, ht8_off p (by omega)]
          exact hszeros p (by omega) (by omega))
      set d12 := TM.runConfig (M := constIterProgram.toPhased.toTM) d11
        (walkZoneSteps (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1) with hd12
      have hh12 : (d12.head : Nat) = z.ctrlBase - 1 := by rw [h12c]
      have ht12 : d12.tape = d8.tape := by rw [t12, ht11]
      -- L13 (scan left 42/85 → next): onto the `SHW` window's top `1`.
      obtain ⟨p13, h13c, t13⟩ := constIter_region_scanL6_85.run_scanLeft_hop d12 p12
        (z.shwBase + k)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht12, ht8_off p (by omega)]
          exact hszeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht12, ht8_off p (by omega)]
          obtain ⟨hf, hc⟩ := hshw
          have := hc p (by omega) (by rw [List.length_replicate]; omega)
          rw [this]
          exact getD_replicate_of_lt true false (by omega))
      set d13 := TM.runConfig (M := constIterProgram.toPhased.toTM) d12
        (((d12.head : Nat) - (z.shwBase + k)) + 2) with hd13
      have hh13 : (d13.head : Nat) = z.shwBase + k := by rw [h13c]
      have ht13 : d13.tape = d8.tape := by rw [t13, ht12]
      -- L14 (ones-scan left 44/87 → next): across `SHW` onto the dead cell `shwBase − 1`.
      obtain ⟨p14, h14c, t14⟩ := constIter_region_scanL12_87.run_scanLeftOne_hop d13 p13
        (z.shwBase - 1)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht13, ht8_off p (by omega)]
          obtain ⟨hf, hc⟩ := hshw
          have := hc p (by omega) (by rw [List.length_replicate]; omega)
          rw [this]
          exact getD_replicate_of_lt true false (by omega))
        (fun p hp => by
          rw [ht13, ht8_off p (by omega)]
          exact hvzeros p (by omega) (by omega))
      set d14 := TM.runConfig (M := constIterProgram.toPhased.toTM) d13
        (((d13.head : Nat) - (z.shwBase - 1)) + 2) with hd14
      have hh14 : (d14.head : Nat) = z.shwBase - 1 := by rw [h14c]
      have ht14 : d14.tape = d8.tape := by rw [t14, ht13]
      -- L15 (scan left 46/89 → next): onto the value stack's top content cell.
      obtain ⟨p15, h15c, t15⟩ := constIter_region_scanL7_89.run_scanLeft_hop d14 p14
        (vtop - 1)
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht14, ht8_off p (by omega)]
          exact hvzeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht14, ht8_off p (by omega)]
          exact windowSpells_getLast_true c0.tape z.valBase _ hval
            (encodeNatStackR_getLast_true val) p (by omega))
      set d15 := TM.runConfig (M := constIterProgram.toPhased.toTM) d14
        (((d14.head : Nat) - (vtop - 1)) + 2) with hd15
      have hh15 : (d15.head : Nat) = vtop - 1 := by rw [h15c]
      have ht15 : d15.tape = d8.tape := by rw [t15, ht14]
      -- L16 (walk the value zone leftward 48/91 → next): park on `valBase − 1`.
      have hvalwz : (walkZone (val.map (· + 2))).length = (encodeNatStackR val).length := by
        rw [encodeNatStackR_eq_walkZone]
      obtain ⟨p16, h16c, t16⟩ := constIter_region_walkL4_91.run_walkZoneLeft_hop
        (by intro j hj; unfold exitAt; rw [if_neg (by omega)])
        (by unfold exitAt; rw [if_pos rfl])
        d15 (hlen_of_le (Nat.le_succ L)) p15
        (val.map (· + 2))
        (by intro x hx; rw [List.mem_map] at hx; obtain ⟨v, -, rfl⟩ := hx; omega)
        z.valBase (by omega)
        (by rw [hh15, hvalwz])
        (by have := walkL_len L; omega)
        (by
          rw [ht15]
          refine ⟨by rw [hvalwz]; have := constIter_len L; omega, fun q hlo hhi => ?_⟩
          rw [hvalwz] at hhi
          rw [ht8_off q (by omega),
            show walkZone (val.map (· + 2)) = encodeNatStackR val from
              (encodeNatStackR_eq_walkZone val).symm]
          exact hval.2 q hlo (by omega))
        (fun p hp => by
          rw [ht15, ht8_off p (by omega)]
          exact hfzeros p (by omega) (by omega))
      set d16 := TM.runConfig (M := constIterProgram.toPhased.toTM) d15
        (walkZoneSteps (val.map (· + 2)) + 1) with hd16
      have hh16 : (d16.head : Nat) = z.valBase - 1 := by rw [h16c]
      have ht16 : d16.tape = d8.tape := by rw [t16, ht15]
      -- L17 (scan left 53/96 → next): onto the frontier marker `FM`.
      obtain ⟨p17, h17c, t17⟩ := constIter_region_scanL8_96.run_scanLeft_hop d16 p16
        fm
        (by omega)
        (fun p hp1 hp2 => by
          rw [ht16, ht8_off p (by omega)]
          exact hfzeros p (by omega) (by omega))
        (fun p hp => by
          rw [ht16, ht8_off p (by omega)]
          exact hFM p (by omega))
      set d17 := TM.runConfig (M := constIterProgram.toPhased.toTM) d16
        (((d16.head : Nat) - fm) + 2) with hd17
      have hh17 : (d17.head : Nat) = fm := by rw [h17c]
      have ht17 : d17.tape = d8.tape := by rw [t17, ht16]
      -- L18 (the record-plus-replant block 55/98 → 103): `[1,0,b,1]` at `FM`.
      obtain ⟨p18, h18c, t18⟩ := constIter_region_rec1_98.run_writeBits_hop d17 p17
        (by simp only [constRecBlock_length]; have := constIter_len L; omega)
      set d18 := TM.runConfig (M := constIterProgram.toPhased.toTM) d17
        ((constRecBlock true).length + 1) with hd18
      have hh18 : (d18.head : Nat) = fm + 4 := by
        rw [h18c, hh17]
        simp only [constRecBlock_length]
      have ht18 : d18.tape = writeBlockTape
          (writeBlockTape c0.tape (CUR - 1) constMarkBlock) fm (constRecBlock true) := by
        rw [t18, hh17, ht17, ht8]
      -- Assemble the chain.
      have hfinal : TM.runConfig (M := constIterProgram.toPhased.toTM) c0
          (2 + (4 + (2 + (2 + (2 + (2 + (2 + ((constMarkBlock.length + 1) + (2 + (2
            + ((((d10.head : Nat) - (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)) + 2)
            + ((walkZoneSteps (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1)
            + ((((d12.head : Nat) - (z.shwBase + k)) + 2)
            + ((((d13.head : Nat) - (z.shwBase - 1)) + 2)
            + ((((d14.head : Nat) - (vtop - 1)) + 2)
            + ((walkZoneSteps (val.map (· + 2)) + 1)
            + ((((d16.head : Nat) - fm) + 2)
            + ((constRecBlock true).length + 1))))))))))))))))))
          = d18 := by
        rw [TM.runConfig_add, ← hd1]
        rw [TM.runConfig_add, ← hd2]
        rw [TM.runConfig_add, ← hd3]
        rw [TM.runConfig_add, ← hd4]
        rw [TM.runConfig_add, ← hd5]
        rw [TM.runConfig_add, ← hd6]
        rw [TM.runConfig_add, ← hd7]
        rw [TM.runConfig_add, ← hd8]
        rw [TM.runConfig_add, ← hd9]
        rw [TM.runConfig_add, ← hd10]
        rw [TM.runConfig_add, ← hd11]
        rw [TM.runConfig_add, ← hd12]
        rw [TM.runConfig_add, ← hd13]
        rw [TM.runConfig_add, ← hd14]
        rw [TM.runConfig_add, ← hd15]
        rw [TM.runConfig_add, ← hd16]
        rw [TM.runConfig_add, ← hd17]
      -- The budget.
      have hwzc := walkZoneSteps_le (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1])
      have hwzv := walkZoneSteps_le (val.map (· + 2))
      rw [hctrlwz] at hwzc
      rw [hvalwz] at hwzv
      refine ⟨2 + (4 + (2 + (2 + (2 + (2 + (2 + ((constMarkBlock.length + 1) + (2 + (2
            + ((((d10.head : Nat) - (z.ctrlBase + (encodeCtrlStackR ctrl).length - 1)) + 2)
            + ((walkZoneSteps (ctrl.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) + 1)
            + ((((d12.head : Nat) - (z.shwBase + k)) + 2)
            + ((((d13.head : Nat) - (z.shwBase - 1)) + 2)
            + ((((d14.head : Nat) - (vtop - 1)) + 2)
            + ((walkZoneSteps (val.map (· + 2)) + 1)
            + ((((d16.head : Nat) - fm) + 2)
            + ((constRecBlock true).length + 1))))))))))))))))), ?_, ?_, ?_, ?_⟩
      · simp only [constMarkBlock_length, constRecBlock_length]
        omega
      · rw [hfinal, p18]
      · rw [hfinal, hh18]
      · rw [hfinal, ht18]



set_option maxHeartbeats 4000000 in
/-- **The const iteration, end to end.**  For a reading state whose next token is
`leaf (const b)` (tail nonempty), from the read home `constIterProgram` reaches the home-read out
(phase `168`) on the **new** marker with the tape exactly `corridorInv_constStep`'s transformer —
`constStepTape` followed by the `SHW` tick — within an explicit polynomial budget. -/
theorem constIter_run {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (b : Bool) (toks' : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat)
    (c0 : Configuration (M := constIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape
      (⟨PreToken.leaf (SLGate.const b) :: toks', out, ctrl, val, false⟩ : DriveState n))
    (hrem : ∀ f ∈ ctrl, 1 ≤ f.2)
    (hLfit : z.certEnd + 2 ≤ L)
    (hwcap : z.workBase + (encodeGateRecordStream out).length + 4 ≤ z.workEnd)
    (hvcap : z.valBase + (encodeNatStackR val).length + (out.length + 3) ≤ z.valEnd)
    (hscratch : z.shwBase + 2 * out.length + 2 < z.ctrlBase)
    (hphase0 : (c0.state.fst : Nat) = 0)
    (hhead0 : (c0.head : Nat) = z.certEnd
      - (encodePreorder width h_width (PreToken.leaf (SLGate.const b) :: toks')).length - 1) :
    ∃ T : Nat,
      T ≤ (out.length + 2) * (2 * z.certEnd + 6 * out.length + 20)
          + 22 * z.certEnd + 9 * out.length + 140
      ∧ (((TM.runConfig (M := constIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 168
      ∧ ((TM.runConfig (M := constIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width toks').length - 1
      ∧ (TM.runConfig (M := constIterProgram.toPhased.toTM) c0 T).tape
          = writeBlockTape
              (constStepTape c0.tape
                (z.certEnd - (encodePreorder width h_width
                  (PreToken.leaf (SLGate.const b) :: toks')).length)
                (z.valBase + (encodeNatStackR val).length)
                (z.workBase + (encodeGateRecordStream out).length)
                (encodeNatEntryR out.length)
                (encodeGateRecord (SLGate.const b : SLGate n)))
              (z.shwBase + out.length + 1) [true] := by
  obtain ⟨F, hF, pF, hF2, tF⟩ := constIter_run_front width h_width z b toks' out ctrl val c0
    hinv hrem hLfit hphase0 hhead0
  obtain ⟨T', hT', pT, hT2, tT⟩ := constIter_run_tail width h_width z b toks' out ctrl val
    c0.tape (TM.runConfig (M := constIterProgram.toPhased.toTM) c0 F)
    hinv hrem hLfit hwcap hvcap hscratch tF pF hF2
  -- The disjointness shells for the write-chain rewrite.
  have hreceq : (encodeGateRecord (SLGate.const b : SLGate n)) = [true, false, b] := rfl
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcfit : z.certBase + (encodePreorder width h_width
      (PreToken.leaf (SLGate.const b) :: toks')).length ≤ z.certEnd := hcfit
  replace hffit : z.workBase + (encodeGateRecordStream out).length + 1 ≤ z.workEnd := hffit
  replace hvfit : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ z.ctrlEnd := hcfit2
  have hctrllen1 : 1 ≤ (encodeCtrlStackR ctrl).length := by
    cases hv : encodeCtrlStackR ctrl with
    | nil =>
        have := encodeCtrlStackR_getLast_true ctrl
        rw [hv] at this; simp at this
    | cons a l => simp
  refine ⟨F + T', by omega, ?_, ?_, ?_⟩
  · rw [TM.runConfig_add]
    exact pT
  · rw [TM.runConfig_add]
    exact hT2
  · rw [TM.runConfig_add, tT, hreceq,
      ← writeConstChain_eq_constStepTape c0.tape
        (z.certEnd - (encodePreorder width h_width
          (PreToken.leaf (SLGate.const b) :: toks')).length)
        (z.valBase + (encodeNatStackR val).length)
        (z.workBase + (encodeGateRecordStream out).length)
        out.length b
        (by omega) (by omega) (by omega)]

end ContractExpansion
end Frontier
end Pnp4
