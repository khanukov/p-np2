import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionZoneWalkHop
import Pnp4.Frontier.ContractExpansion.TreeMCSPUnaryTransferRun

/-!
# Region unary-transfer hop — D2t-5b (Block A5m-2, transfer): the block mover in a union

The pop arm moves a popped value entry's unary block from the value zone down to the WORK record
site as one region of the driver union.  The native capstone (`unaryTransfer_transfers`) now
carries its per-step confinement stream, which discharges exactly `run_track`'s safety
conditions: the phase never reaches the sink `φ8` (the region's only redirect slot) and the head
stays `≤ opBase + d + γ + m`, with the strict native room supplied by the caller closing the
clamp-edge check.

`run_unaryTransfer_hop`: from the region's phase `base` at `opBase` under the transfer layout's
window facts (stated on the host tape), some `t + 1 ≤ (m−j)·(2(d+m)+2γ+8) + 1` steps land at the
sink slot's redirect target, head on the far terminator `opBase + d + γ + m`, and the **host**
tape reads: the destination block complete (`1^(d+m)`), the former gap-and-source zone all `0`,
everything outside `[opBase, opBase+d+γ+m]` verbatim.

**Progress classification (AGENTS.md): Infrastructure** — a host-generic run segment; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- **The unary-transfer hop**: from the region's phase `base` at `opBase` with the transfer
layout's window facts on the host tape and the strict native room, some
`t + 1 ≤ (m−j)·(2(d+m)+2γ+8) + 1` steps end at the sink slot's redirect target, head on
`opBase + d + γ + m`, the destination block complete, the gap-and-source zone zeroed, the rest
verbatim. -/
theorem run_unaryTransfer_hop (hUP : RegionEmbeddedMulti U unaryTransfer base redirect)
    {L : Nat}
    (hredlow : ∀ j, j < 8 → redirect j = none) {nxt : Nat} (hred8 : redirect 8 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hlen : unaryTransfer.toPhased.toTM.tapeLength L ≤ U.toPhased.toTM.tapeLength L)
    (hphase : (c0.state.fst : Nat) = base)
    (opBase d j γ m : Nat)
    (hhead : (c0.head : Nat) = opBase)
    (hopPos : 1 ≤ opBase) (hg1 : 1 ≤ γ) (hjm : j < m)
    (hroom : opBase + d + γ + m + 1 < unaryTransfer.toPhased.toTM.tapeLength L)
    (hdelim : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase - 1 → c0.tape p = false)
    (hdst : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      opBase ≤ (p : Nat) → (p : Nat) < opBase + d + j → c0.tape p = true)
    (hgap : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      opBase + d + j ≤ (p : Nat) → (p : Nat) < opBase + d + γ + j → c0.tape p = false)
    (hsrc : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      opBase + d + γ + j ≤ (p : Nat) → (p : Nat) < opBase + d + γ + m → c0.tape p = true)
    (hterm : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase + d + γ + m → c0.tape p = false) :
    ∃ t : Nat, t ≤ (m - j) * (2 * (d + m) + 2 * γ + 8) + 1
      ∧ (((TM.runConfig (M := U.toPhased.toTM) c0 t).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 t).head : Nat) = opBase + d + γ + m
      ∧ (∀ p : Fin (U.toPhased.toTM.tapeLength L),
          opBase ≤ (p : Nat) → (p : Nat) < opBase + d + m →
          (TM.runConfig (M := U.toPhased.toTM) c0 t).tape p = true)
      ∧ (∀ p : Fin (U.toPhased.toTM.tapeLength L),
          opBase + d + m ≤ (p : Nat) → (p : Nat) ≤ opBase + d + γ + m →
          (TM.runConfig (M := U.toPhased.toTM) c0 t).tape p = false)
      ∧ (∀ p : Fin (U.toPhased.toTM.tapeLength L),
          ((p : Nat) < opBase ∨ opBase + d + γ + m < (p : Nat)) →
          (TM.runConfig (M := U.toPhased.toTM) c0 t).tape p = c0.tape p) := by
  set cn0 := trackStart unaryTransfer c0 (by simp [unaryTransfer]) (by omega) hlen with hcn0
  -- The native layout, transported pointwise.
  have hlay : TransferLayout cn0 opBase d j γ m :=
    { hphase := trackStart_phase _ _ _ _ _
      hhead := by rw [trackStart_head]; exact hhead
      hopPos := hopPos
      hg1 := hg1
      hjm := by omega
      hbound := hroom
      hdelim := fun p hp => by
        show c0.tape _ = false
        exact hdelim ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp
      hdst := fun p hp1 hp2 => by
        show c0.tape _ = true
        exact hdst ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp1 hp2
      hgap := fun p hp1 hp2 => by
        show c0.tape _ = false
        exact hgap ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp1 hp2
      hsrc := fun p hp1 hp2 => by
        show c0.tape _ = true
        exact hsrc ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp1 hp2
      hterm := fun p hp => by
        show c0.tape _ = false
        exact hterm ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp }
  -- The native capstone with its confinement stream.
  obtain ⟨t, htb, hp8, hhd, hdst', hzero', hout', hstr⟩ :=
    unaryTransfer_transfers cn0 opBase d j γ m hlay hjm
  -- The coupled run.
  obtain ⟨htph, hthd, http, hthi⟩ := hUP.run_track hlen c0 cn0
    (by rw [hphase, trackStart_phase]; omega)
    (by rw [trackStart_head])
    (trackStart_tapeAgree _ _ _ _ _)
    t
    (fun s hs => by
      obtain ⟨hp, hhb⟩ := hstr s hs
      exact ⟨hredlow _ hp, by omega⟩)
  -- The redirect step at the sink slot.
  refine ⟨t + 1, by omega, ?_⟩
  rw [TM.runConfig_succ]
  set ce := TM.runConfig (M := U.toPhased.toTM) c0 t with hce
  have hij : (ce.state.fst : Nat) = base + ((⟨8, by simp [unaryTransfer]⟩
      : Fin unaryTransfer.numPhases)).val := by
    rw [hce, htph, hp8]
  have hehd : (ce.head : Nat) = opBase + d + γ + m := by
    rw [hce, hthd, hhd]
  have hedst : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      opBase ≤ (p : Nat) → (p : Nat) < opBase + d + m → ce.tape p = true := by
    intro p hp1 hp2
    have hplt : (p : Nat) < unaryTransfer.toPhased.toTM.tapeLength L := by omega
    have := http p ⟨(p : Nat), hplt⟩ rfl
    rw [hce, this]
    exact hdst' ⟨(p : Nat), hplt⟩ hp1 hp2
  have hezero : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      opBase + d + m ≤ (p : Nat) → (p : Nat) ≤ opBase + d + γ + m → ce.tape p = false := by
    intro p hp1 hp2
    have hplt : (p : Nat) < unaryTransfer.toPhased.toTM.tapeLength L := by omega
    have := http p ⟨(p : Nat), hplt⟩ rfl
    rw [hce, this]
    exact hzero' ⟨(p : Nat), hplt⟩ hp1 hp2
  have heout : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      ((p : Nat) < opBase ∨ opBase + d + γ + m < (p : Nat)) → ce.tape p = c0.tape p := by
    intro p hp
    by_cases hplt : (p : Nat) < unaryTransfer.toPhased.toTM.tapeLength L
    · have hagree := http p ⟨(p : Nat), hplt⟩ rfl
      rw [hce, hagree, hout' ⟨(p : Nat), hplt⟩ hp]
      show c0.tape _ = c0.tape p
      congr 1
    · rw [hce]
      exact hthi p (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase ce rfl _ hij hred8
  · rw [hUP.stepConfig_redirect_head ce rfl _ hij hred8]
    exact hehd
  · intro p hp1 hp2
    rw [hUP.stepConfig_redirect_tape ce rfl _ hij hred8]
    exact hedst p hp1 hp2
  · intro p hp1 hp2
    rw [hUP.stepConfig_redirect_tape ce rfl _ hij hred8]
    exact hezero p hp1 hp2
  · intro p hp
    rw [hUP.stepConfig_redirect_tape ce rfl _ hij hred8]
    exact heout p hp

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
