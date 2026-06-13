import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionZoneWalkHop
import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushHeadline

/-!
# Region value-push hop — D2t-5b (Block A5m-6a, transfer): the M1 fan-out in a union

The leaf/pop arms run the whole A5m-V value-push machine as one region of the driver union.  Its
native headline (`valuePush_pushes_writeBlock`) carries the M2-confinement per-step stream, which
discharges exactly `run_track`'s safety conditions: the phase never reaches the exit `φ34` (the
region's only redirect slot), and the head stays `≤ aPos + 2k + 2` — with the **strict** native
room `aPos + 2k + 3 < tapeLength` supplied from the corridor geometry, that closes `run_track`'s
clamp-edge check (the strictness obligation documented on the native headline).

`run_valuePush_hop`: from the region's phase `base` at the value frontier `opBase` under the
layout's window facts (stated on the host tape), some `t + 1 ≤ (k+2)·(2·(aPos−opBase)+6k+20) + 1`
steps land at the exit slot's redirect target, head back on `opBase`, and the **host** tape is
exactly `writeBlockTape c0.tape opBase (encodeNatEntryR k)` — the value entry written, everything
else (including the `SHW` source, restored in place) verbatim.

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

/-- **The value-push hop**: from the region's phase `base` at the value frontier `opBase`, with
the layout's window facts on the host tape and the strict native room, some
`t + 1 ≤ (k+2)·(2·(aPos−opBase)+6k+20) + 1` steps end at the exit slot's redirect target, head on
`opBase`, host tape exactly `writeBlockTape c0.tape opBase (encodeNatEntryR k)`. -/
theorem run_valuePush_hop (hUP : RegionEmbeddedMulti U valuePushProgram base redirect) {L : Nat}
    (hredlow : ∀ j, j < 34 → redirect j = none) {nxt : Nat} (hred34 : redirect 34 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hlen : valuePushProgram.toPhased.toTM.tapeLength L ≤ U.toPhased.toTM.tapeLength L)
    (hphase : (c0.state.fst : Nat) = base)
    (opBase aPos k : Nat)
    (hhead : (c0.head : Nat) = opBase)
    (hgeom : opBase + k + 4 ≤ aPos)
    (hroom : aPos + 2 * k + 3 < valuePushProgram.toPhased.toTM.tapeLength L)
    (hzeroL : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      opBase ≤ (p : Nat) → (p : Nat) < aPos → c0.tape p = false)
    (hanchor : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = aPos → c0.tape p = true)
    (hsrc : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      aPos < (p : Nat) → (p : Nat) ≤ aPos + k → c0.tape p = true)
    (hzeroR : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      aPos + k < (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c0.tape p = false) :
    ∃ t : Nat, t ≤ (k + 2) * (2 * (aPos - opBase) + 6 * k + 20) + 1
      ∧ (((TM.runConfig (M := U.toPhased.toTM) c0 t).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 t).head : Nat) = opBase
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 t).tape
          = writeBlockTape c0.tape opBase (encodeNatEntryR k) := by
  set cn0 := trackStart valuePushProgram c0 (by simp [valuePushProgram]) (by omega) hlen
    with hcn0
  -- The native layout, transported pointwise.
  have hlay : ValuePushLayout cn0 opBase aPos k :=
    { hphase := trackStart_phase _ _ _ _ _
      hhead := by rw [trackStart_head]; exact hhead
      hgeom := hgeom
      hbound := by omega
      hzeroL := fun p hp1 hp2 => by
        show c0.tape _ = false
        exact hzeroL ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp1 hp2
      hanchor := fun p hp => by
        show c0.tape _ = true
        exact hanchor ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp
      hsrc := fun p hp1 hp2 => by
        show c0.tape _ = true
        exact hsrc ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp1 hp2
      hzeroR := fun p hp1 hp2 => by
        show c0.tape _ = false
        exact hzeroR ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp1 hp2 }
  -- The native headline with its confinement stream.
  obtain ⟨t, ht, hp34, hh, htape, hstream⟩ := valuePush_pushes_writeBlock cn0 opBase aPos k hlay
  -- The coupled run: the stream discharges run_track's safety conditions (the strict native room
  -- closes the clamp-edge check).
  obtain ⟨htph, hthd, http, hthi⟩ := hUP.run_track hlen c0 cn0
    (by rw [hphase, trackStart_phase]; omega)
    (by rw [trackStart_head])
    (trackStart_tapeAgree _ _ _ _ _)
    t
    (fun s hs => by
      obtain ⟨hp, hhb⟩ := hstream s hs
      have hplt : (((TM.runConfig (M := valuePushProgram.toPhased.toTM) cn0 s).state).fst : Nat)
          < 35 := by
        have := ((TM.runConfig (M := valuePushProgram.toPhased.toTM) cn0 s).state).fst.isLt
        simpa using this
      exact ⟨hredlow _ (by omega), by omega⟩)
  -- The redirect step at the exit slot.
  refine ⟨t + 1, by omega, ?_⟩
  rw [TM.runConfig_succ]
  set ce := TM.runConfig (M := U.toPhased.toTM) c0 t with hce
  have hij : (ce.state.fst : Nat) = base + ((⟨34, by simp [valuePushProgram]⟩
      : Fin valuePushProgram.numPhases)).val := by
    rw [hce, htph, hp34]
  have hehd : (ce.head : Nat) = opBase := by
    rw [hce, hthd, hh]
  have hetp : ce.tape = writeBlockTape c0.tape opBase (encodeNatEntryR k) := by
    funext q
    by_cases hq : (q : Nat) < valuePushProgram.toPhased.toTM.tapeLength L
    · have hagree := http q ⟨(q : Nat), hq⟩ rfl
      rw [hce, hagree, htape]
      show writeBlockTape cn0.tape opBase (encodeNatEntryR k) _
          = writeBlockTape c0.tape opBase (encodeNatEntryR k) q
      unfold writeBlockTape
      by_cases hin : opBase ≤ (q : Nat) ∧ (q : Nat) < opBase + (encodeNatEntryR k).length
      · rw [if_pos hin, if_pos hin]
      · rw [if_neg hin, if_neg hin]
        show c0.tape _ = c0.tape q
        congr 1
    · have hhi := hthi q (by omega)
      rw [hce, hhi]
      unfold writeBlockTape
      rw [if_neg (by
        rw [encodeNatEntryR_length]
        omega)]
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase ce rfl _ hij hred34
  · rw [hUP.stepConfig_redirect_head ce rfl _ hij hred34]
    exact hehd
  · rw [hUP.stepConfig_redirect_tape ce rfl _ hij hred34]
    exact hetp

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
