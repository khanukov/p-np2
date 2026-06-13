import Pnp4.Frontier.ContractExpansion.TreeMCSPBitProbe
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionAtomHops

/-!
# Region bit-probe hops — D2t-5b (Block A5m-6a, transfer): the in-place prober in a union

The host-generic transfer of `bitProbe` into a region union: from the region's phase `base` the
prober reads the scanned cell and, in `2` steps (the verdict step plus the redirect step), lands at
the redirect target of the outcome slot — `1` on a `0` cell, `2` on a `1` cell — head and tape
untouched.  The two hops are the leaf arms' value/index-bit branch points (`constIterProgram`
routes its `b = 0`/`b = 1` chains off these slots).

**Progress classification (AGENTS.md): Infrastructure** — host-generic run segments; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The write-back of the scanned bit leaves the tape unchanged. -/
private theorem write_self {M : TM} {L : Nat} (c : Configuration (M := M) L) :
    c.write c.head (c.tape c.head) = c.tape := by
  funext q
  by_cases hq : q = c.head
  · subst hq; simp [Configuration.write]
  · simp [Configuration.write, hq]

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- **The bit-probe hop, zero branch**: from the region's phase `base` with the scanned cell
reading `0`, `2` steps (the verdict, the redirect) end at the redirect target of the zero-outcome
slot `1`, head and tape untouched. -/
theorem run_bitProbe_zero_hop (hUP : RegionEmbeddedMulti U bitProbe base redirect) {L : Nat}
    (hred0 : redirect 0 = none) {nxt : Nat} (hred1 : redirect 1 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hbit : c0.tape c0.head = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 2).state).fst : Nat) = nxt
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 2).head = c0.head
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 2).tape = c0.tape := by
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij0 : (c0.state.fst : Nat) = base + (⟨0, by simp [bitProbe]⟩
      : Fin bitProbe.numPhases).val := by simpa using hphase
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij0 hred0]
    simp [bitProbe, hbit]
  have hhd1 : c1.head = c0.head := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij0 hred0]
    have hm : (bitProbe.transition ⟨0, by simp [bitProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.stay := by
      simp [bitProbe, hbit]
    rw [hm]
    simp [Configuration.moveHead]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij0 hred0]
    have hb : (bitProbe.transition ⟨0, by simp [bitProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [bitProbe, hbit]
    rw [hb]
    exact write_self c0
  have hij1 : (c1.state.fst : Nat) = base + (⟨1, by simp [bitProbe]⟩
      : Fin bitProbe.numPhases).val := by simpa using hph1
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c1 rfl _ hij1 hred1
  · rw [hUP.stepConfig_redirect_head c1 rfl _ hij1 hred1]; exact hhd1
  · rw [hUP.stepConfig_redirect_tape c1 rfl _ hij1 hred1]; exact htp1

/-- **The bit-probe hop, one branch**: as `run_bitProbe_zero_hop` with the scanned cell reading
`1`, ending at the redirect target of the one-outcome slot `2`. -/
theorem run_bitProbe_one_hop (hUP : RegionEmbeddedMulti U bitProbe base redirect) {L : Nat}
    (hred0 : redirect 0 = none) {nxt : Nat} (hred2 : redirect 2 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hbit : c0.tape c0.head = true) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 2).state).fst : Nat) = nxt
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 2).head = c0.head
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 2).tape = c0.tape := by
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij0 : (c0.state.fst : Nat) = base + (⟨0, by simp [bitProbe]⟩
      : Fin bitProbe.numPhases).val := by simpa using hphase
  have hph1 : (c1.state.fst : Nat) = base + 2 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij0 hred0]
    simp [bitProbe, hbit]
  have hhd1 : c1.head = c0.head := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij0 hred0]
    have hm : (bitProbe.transition ⟨0, by simp [bitProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.stay := by
      simp [bitProbe, hbit]
    rw [hm]
    simp [Configuration.moveHead]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij0 hred0]
    have hb : (bitProbe.transition ⟨0, by simp [bitProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [bitProbe, hbit]
    rw [hb]
    exact write_self c0
  have hij1 : (c1.state.fst : Nat) = base + (⟨2, by simp [bitProbe]⟩
      : Fin bitProbe.numPhases).val := by simpa using hph1
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c1 rfl _ hij1 hred2
  · rw [hUP.stepConfig_redirect_head c1 rfl _ hij1 hred2]; exact hhd1
  · rw [hUP.stepConfig_redirect_tape c1 rfl _ hij1 hred2]; exact htp1

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
