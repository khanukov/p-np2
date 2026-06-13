import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionRunTransfer
import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalkRightFull

/-!
# Region zone-walk hops — D2t-5b (Block A5m-6a, transfer): the full-zone walkers in a union

The const/input arms cross whole stack zones inside the driver union.  Re-running the walkers'
zone inductions on the host would duplicate them; instead this module rides
`RegionEmbeddedMulti.run_track`: the walkers' native capstones now carry per-step confinement
streams (A4w), which discharge exactly `run_track`'s safety conditions, and the coupling
transports the whole native run into the host in one theorem per direction.

* `trackStart` — the native configuration a host hop constructs: the component's phase `0`, the
  host's head position, the host tape restricted to the native range (its `TapeAgree` coupling
  holds by construction);
* `RegionEmbeddedMulti.run_walkZoneLeft_hop` — from the region's base phase on the zone's
  rightmost content cell, `walkZoneSteps ks + 1` steps (the walk plus the redirect) land at the
  done slot's redirect target on the dead cell `zbase − 1`, host tape untouched;
* `RegionEmbeddedMulti.run_walkZoneRight_hop` — the rightward mirror from the base sentinel,
  `walkZoneStepsR ks + 1` steps to the second dead cell past the zone's content.

**Progress classification (AGENTS.md): Infrastructure** — host-generic run segments; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The tracked component's start configuration**: the component's phase `0`, the host's head
position, the host tape restricted to the native range. -/
def trackStart (P : ConstStatePhasedProgram Unit) {U : ConstStatePhasedProgram Unit} {L : Nat}
    (ch : Configuration (M := U.toPhased.toTM) L)
    (hpos : 0 < P.numPhases)
    (hhd : (ch.head : Nat) < P.toPhased.toTM.tapeLength L)
    (hlen : P.toPhased.toTM.tapeLength L ≤ U.toPhased.toTM.tapeLength L) :
    Configuration (M := P.toPhased.toTM) L where
  state := ⟨⟨0, hpos⟩, ()⟩
  head := ⟨(ch.head : Nat), hhd⟩
  tape := fun qn => ch.tape ⟨(qn : Nat), lt_of_lt_of_le qn.isLt hlen⟩

@[simp] theorem trackStart_phase (P : ConstStatePhasedProgram Unit)
    {U : ConstStatePhasedProgram Unit} {L : Nat}
    (ch : Configuration (M := U.toPhased.toTM) L) (hpos hhd hlen) :
    (((trackStart P ch hpos hhd hlen).state).fst : Nat) = 0 := rfl

@[simp] theorem trackStart_head (P : ConstStatePhasedProgram Unit)
    {U : ConstStatePhasedProgram Unit} {L : Nat}
    (ch : Configuration (M := U.toPhased.toTM) L) (hpos hhd hlen) :
    ((trackStart P ch hpos hhd hlen).head : Nat) = (ch.head : Nat) := rfl

theorem trackStart_tapeAgree (P : ConstStatePhasedProgram Unit)
    {U : ConstStatePhasedProgram Unit} {L : Nat}
    (ch : Configuration (M := U.toPhased.toTM) L) (hpos hhd hlen) :
    TapeAgree ch (trackStart P ch hpos hhd hlen) := by
  intro qh qn hq
  show ch.tape qh = ch.tape ⟨(qn : Nat), lt_of_lt_of_le qn.isLt hlen⟩
  congr 1
  exact Fin.ext hq

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- **The leftward full-zone walk hop**: from the region's phase `base` on the rightmost content
cell of a zone spelling `walkZone ks` (every block `≥ 2`, the dead `0` at `zbase − 1`),
`walkZoneSteps ks + 1` steps (the walk plus the redirect) end at the done slot's redirect target,
head on `zbase − 1`, host tape untouched. -/
theorem run_walkZoneLeft_hop (hUP : RegionEmbeddedMulti U zoneWalkLeft base redirect) {L : Nat}
    (hredlow : ∀ j, j < 4 → redirect j = none) {nxt : Nat} (hred4 : redirect 4 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hlen : zoneWalkLeft.toPhased.toTM.tapeLength L ≤ U.toPhased.toTM.tapeLength L)
    (hphase : (c0.state.fst : Nat) = base)
    (ks : List Nat) (hks : ∀ k ∈ ks, 2 ≤ k) (zbase : Nat) (hzbase : 1 ≤ zbase)
    (hhead : (c0.head : Nat) = zbase + (walkZone ks).length - 1)
    (hroom : (c0.head : Nat) + 1 < zoneWalkLeft.toPhased.toTM.tapeLength L)
    (hwin : windowSpells c0.tape zbase (walkZone ks))
    (hdead : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = zbase - 1 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneSteps ks + 1)).state).fst : Nat) = nxt
    ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneSteps ks + 1)).head : Nat) = zbase - 1
    ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneSteps ks + 1)).tape = c0.tape := by
  set cn0 := trackStart zoneWalkLeft c0 (by simp [zoneWalkLeft]) (by omega) hlen with hcn0
  -- The native window/dead facts, transported pointwise.
  have hfit : zbase + (walkZone ks).length ≤ zoneWalkLeft.toPhased.toTM.tapeLength L := by
    omega
  have hnwin : windowSpells cn0.tape zbase (walkZone ks) := by
    refine ⟨hfit, fun q hlo hhi => ?_⟩
    show c0.tape _ = _
    exact hwin.2 ⟨(q : Nat), lt_of_lt_of_le q.isLt hlen⟩ hlo hhi
  have hndead : ∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
      (p : Nat) = zbase - 1 → cn0.tape p = false := by
    intro p hp
    show c0.tape _ = false
    exact hdead ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp
  -- The native walk with its stream.
  obtain ⟨hw1, hw2, hw3, hw4⟩ := zoneWalkLeft_runConfig_walkZone cn0 ks hks zbase hzbase
    (trackStart_phase _ _ _ _ _) (by rw [trackStart_head]; exact hhead) hnwin hndead
  -- The coupled run.
  obtain ⟨htph, hthd, http, hthi⟩ := hUP.run_track hlen c0 cn0
    (by rw [hphase, trackStart_phase]; omega)
    (by rw [trackStart_head])
    (trackStart_tapeAgree _ _ _ _ _)
    (walkZoneSteps ks)
    (fun s hs => by
      obtain ⟨hp4, hhb⟩ := hw4 s hs
      refine ⟨hredlow _ hp4, ?_⟩
      have hhb' : ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) cn0 s).head : Nat)
          ≤ (cn0.head : Nat) := hhb
      rw [trackStart_head] at hhb'
      omega)
  -- The redirect step at the done slot.
  rw [TM.runConfig_succ]
  set ce := TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneSteps ks) with hce
  have hij : (ce.state.fst : Nat) = base + ((⟨4, by simp [zoneWalkLeft]⟩
      : Fin zoneWalkLeft.numPhases)).val := by
    rw [hce, htph, hw1]
  have hehd : (ce.head : Nat) = zbase - 1 := by
    rw [hce, hthd, hw2]
  have hetp : ce.tape = c0.tape := by
    funext q
    by_cases hq : (q : Nat) < zoneWalkLeft.toPhased.toTM.tapeLength L
    · have := http q ⟨(q : Nat), hq⟩ rfl
      rw [hce, this, hw3]
      show c0.tape _ = c0.tape q
      congr 1
    · exact hthi q (by omega)
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase ce rfl _ hij hred4
  · rw [hUP.stepConfig_redirect_head ce rfl _ hij hred4]
    exact hehd
  · rw [hUP.stepConfig_redirect_tape ce rfl _ hij hred4]
    exact hetp

/-- **The rightward full-zone walk hop**: from the region's phase `base` on the base sentinel of a
zone spelling `walkZone ks` (every block `≥ 2`, the two dead cells past the content pinned),
`walkZoneStepsR ks + 1` steps (the walk plus the redirect) end at the done slot's redirect target,
head on the second dead cell `zbase + |walkZone ks| + 1`, host tape untouched. -/
theorem run_walkZoneRight_hop (hUP : RegionEmbeddedMulti U zoneWalkRight base redirect) {L : Nat}
    (hredlow : ∀ j, j < 4 → redirect j = none) {nxt : Nat} (hred4 : redirect 4 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hlen : zoneWalkRight.toPhased.toTM.tapeLength L ≤ U.toPhased.toTM.tapeLength L)
    (hphase : (c0.state.fst : Nat) = base)
    (ks : List Nat) (hks : ∀ k ∈ ks, 2 ≤ k) (zbase : Nat)
    (hhead : (c0.head : Nat) = zbase)
    (hroom : zbase + (walkZone ks).length + 2 < zoneWalkRight.toPhased.toTM.tapeLength L)
    (hwin : windowSpells c0.tape zbase (walkZone ks))
    (hdead1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = zbase + (walkZone ks).length → c0.tape p = false)
    (hdead2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = zbase + (walkZone ks).length + 1 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneStepsR ks + 1)).state).fst : Nat) = nxt
    ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneStepsR ks + 1)).head : Nat)
        = zbase + (walkZone ks).length + 1
    ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneStepsR ks + 1)).tape = c0.tape := by
  set cn0 := trackStart zoneWalkRight c0 (by simp [zoneWalkRight]) (by omega) hlen with hcn0
  have hnwin : windowSpells cn0.tape zbase (walkZone ks) := by
    refine ⟨by omega, fun q hlo hhi => ?_⟩
    show c0.tape _ = _
    exact hwin.2 ⟨(q : Nat), lt_of_lt_of_le q.isLt hlen⟩ hlo hhi
  have hndead1 : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (p : Nat) = zbase + (walkZone ks).length → cn0.tape p = false := by
    intro p hp
    show c0.tape _ = false
    exact hdead1 ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp
  have hndead2 : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (p : Nat) = zbase + (walkZone ks).length + 1 → cn0.tape p = false := by
    intro p hp
    show c0.tape _ = false
    exact hdead2 ⟨(p : Nat), lt_of_lt_of_le p.isLt hlen⟩ hp
  obtain ⟨hw1, hw2, hw3, hw4⟩ := zoneWalkRight_runConfig_walkZone cn0 ks hks zbase
    (trackStart_phase _ _ _ _ _) (by rw [trackStart_head]; exact hhead) (by omega)
    hnwin hndead1 hndead2
  obtain ⟨htph, hthd, http, hthi⟩ := hUP.run_track hlen c0 cn0
    (by rw [hphase, trackStart_phase]; omega)
    (by rw [trackStart_head])
    (trackStart_tapeAgree _ _ _ _ _)
    (walkZoneStepsR ks)
    (fun s hs => by
      obtain ⟨hp4, hhb⟩ := hw4 s hs
      exact ⟨hredlow _ hp4, by omega⟩)
  rw [TM.runConfig_succ]
  set ce := TM.runConfig (M := U.toPhased.toTM) c0 (walkZoneStepsR ks) with hce
  have hij : (ce.state.fst : Nat) = base + ((⟨4, by simp [zoneWalkRight]⟩
      : Fin zoneWalkRight.numPhases)).val := by
    rw [hce, htph, hw1]
  have hehd : (ce.head : Nat) = zbase + (walkZone ks).length + 1 := by
    rw [hce, hthd, hw2]
  have hetp : ce.tape = c0.tape := by
    funext q
    by_cases hq : (q : Nat) < zoneWalkRight.toPhased.toTM.tapeLength L
    · have := http q ⟨(q : Nat), hq⟩ rfl
      rw [hce, this, hw3]
      show c0.tape _ = c0.tape q
      congr 1
    · exact hthi q (by omega)
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase ce rfl _ hij hred4
  · rw [hUP.stepConfig_redirect_head ce rfl _ hij hred4]
    exact hehd
  · rw [hUP.stepConfig_redirect_tape ce rfl _ hij hred4]
    exact hetp

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
