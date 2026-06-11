import Pnp4.Frontier.ContractExpansion.TreeMCSPSettleProbeFrame

/-!
# `RegionEmbedded` — D2t-5b (Block A5m-U1): generic phase-region embedding

`seq` composes exactly two programs; the driver needs **branching** (probe verdicts, tag dispatch),
so its machine is one program whose phase space hosts **many** component regions with redirected
exits.  `RegionEmbedded U P base next` captures the contract one region obeys — on
`[base, base + P.numPhases)` the host `U`'s transition is `P`'s (phases shifted by `base`), except
at `P`'s accept phase, which **redirects** to the absolute phase `next` (one handoff step: bit
written back, head stays) — exactly `seq`'s boundary discipline, region-generic.  Branching is then
free: different regions redirect to different successors, and a *branching* component (like the
probes, whose two verdicts are distinct phases) can sit in a region whose normal transitions carry
both outcome phases.

The six `stepConfig` transfer lemmas mirror the `seq` P1-simulation (`BoundedLoopProgram` §6a) for
an arbitrary embedded region: a host step at a normal region phase effects `P`'s transition (phase
shifted, same bit, same move), and a host step at the region's accept phase performs the redirect
(phase `next`, tape and head unchanged).  Per-segment run inductions are then re-run directly on the
host using these (the established ~30-line pattern), with **no** configuration transport.

**Progress classification (AGENTS.md): Infrastructure** — a generic composition contract plus
single-step transfer lemmas; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The region contract**: on `[base, base + P.numPhases)` the host `U` runs `P` (shifted), with
`P`'s accept phase redirected to the absolute phase `next` (bit written back, head stays). -/
structure RegionEmbedded (U P : ConstStatePhasedProgram Unit) (base next : Nat) : Prop where
  fit : base + P.numPhases ≤ U.numPhases
  next_lt : next < U.numPhases
  normal_phase : ∀ (j : Fin P.numPhases) (b : Bool), j.val ≠ (P.acceptPhase : Nat) →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).fst.val
      = base + (P.transition j () b).fst.val
  normal_bit : ∀ (j : Fin P.numPhases) (b : Bool), j.val ≠ (P.acceptPhase : Nat) →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).snd.snd.fst
      = (P.transition j () b).snd.snd.fst
  normal_move : ∀ (j : Fin P.numPhases) (b : Bool), j.val ≠ (P.acceptPhase : Nat) →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).snd.snd.snd
      = (P.transition j () b).snd.snd.snd
  accept_phase : ∀ b : Bool,
    (U.transition ⟨base + (P.acceptPhase : Nat),
        by have := P.acceptPhase.isLt; omega⟩ () b).fst.val = next
  accept_bit : ∀ b : Bool,
    (U.transition ⟨base + (P.acceptPhase : Nat),
        by have := P.acceptPhase.isLt; omega⟩ () b).snd.snd.fst = b
  accept_move : ∀ b : Bool,
    (U.transition ⟨base + (P.acceptPhase : Nat),
        by have := P.acceptPhase.isLt; omega⟩ () b).snd.snd.snd = Move.stay

namespace RegionEmbedded

variable {U P : ConstStatePhasedProgram Unit} {base next : Nat}

/-- A host step at a normal region phase: the phase tracks `P`'s transition (shifted). -/
theorem stepConfig_normal_phase (hUP : RegionEmbedded U P base next) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) (hj : j.val ≠ (P.acceptPhase : Nat)) :
    ((TM.stepConfig (M := U.toPhased.toTM) c).state).fst.val
      = base + (P.transition j () (c.tape c.head)).fst.val := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  exact hUP.normal_phase j (c.tape c.head) hj

/-- A host step at a normal region phase: the head moves as `P`'s transition directs. -/
theorem stepConfig_normal_head (hUP : RegionEmbedded U P base next) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) (hj : j.val ≠ (P.acceptPhase : Nat)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).head
      = c.moveHead (P.transition j () (c.tape c.head)).snd.snd.snd := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  rw [hUP.normal_move j (c.tape c.head) hj]

/-- A host step at a normal region phase: the tape gets `P`'s written bit at the head. -/
theorem stepConfig_normal_tape (hUP : RegionEmbedded U P base next) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) (hj : j.val ≠ (P.acceptPhase : Nat)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).tape
      = c.write c.head (P.transition j () (c.tape c.head)).snd.snd.fst := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  rw [hUP.normal_bit j (c.tape c.head) hj]

/-- The redirect step (at the region's accept phase): the phase jumps to `next`. -/
theorem stepConfig_accept_phase (hUP : RegionEmbedded U P base next) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (hij : i.val = base + (P.acceptPhase : Nat)) :
    ((TM.stepConfig (M := U.toPhased.toTM) c).state).fst.val = next := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + (P.acceptPhase : Nat), by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  exact hUP.accept_phase (c.tape c.head)

/-- The redirect step: the head stays. -/
theorem stepConfig_accept_head (hUP : RegionEmbedded U P base next) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (hij : i.val = base + (P.acceptPhase : Nat)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + (P.acceptPhase : Nat), by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  rw [hUP.accept_move (c.tape c.head)]
  simp [Configuration.moveHead]

/-- The redirect step: the tape is unchanged (the scanned bit is written back). -/
theorem stepConfig_accept_tape (hUP : RegionEmbedded U P base next) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (hij : i.val = base + (P.acceptPhase : Nat)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + (P.acceptPhase : Nat), by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi, hUP.accept_bit (c.tape c.head)]
  funext q
  by_cases hq : q = c.head
  · subst hq; simp [Configuration.write]
  · simp [Configuration.write, hq]

end RegionEmbedded

end ContractExpansion
end Frontier
end Pnp4
