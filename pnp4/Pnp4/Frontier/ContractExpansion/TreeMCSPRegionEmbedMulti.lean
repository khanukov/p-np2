import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionEmbed

/-!
# `RegionEmbeddedMulti` — D2t-5b (Block A5m-U2): multi-exit region embedding

A region whose component **branches** (the tag trie's five verdicts, the probes' two) needs more
than the single accept-redirect of `RegionEmbedded`: each *outcome* phase must route to a different
successor region.  `RegionEmbeddedMulti U P base redirect` generalises the contract with a redirect
**map** over `P`'s phases: mapped phases hand off to their absolute targets (bit written back, head
stays); unmapped phases run `P`'s transition shifted.  `RegionEmbedded` is the special case mapping
exactly the accept phase.

The six `stepConfig` transfer lemmas mirror Block A5m-U1's.  With this, every merged component —
linear or branching — embeds into the one driver machine, and the arms' run segments are re-run on
the host via these step lemmas.

**Progress classification (AGENTS.md): Infrastructure** — a generic composition contract plus
single-step transfer lemmas; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The multi-exit region contract**: on `[base, base + P.numPhases)` the host `U` runs `P`
(shifted), except at the phases in the redirect map, which hand off to their absolute targets (bit
written back, head stays). -/
structure RegionEmbeddedMulti (U P : ConstStatePhasedProgram Unit) (base : Nat)
    (redirect : Nat → Option Nat) : Prop where
  fit : base + P.numPhases ≤ U.numPhases
  redirect_lt : ∀ {j nxt : Nat}, redirect j = some nxt → nxt < U.numPhases
  normal_phase : ∀ (j : Fin P.numPhases) (b : Bool), redirect j.val = none →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).fst.val
      = base + (P.transition j () b).fst.val
  normal_bit : ∀ (j : Fin P.numPhases) (b : Bool), redirect j.val = none →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).snd.snd.fst
      = (P.transition j () b).snd.snd.fst
  normal_move : ∀ (j : Fin P.numPhases) (b : Bool), redirect j.val = none →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).snd.snd.snd
      = (P.transition j () b).snd.snd.snd
  redirect_phase : ∀ (j : Fin P.numPhases) (b : Bool) {nxt : Nat}, redirect j.val = some nxt →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).fst.val = nxt
  redirect_bit : ∀ (j : Fin P.numPhases) (b : Bool) {nxt : Nat}, redirect j.val = some nxt →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).snd.snd.fst = b
  redirect_move : ∀ (j : Fin P.numPhases) (b : Bool) {nxt : Nat}, redirect j.val = some nxt →
    (U.transition ⟨base + j.val, by have := j.isLt; omega⟩ () b).snd.snd.snd = Move.stay

namespace RegionEmbeddedMulti

variable {U P : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- A host step at an unmapped region phase: the phase tracks `P`'s transition (shifted). -/
theorem stepConfig_normal_phase (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) (hj : redirect j.val = none) :
    ((TM.stepConfig (M := U.toPhased.toTM) c).state).fst.val
      = base + (P.transition j () (c.tape c.head)).fst.val := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  exact hUP.normal_phase j (c.tape c.head) hj

/-- A host step at an unmapped region phase: the head moves as `P`'s transition directs. -/
theorem stepConfig_normal_head (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) (hj : redirect j.val = none) :
    (TM.stepConfig (M := U.toPhased.toTM) c).head
      = c.moveHead (P.transition j () (c.tape c.head)).snd.snd.snd := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  rw [hUP.normal_move j (c.tape c.head) hj]

/-- A host step at an unmapped region phase: the tape gets `P`'s written bit at the head. -/
theorem stepConfig_normal_tape (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) (hj : redirect j.val = none) :
    (TM.stepConfig (M := U.toPhased.toTM) c).tape
      = c.write c.head (P.transition j () (c.tape c.head)).snd.snd.fst := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  rw [hUP.normal_bit j (c.tape c.head) hj]

/-- A host step at a mapped region phase: the phase jumps to the target. -/
theorem stepConfig_redirect_phase (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) {nxt : Nat}
    (hj : redirect j.val = some nxt) :
    ((TM.stepConfig (M := U.toPhased.toTM) c).state).fst.val = nxt := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  exact hUP.redirect_phase j (c.tape c.head) hj

/-- A host step at a mapped region phase: the head stays. -/
theorem stepConfig_redirect_head (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) {nxt : Nat}
    (hj : redirect j.val = some nxt) :
    (TM.stepConfig (M := U.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi]
  rw [hUP.redirect_move j (c.tape c.head) hj]
  simp [Configuration.moveHead]

/-- A host step at a mapped region phase: the tape is unchanged. -/
theorem stepConfig_redirect_tape (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (c : Configuration (M := U.toPhased.toTM) L)
    {i : Fin U.numPhases} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    (j : Fin P.numPhases) (hij : i.val = base + j.val) {nxt : Nat}
    (hj : redirect j.val = some nxt) :
    (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased]
  have hi : i = ⟨base + j.val, by have := i.isLt; omega⟩ := Fin.ext hij
  rw [hi, hUP.redirect_bit j (c.tape c.head) hj]
  funext q
  by_cases hq : q = c.head
  · subst hq; simp [Configuration.write]
  · simp [Configuration.write, hq]

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
