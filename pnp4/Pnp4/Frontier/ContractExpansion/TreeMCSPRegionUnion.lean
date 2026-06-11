import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionRunTransfer

/-!
# `unionProgram` — D2t-5b (Block A5m-U5): the region-union machine builder

The driver machine is a phase-space union of the merged components.  This module builds such a
machine from a phase **assignment**: each absolute phase is owned by a region — recorded as the
component, its base, the phase's **local index within the component** (carried explicitly, so the
builder's body involves no subtraction), and the region's redirect map — or idles.  The single
generic theorem `unionProgram_embedded` turns a consistent assignment into the region contract
`RegionEmbeddedMulti`, so at assembly **every** region's contract is one instantiation and the
U1–U4 transfer machinery applies wholesale.

**Progress classification (AGENTS.md): Infrastructure** — a machine builder plus its contract
theorem; builds no *specific* machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- What a phase of the union machine does: run a component region's local phase, or idle. -/
inductive RegionAction where
  /-- The phase is local phase `jloc` of the region of `prog` based at `base`, with redirect map
  `redirect`.  (A consistent assignment sends absolute phase `base + jloc` here.) -/
  | run (prog : ConstStatePhasedProgram Unit) (base jloc : Nat) (redirect : Nat → Option Nat)
  /-- The phase idles (self-loop, bit written back, head stays). -/
  | idle

/-- **The region-union machine**: phase `i`'s behaviour is read off the assignment.  A redirected
local phase hands off to the absolute target (bit written back, head stays); an unmapped one runs
the component's transition, shifted by the region base.  Out-of-range cases idle (the contract
theorem's hypotheses exclude them on consistently assigned regions). -/
def unionProgram (N : Nat) (hN : 0 < N) (start accept : Fin N)
    (assign : Nat → RegionAction) : ConstStatePhasedProgram Unit where
  numPhases := N
  startPhase := start
  startState := ()
  acceptPhase := accept
  acceptState := ()
  transition := fun i _ b =>
    match assign i.val with
    | .run P base jloc redirect =>
        match redirect jloc with
        | some nxt =>
            if hn : nxt < N then (⟨nxt, hn⟩, (), b, Move.stay)
            else (i, (), b, Move.stay)
        | none =>
            if hloc : jloc < P.numPhases then
              let r := P.transition ⟨jloc, hloc⟩ () b
              if hsh : base + r.fst.val < N then
                (⟨base + r.fst.val, hsh⟩, (), r.snd.snd.fst, r.snd.snd.snd)
              else (i, (), b, Move.stay)
            else (i, (), b, Move.stay)
    | .idle => (i, (), b, Move.stay)
  timeBound := fun n => n + 1

@[simp] theorem unionProgram_numPhases (N : Nat) (hN : 0 < N) (start accept : Fin N)
    (assign : Nat → RegionAction) :
    (unionProgram N hN start accept assign).numPhases = N := rfl

/-- **The contract from a consistent assignment**: if every local phase `k` of the region maps to
`assign (base + k) = .run P base k redirect`, the region fits, and redirect targets are in range,
then the union machine hosts the region (`RegionEmbeddedMulti`). -/
theorem unionProgram_embedded (N : Nat) (hN : 0 < N) (start accept : Fin N)
    (assign : Nat → RegionAction)
    (P : ConstStatePhasedProgram Unit) (base : Nat) (redirect : Nat → Option Nat)
    (hassign : ∀ k, k < P.numPhases → assign (base + k) = RegionAction.run P base k redirect)
    (hfit : base + P.numPhases ≤ N)
    (hred_lt : ∀ {j nxt : Nat}, redirect j = some nxt → nxt < N) :
    RegionEmbeddedMulti (unionProgram N hN start accept assign) P base redirect := by
  refine ⟨hfit, fun {j nxt} h => hred_lt h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- normal_phase
  · intro j b hj
    show ((unionProgram N hN start accept assign).transition
      ⟨base + j.val, by have := j.isLt; simp only [unionProgram_numPhases]; omega⟩ () b).fst.val
      = base + (P.transition j () b).fst.val
    simp only [unionProgram, hassign j.val j.isLt, hj, dif_pos j.isLt]
    rw [dif_pos (by have := (P.transition ⟨j.val, j.isLt⟩ () b).fst.isLt; omega
      : base + (P.transition ⟨j.val, j.isLt⟩ () b).fst.val < N)]
  -- normal_bit
  · intro j b hj
    show ((unionProgram N hN start accept assign).transition
      ⟨base + j.val, by have := j.isLt; simp only [unionProgram_numPhases]; omega⟩ () b).snd.snd.fst
      = (P.transition j () b).snd.snd.fst
    simp only [unionProgram, hassign j.val j.isLt, hj, dif_pos j.isLt]
    rw [dif_pos (by have := (P.transition ⟨j.val, j.isLt⟩ () b).fst.isLt; omega
      : base + (P.transition ⟨j.val, j.isLt⟩ () b).fst.val < N)]
  -- normal_move
  · intro j b hj
    show ((unionProgram N hN start accept assign).transition
      ⟨base + j.val, by have := j.isLt; simp only [unionProgram_numPhases]; omega⟩ () b).snd.snd.snd
      = (P.transition j () b).snd.snd.snd
    simp only [unionProgram, hassign j.val j.isLt, hj, dif_pos j.isLt]
    rw [dif_pos (by have := (P.transition ⟨j.val, j.isLt⟩ () b).fst.isLt; omega
      : base + (P.transition ⟨j.val, j.isLt⟩ () b).fst.val < N)]
  -- redirect_phase
  · intro j b nxt hj
    show ((unionProgram N hN start accept assign).transition
      ⟨base + j.val, by have := j.isLt; simp only [unionProgram_numPhases]; omega⟩ () b).fst.val = nxt
    simp only [unionProgram, hassign j.val j.isLt, hj]
    rw [dif_pos (hred_lt hj)]
  -- redirect_bit
  · intro j b nxt hj
    show ((unionProgram N hN start accept assign).transition
      ⟨base + j.val, by have := j.isLt; simp only [unionProgram_numPhases]; omega⟩ () b).snd.snd.fst = b
    simp only [unionProgram, hassign j.val j.isLt, hj]
    rw [dif_pos (hred_lt hj)]
  -- redirect_move
  · intro j b nxt hj
    show ((unionProgram N hN start accept assign).transition
      ⟨base + j.val, by have := j.isLt; simp only [unionProgram_numPhases]; omega⟩ () b).snd.snd.snd = Move.stay
    simp only [unionProgram, hassign j.val j.isLt, hj]
    rw [dif_pos (hred_lt hj)]

end ContractExpansion
end Frontier
end Pnp4
