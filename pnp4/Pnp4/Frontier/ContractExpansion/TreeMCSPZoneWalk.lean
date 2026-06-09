import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor
import Pnp4.Frontier.ContractExpansion.TreeMCSPLoopUntilSink

/-!
# `zoneWalkLeft` — D2t-5b (Block A4w): traversing a corridor stack zone right-to-left

The corridor layout (A3) stores both stacks as `[sentinel 1] [0 1^{k₁}] [0 1^{k₂}] …` with every
field block carrying **≥ 2** ones and the base sentinel exactly **1** — so a zone can be *walked*
right-to-left without any markers: enter a block at its rightmost `1`, peek one cell left — another
`1` means a field block (walk its remaining ones and hop its delimiter to the next block), a `0`
means the block was the single-`1` **base sentinel**: stop.  `zoneWalkLeft` is that walker; the
driver's cross-zone routes (cursor → control top → value top → WORK frontier and back) chain it with
the 0-corridor scans.

Phases: φ0 enter block (step left off its rightmost `1`); φ1 peek (`1` → field, φ2; `0` → it was the
sentinel, φ5 done); φ2 walk the field's remaining ones (self-loop left, stop on the delimiter `0`);
φ3 step left off the delimiter; φ4 confirm the next block's `1` (re-enter φ0 shape via a stay);
φ5 done — the head rests on the `0` immediately **left of the sentinel**, exactly where the caller's
next leftward 0-corridor scan begins.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component; builds no
verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The leftward zone walker** (6 phases).  φ0 step into the block; φ1 peek (field vs sentinel);
φ2 walk the field's ones; φ3 step off the delimiter; φ4 re-enter; φ5 done (sentinel found, head on
the `0` just left of it). -/
def zoneWalkLeft : ConstStatePhasedProgram Unit where
  numPhases := 6
  startPhase := ⟨0, by decide⟩
  startState := ()
  acceptPhase := ⟨5, by decide⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      -- on the block's rightmost 1: step left to peek
      (⟨1, by decide⟩, (), b, Move.left)
    else if i.val = 1 then
      -- peek: 1 = a ≥2 field block (walk it); 0 = the block was the single-1 sentinel (done)
      if b then (⟨2, by decide⟩, (), b, Move.stay)
      else (⟨5, by decide⟩, (), b, Move.stay)
    else if i.val = 2 then
      -- walk the field's remaining ones leftward; the 0 is the field's left delimiter
      if b then (⟨2, by decide⟩, (), b, Move.left)
      else (⟨3, by decide⟩, (), b, Move.stay)
    else if i.val = 3 then
      -- step left off the delimiter onto the next block's rightmost 1
      (⟨4, by decide⟩, (), b, Move.left)
    else if i.val = 4 then
      -- confirm and re-enter the block walk (the adjacency invariant guarantees a 1)
      if b then (⟨1, by decide⟩, (), b, Move.left)
      else (⟨5, by decide⟩, (), b, Move.stay)
    else
      -- φ5: done — idle
      (⟨5, by decide⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem zoneWalkLeft_numPhases : zoneWalkLeft.numPhases = 6 := rfl

@[simp] theorem zoneWalkLeft_startPhase : (zoneWalkLeft.startPhase : Nat) = 0 := rfl

@[simp] theorem zoneWalkLeft_acceptPhase : (zoneWalkLeft.acceptPhase : Nat) = 5 := rfl

/-! ### Transition lemmas -/

theorem zoneWalkLeft_t0 (b : Bool) :
    zoneWalkLeft.transition ⟨0, by decide⟩ () b = (⟨1, by decide⟩, (), b, Move.left) := rfl

theorem zoneWalkLeft_t1_one :
    zoneWalkLeft.transition ⟨1, by decide⟩ () true = (⟨2, by decide⟩, (), true, Move.stay) := rfl

theorem zoneWalkLeft_t1_zero :
    zoneWalkLeft.transition ⟨1, by decide⟩ () false = (⟨5, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t2_one :
    zoneWalkLeft.transition ⟨2, by decide⟩ () true = (⟨2, by decide⟩, (), true, Move.left) := rfl

theorem zoneWalkLeft_t2_zero :
    zoneWalkLeft.transition ⟨2, by decide⟩ () false = (⟨3, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t3 (b : Bool) :
    zoneWalkLeft.transition ⟨3, by decide⟩ () b = (⟨4, by decide⟩, (), b, Move.left) := rfl

theorem zoneWalkLeft_t4_one :
    zoneWalkLeft.transition ⟨4, by decide⟩ () true = (⟨1, by decide⟩, (), true, Move.left) := rfl

theorem zoneWalkLeft_t4_zero :
    zoneWalkLeft.transition ⟨4, by decide⟩ () false = (⟨5, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t5 (b : Bool) :
    zoneWalkLeft.transition ⟨5, by decide⟩ () b = (⟨5, by decide⟩, (), b, Move.stay) := rfl

end ContractExpansion
end Frontier
end Pnp4
