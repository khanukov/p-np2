import Pnp4.Frontier.ContractExpansion.TreeMCSPLoopUntilSink
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout

/-!
# `unaryTransferBody` — D2t-5b (Block A2): the generic unary-block transfer pass

The driver's data-dependent moves (record operands from the value stack, the fresh index from COUNT)
are all instances of one primitive: **move a unary block of unknown length `m` across a blank gap** —
from a *source* `1^m 0` to a growing *destination* block, one unit per pass (the proven
binary→unary discipline, with the blank gap in place of the binary counter).

One **pass** of the body, started at HOME (the destination block's leftmost cell):

* φ0 — walk right over the destination's `1`s; on the first `0` (its frontier) **write `1`** (the
  transferred unit) and continue right (φ1);
* φ1 — scan right over the gap's `0`s; the first `1` is the source's leftmost remaining unit (φ2);
* φ2 — **erase** it (write `0`), step right (φ3);
* φ3 — **peek**: a `1` means more units remain — return home (φ4); a `0` is the source's terminator —
  every unit (including this pass's) has been appended: jump to the **sink** (φ8);
* φ4/φ5/φ6 — return: scan left over the gap's `0`s, then left over the destination's `1`s, then one
  step right back onto HOME (φ7, the body's accept — the `loopUntilSink` back-edge re-enters φ0).

Soundness of the landmarks is exactly what A1's shifted stack codecs guarantee: the source field opens
with a `1`, the gap is all-`0`, and the growing destination block is its own left landmark.

This module ships the program and its single-step lemmas; the one-pass `runConfig` walk-through and the
`loopUntilSink` discharge (the transfer-correctness headline) build on these.

**Progress classification (AGENTS.md): Infrastructure** — a generic verifier machine component; builds
no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **One transfer pass** (9 phases).  φ0 dst-walk/append, φ1 gap scan →, φ2 erase, φ3 peek
(→ φ4 return | → φ8 sink), φ4 gap scan ←, φ5 dst-walk ←, φ6 re-home step →, φ7 accept (back-edge),
φ8 sink (source exhausted). -/
def unaryTransferBody : ConstStatePhasedProgram Unit where
  numPhases := 9
  startPhase := ⟨0, by decide⟩
  startState := ()
  acceptPhase := ⟨7, by decide⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      -- dst walk: loop right over 1s; on the frontier 0 write the unit and move on
      if b then (⟨0, by decide⟩, (), true, Move.right)
      else (⟨1, by decide⟩, (), true, Move.right)
    else if i.val = 1 then
      -- gap scan →: loop right over 0s; first 1 is the source's head
      if b then (⟨2, by decide⟩, (), b, Move.stay)
      else (⟨1, by decide⟩, (), b, Move.right)
    else if i.val = 2 then
      -- erase the source unit, step right to peek
      (⟨3, by decide⟩, (), false, Move.right)
    else if i.val = 3 then
      -- peek: 1 = more units (return home); 0 = terminator (sink)
      if b then (⟨4, by decide⟩, (), b, Move.left)
      else (⟨8, by decide⟩, (), b, Move.stay)
    else if i.val = 4 then
      -- gap scan ←: loop left over 0s; first 1 is the destination's right end
      if b then (⟨5, by decide⟩, (), b, Move.stay)
      else (⟨4, by decide⟩, (), b, Move.left)
    else if i.val = 5 then
      -- dst walk ←: loop left over 1s; the 0 just left of the block is the home delimiter
      if b then (⟨5, by decide⟩, (), b, Move.left)
      else (⟨6, by decide⟩, (), b, Move.stay)
    else if i.val = 6 then
      -- re-home: one step right onto the block's leftmost 1
      (⟨7, by decide⟩, (), b, Move.right)
    else if i.val = 7 then
      -- accept (pass done): idle; loopUntilSink's back-edge re-enters φ0
      (⟨7, by decide⟩, (), b, Move.stay)
    else
      -- φ8: sink — idle
      (⟨8, by decide⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem unaryTransferBody_numPhases : unaryTransferBody.numPhases = 9 := rfl

@[simp] theorem unaryTransferBody_startPhase : (unaryTransferBody.startPhase : Nat) = 0 := rfl

@[simp] theorem unaryTransferBody_acceptPhase : (unaryTransferBody.acceptPhase : Nat) = 7 := rfl

/-! ### Single-step transition lemmas (one per φ/bit arm) -/

theorem unaryTransferBody_t0_one :
    unaryTransferBody.transition ⟨0, by decide⟩ () true = (⟨0, by decide⟩, (), true, Move.right) := rfl

theorem unaryTransferBody_t0_zero :
    unaryTransferBody.transition ⟨0, by decide⟩ () false = (⟨1, by decide⟩, (), true, Move.right) := rfl

theorem unaryTransferBody_t1_one :
    unaryTransferBody.transition ⟨1, by decide⟩ () true = (⟨2, by decide⟩, (), true, Move.stay) := rfl

theorem unaryTransferBody_t1_zero :
    unaryTransferBody.transition ⟨1, by decide⟩ () false = (⟨1, by decide⟩, (), false, Move.right) := rfl

theorem unaryTransferBody_t2 (b : Bool) :
    unaryTransferBody.transition ⟨2, by decide⟩ () b = (⟨3, by decide⟩, (), false, Move.right) := rfl

theorem unaryTransferBody_t3_one :
    unaryTransferBody.transition ⟨3, by decide⟩ () true = (⟨4, by decide⟩, (), true, Move.left) := rfl

theorem unaryTransferBody_t3_zero :
    unaryTransferBody.transition ⟨3, by decide⟩ () false = (⟨8, by decide⟩, (), false, Move.stay) := rfl

theorem unaryTransferBody_t4_one :
    unaryTransferBody.transition ⟨4, by decide⟩ () true = (⟨5, by decide⟩, (), true, Move.stay) := rfl

theorem unaryTransferBody_t4_zero :
    unaryTransferBody.transition ⟨4, by decide⟩ () false = (⟨4, by decide⟩, (), false, Move.left) := rfl

theorem unaryTransferBody_t5_one :
    unaryTransferBody.transition ⟨5, by decide⟩ () true = (⟨5, by decide⟩, (), true, Move.left) := rfl

theorem unaryTransferBody_t5_zero :
    unaryTransferBody.transition ⟨5, by decide⟩ () false = (⟨6, by decide⟩, (), false, Move.stay) := rfl

theorem unaryTransferBody_t6 (b : Bool) :
    unaryTransferBody.transition ⟨6, by decide⟩ () b = (⟨7, by decide⟩, (), b, Move.right) := rfl

theorem unaryTransferBody_t7 (b : Bool) :
    unaryTransferBody.transition ⟨7, by decide⟩ () b = (⟨7, by decide⟩, (), b, Move.stay) := rfl

theorem unaryTransferBody_t8 (b : Bool) :
    unaryTransferBody.transition ⟨8, by decide⟩ () b = (⟨8, by decide⟩, (), b, Move.stay) := rfl

end ContractExpansion
end Frontier
end Pnp4
