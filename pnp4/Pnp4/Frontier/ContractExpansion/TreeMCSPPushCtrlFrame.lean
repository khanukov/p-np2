import Pnp4.Frontier.ContractExpansion.TreeMCSPWriteBits
import Pnp4.Frontier.ContractExpansion.TreeMCSPCtrlFrameStack

/-!
# `pushCtrlFrame` — D2t-5a machine: push an initial control frame onto the STACK

The control-stack `pushFrame` of D2t-5's driver (D2t-5b): when the preorder reader (`treeTagDispatch`)
hits an internal node `tag`, the driver pushes the **initial frame** `(tag, tag.arity)` onto the control
stack (`STACK_ctrl`) — `tag` and `arity` children still to process.

Because the tag is known from the dispatch branch, that frame's encoding `encodeCtrlFrame (tag, tag.arity)`
is a **fixed bit list**, so the push is a fixed-width write — `pushCtrlFrame tag := writeBits …`.  Its
correctness is therefore a direct corollary of `writeBits_runConfig`: from the stack-top pointer `p`, after
`(encodeCtrlFrame (tag, tag.arity)).length` steps the window `[p, p + …)` holds exactly the control frame's
bits and the pointer rests just past it (so the new frame sits at the head of `encodeCtrlStack`, since
`encodeCtrlStack (f :: rest)` prepends `encodeCtrlFrame f` by definition).

`pushCtrlFrame_frameLen_*` give the concrete per-tag frame widths (`not` ↦ 3, `and` ↦ 5, `or` ↦ 6 cells),
for the driver's room bounds.

**Progress classification (AGENTS.md): Infrastructure** — a stack-push machine proven at the configuration
level against the merged frame codec; builds no verifier and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Push the initial frame `(tag, tag.arity)` onto the control stack: write its fixed encoding
`encodeCtrlFrame (tag, tag.arity)` rightward from the stack-top pointer. -/
def pushCtrlFrame (tag : ITag) : ConstStatePhasedProgram Unit :=
  writeBits (encodeCtrlFrame (tag, tag.arity))

/-- **`pushCtrlFrame` run-through.**  From the stack-top pointer `p = c.head` (phase `0`) with room for the
frame, after `(encodeCtrlFrame (tag, tag.arity)).length` steps the machine halts at the accept phase, the
pointer rests at `p + len`, and the window `[p, p + len)` holds exactly `encodeCtrlFrame (tag, tag.arity)`
— the pushed control frame (tape elsewhere unchanged).  Direct corollary of `writeBits_runConfig`. -/
theorem pushCtrlFrame_runConfig {L : Nat} (tag : ITag)
    (c : Configuration (M := (pushCtrlFrame tag).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + (encodeCtrlFrame (tag, tag.arity)).length
        < (pushCtrlFrame tag).toPhased.toTM.tapeLength L) :
    ((TM.runConfig (M := (pushCtrlFrame tag).toPhased.toTM) c
          (encodeCtrlFrame (tag, tag.arity)).length).state.fst : Nat)
        = (encodeCtrlFrame (tag, tag.arity)).length
      ∧ ((TM.runConfig (M := (pushCtrlFrame tag).toPhased.toTM) c
          (encodeCtrlFrame (tag, tag.arity)).length).head : Nat)
        = (c.head : Nat) + (encodeCtrlFrame (tag, tag.arity)).length
      ∧ ∀ q : Fin ((pushCtrlFrame tag).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (pushCtrlFrame tag).toPhased.toTM) c
              (encodeCtrlFrame (tag, tag.arity)).length).tape q
            = if (c.head : Nat) ≤ (q : Nat)
                  ∧ (q : Nat) < (c.head : Nat) + (encodeCtrlFrame (tag, tag.arity)).length
              then (encodeCtrlFrame (tag, tag.arity)).getD ((q : Nat) - (c.head : Nat)) false
              else c.tape q :=
  writeBits_runConfig (encodeCtrlFrame (tag, tag.arity)) c hphase hroom

/-- The `not` control frame `(tnot, 1)` is 3 cells: `unaryField 0 ++ unaryField 1`. -/
@[simp] theorem pushCtrlFrame_frameLen_not :
    (encodeCtrlFrame (ITag.tnot, ITag.tnot.arity)).length = 3 := by
  simp [encodeCtrlFrame, ITag.arity, ITag.tagCode, unaryField]

/-- The `and` control frame `(tand, 2)` is 5 cells: `unaryField 1 ++ unaryField 2`. -/
@[simp] theorem pushCtrlFrame_frameLen_and :
    (encodeCtrlFrame (ITag.tand, ITag.tand.arity)).length = 5 := by
  simp [encodeCtrlFrame, ITag.arity, ITag.tagCode, unaryField]

/-- The `or` control frame `(tor, 2)` is 6 cells: `unaryField 2 ++ unaryField 2`. -/
@[simp] theorem pushCtrlFrame_frameLen_or :
    (encodeCtrlFrame (ITag.tor, ITag.tor.arity)).length = 6 := by
  simp [encodeCtrlFrame, ITag.arity, ITag.tagCode, unaryField]

end ContractExpansion
end Frontier
end Pnp4
