import Pnp4.Frontier.ContractExpansion.TreeMCSPCtrlTopWalk

/-!
# `remWalk` — D2t-5b (Block A5m-4b): the rem-block read, from the separator to the frame base

After `ctrlTopWalk` lands on the tag block's `0` separator, the settle decision needs the top
frame's remaining count: walking left and **counting the ones** of the rem block (`rem + 1` ones)
distinguishes the reachable cases — `2` ones = `rem 1` (**pop**), `3` ones = `rem 2` (**dec**) —
with the head landing on the frame's **base `0`**, exactly where the dec arm's frame rewrite
(`run_writeBits_hop`) begins.

* `φ0` — step left off the separator (onto the rem block's last `1`); `φ1`–`φ3` — count, branching;
* verdicts `φ4` (`rem = 1`, pop), `φ5` (`rem = 2`, dec) idle; `φ6` rejects.

The codec facts `encodeCtrlStackR_remBlock_true` / `encodeCtrlStackR_frameBase_false` pin the rem
block's cells and the frame base.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component with its
codec facts; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### Codec facts: the rem block and the frame base -/

/-- The top frame's rem block: the cells left of the tag separator are `1` (`rem + 1` of them). -/
theorem encodeCtrlStackR_remBlock_true (tag : ITag) (rem : Nat) (rest : List (ITag × Nat))
    (i : Nat) (hi : i < rem + 1) :
    (encodeCtrlStackR ((tag, rem) :: rest)).getD
      ((encodeCtrlStackR ((tag, rem) :: rest)).length - 1 - (tag.tagCode + 2) - 1 - i) false
      = true := by
  have hsplit : encodeCtrlStackR ((tag, rem) :: rest)
      = (encodeCtrlStackR rest ++ [false])
        ++ (List.replicate (rem + 1) true
          ++ ([false] ++ List.replicate (tag.tagCode + 2) true)) := by
    rw [encodeCtrlStackR_cons]
    show encodeCtrlStackR rest
        ++ (false :: (List.replicate (rem + 1) true
          ++ (false :: List.replicate (tag.tagCode + 2) true)))
      = _
    simp [List.append_assoc]
  rw [hsplit]
  have hlen : ((encodeCtrlStackR rest ++ [false])
      ++ (List.replicate (rem + 1) true
        ++ ([false] ++ List.replicate (tag.tagCode + 2) true))).length
      = (encodeCtrlStackR rest ++ [false]).length + (rem + 1) + (tag.tagCode + 3) := by
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil]
    omega
  rw [hlen, List.getD_append_right _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by
      rw [List.length_replicate]
      omega)]
  exact getD_replicate_true _ _ (by omega)

/-- The frame's **base `0`**, immediately left of the rem block. -/
theorem encodeCtrlStackR_frameBase_false (tag : ITag) (rem : Nat) (rest : List (ITag × Nat)) :
    (encodeCtrlStackR ((tag, rem) :: rest)).getD
      ((encodeCtrlStackR ((tag, rem) :: rest)).length - 1 - (tag.tagCode + 2) - 1 - (rem + 1))
      false = false := by
  have hsplit : encodeCtrlStackR ((tag, rem) :: rest)
      = encodeCtrlStackR rest
        ++ ([false] ++ (List.replicate (rem + 1) true
          ++ ([false] ++ List.replicate (tag.tagCode + 2) true))) := by
    rw [encodeCtrlStackR_cons]
    show encodeCtrlStackR rest
        ++ (false :: (List.replicate (rem + 1) true
          ++ (false :: List.replicate (tag.tagCode + 2) true)))
      = _
    simp [List.append_assoc]
  rw [hsplit]
  have hlen : (encodeCtrlStackR rest
      ++ ([false] ++ (List.replicate (rem + 1) true
        ++ ([false] ++ List.replicate (tag.tagCode + 2) true)))).length
      = (encodeCtrlStackR rest).length + 1 + (rem + 1) + (tag.tagCode + 3) := by
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil]
    omega
  rw [hlen, List.getD_append_right _ _ _ _ (by omega)]
  have hidx : (encodeCtrlStackR rest).length + 1 + (rem + 1) + (tag.tagCode + 3) - 1
      - (tag.tagCode + 2) - 1 - (rem + 1) - (encodeCtrlStackR rest).length = 0 := by
    omega
  rw [hidx]
  rfl

/-! ### The walking component -/

/-- **The rem-block walk** (7 phases): step left off the separator, count the ones — verdicts:
`2` ones = `rem 1` (**pop**, `φ4`); `3` ones = `rem 2` (**dec**, `φ5`); a fourth one rejects
(`φ6`).  The verdicts land on the frame's base `0`. -/
def remWalk : ConstStatePhasedProgram Unit where
  numPhases := 7
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨4, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.left)
    else if i.val = 1 then
      if b then (⟨2, by omega⟩, (), b, Move.left) else (⟨6, by omega⟩, (), b, Move.stay)
    else if i.val = 2 then
      if b then (⟨3, by omega⟩, (), b, Move.left) else (⟨4, by omega⟩, (), b, Move.stay)
    else if i.val = 3 then
      if b then (⟨6, by omega⟩, (), b, Move.stay) else (⟨5, by omega⟩, (), b, Move.stay)
    else (⟨i.val, i.isLt⟩, (), b, Move.stay)
  timeBound := fun _ => 4

end ContractExpansion
end Frontier
end Pnp4
