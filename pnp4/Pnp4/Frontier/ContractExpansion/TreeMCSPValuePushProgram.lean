import Pnp4.Frontier.ContractExpansion.TreeMCSPUnaryTransferRun

/-!
# `valuePushProgram` — D2t-5b (Block A5m-V / §12 M1): the non-destructive value-push machine

The settle/leaf keystone transformers write the value entry `encodeNatEntryR k = 0 ++ 1^(k+2)` at
the value-zone top **onto the original tape** — so the machine realizing them must read the gate
count `k` from a unary source block and mint `k + 2` fresh ones **while leaving the source intact**
(`TM_VERIFIER_STRATEGY.md` §12.3 M1; conservation forces a fan-out: `2k` ones must come out of `k`).

This module ships the machine; the run lemmas and the M1 headline
(`tape′ = writeBlockTape tape opBase (encodeNatEntryR k)`) live in `TreeMCSPValuePushRun.lean`.

## Layout (the `ValuePushLayout` of the run file)

```
opBase                          aPos                                    (aPos+2k+2)
v                               v                                       v
0 | 0 0 | 0 … 0                | 1 | 1 … 1 | 0 | 0 … 0                | 0
HOME seeds  gap₁                 ANCHOR  src k   term  scratch zone (k)   beyond
```

* `opBase` — HOME; the cell is the entry's `0` delimiter and is never rewritten;
* `[opBase+1, opBase+3)` — the entry's two framing ones (`+2`), written by the prologue;
* the entry then grows rightward to `[opBase+1, opBase+3+k)` — one deposit per drain pass;
* `aPos` — a **permanent anchor `1`** immediately left of the source (instantiated by the caller;
  in the corridor this is a stack-discipline base sentinel).  Every leftward scan between the
  source area and the entry hops it, and the restore stage uses **anchor + rebuilt block** as the
  contiguous destination landmark;
* `[aPos+1, aPos+1+k)` — the source units (the count `k` being pushed), `0`-terminated at
  `aPos+1+k`;
* `[aPos+2+k, aPos+2+2k)` — the scratch zone (all `0` initially): the fan-out's second copy grows
  here, directly after the terminator (the terminator is the landmark — no scratch anchor needed).

## The five stages

1. **Prologue** (φ0–φ4): write the two framing ones, scan to the anchor, probe the source:
   empty (`k = 0`) jumps straight to the park chain.
2. **Drain loop** (φ5–φ15), pass invariant "standing on the leftmost remaining unit":
   erase it (φ5), probe right (φ6) — the block is consumed left-to-right, so the probe cell is the
   next unit (`1`, mid round) or the honest terminator (`0`, final round; no anchor on this side to
   lie).  A **mid round** (φ7–φ15) deposits one entry one (left, hopping the anchor) and one scratch
   one (right, walking source-rest → terminator → scratch to its frontier), then walks back to the
   new leftmost unit — the erased prefix is nonempty from the first round on, so the return walk
   exits on an erased `0`, never onto the anchor.
3. **Final round** (φ16–φ21): after the last erase the head sits on the terminator; deposit the
   `k`-th scratch one **first** (the scratch walk starts at the terminator, sound even when the
   scratch is still empty at `k = 1`), then the `k`-th entry one, then park the head on the anchor.
4. **Restore** (φ22–φ29): a verbatim clone of the nine `unaryTransferBody` phases with
   `dst := anchor + rebuilt source` (`d = 1` pre-existing ones — the anchor!), `src := scratch`,
   and the constant sliding gap `γ = k + 1` — exactly the proven `TransferLayout` geometry; the
   sink edge exits to the park chain instead of idling.
5. **Park** (φ30–φ34): walk home left (zeros → source+anchor block → gap₁ → entry block → the `0`
   at `opBase` = HOME) and idle in the accept phase φ34.  The `k = 0` probe exit joins this chain
   at φ30 (the "block" it walks is then the bare anchor).

Validated by the run file's headline (the broken-`remWalk` lesson: no unvalidated bodies) — this
module only fixes the transition table and its single-step characterizations.

**Progress classification (AGENTS.md): Infrastructure** — a generic verifier machine component;
builds no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The value-push machine** (35 phases).  Stages: prologue φ0–φ4, drain loop φ5–φ15 (mid-round
deposits φ7–φ15), final round φ16–φ21, restore clone φ22–φ29, park φ30–φ33, accept φ34.  See the
module docstring for the leg-by-leg geometry. -/
def valuePushProgram : ConstStatePhasedProgram Unit where
  numPhases := 35
  startPhase := ⟨0, by decide⟩
  startState := ()
  acceptPhase := ⟨34, by decide⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      -- HOME (the entry delimiter, value 0): step right onto the first seed cell
      (⟨1, by decide⟩, (), b, Move.right)
    else if i.val = 1 then
      -- seed the first framing one
      (⟨2, by decide⟩, (), true, Move.right)
    else if i.val = 2 then
      -- seed the second framing one
      (⟨3, by decide⟩, (), true, Move.right)
    else if i.val = 3 then
      -- probe scan →: gap₁ zeros; the first 1 is the anchor — step onto the source head
      if b then (⟨4, by decide⟩, (), b, Move.right)
      else (⟨3, by decide⟩, (), b, Move.right)
    else if i.val = 4 then
      -- probe: 1 = source nonempty (drain); 0 = k = 0 (the terminator) — park directly
      if b then (⟨5, by decide⟩, (), b, Move.stay)
      else (⟨30, by decide⟩, (), b, Move.stay)
    else if i.val = 5 then
      -- drain loop point (on the leftmost remaining unit): erase it, step right to probe
      (⟨6, by decide⟩, (), false, Move.right)
    else if i.val = 6 then
      -- drain probe: 1 = units remain (mid round, step back onto the erased cell);
      --              0 = that was the last unit (final round; we are on the terminator)
      if b then (⟨7, by decide⟩, (), b, Move.left)
      else (⟨16, by decide⟩, (), b, Move.right)
    else if i.val = 7 then
      -- mid: scan ← the erased prefix; the first 1 is the anchor — hop over it
      if b then (⟨8, by decide⟩, (), b, Move.left)
      else (⟨7, by decide⟩, (), b, Move.left)
    else if i.val = 8 then
      -- mid: scan ← gap₁; the first 1 is the entry's rightmost one — turn onto the frontier
      if b then (⟨9, by decide⟩, (), b, Move.right)
      else (⟨8, by decide⟩, (), b, Move.left)
    else if i.val = 9 then
      -- mid: append the entry one (the frontier cell is 0), head on rightward
      (⟨10, by decide⟩, (), true, Move.right)
    else if i.val = 10 then
      -- mid: scan → the rest of gap₁; the first 1 is the anchor — step over it
      if b then (⟨11, by decide⟩, (), b, Move.right)
      else (⟨10, by decide⟩, (), b, Move.right)
    else if i.val = 11 then
      -- mid: scan → the erased prefix; the first 1 is the new leftmost unit — step into the block
      if b then (⟨12, by decide⟩, (), b, Move.right)
      else (⟨11, by decide⟩, (), b, Move.right)
    else if i.val = 12 then
      -- mid: walk → the remaining units; the first 0 is the terminator — step onto the scratch
      if b then (⟨12, by decide⟩, (), b, Move.right)
      else (⟨13, by decide⟩, (), b, Move.right)
    else if i.val = 13 then
      -- mid: walk → the scratch ones; at its frontier 0 write the scratch deposit, turn left
      if b then (⟨13, by decide⟩, (), b, Move.right)
      else (⟨14, by decide⟩, (), true, Move.left)
    else if i.val = 14 then
      -- mid return: walk ← the scratch ones; the first 0 is the terminator — step left
      if b then (⟨14, by decide⟩, (), b, Move.left)
      else (⟨15, by decide⟩, (), b, Move.left)
    else if i.val = 15 then
      -- mid return: walk ← the remaining units; the first 0 is the erased prefix's right end
      -- (nonempty from round one — never the anchor): turn right onto the leftmost unit (loop)
      if b then (⟨15, by decide⟩, (), b, Move.left)
      else (⟨5, by decide⟩, (), b, Move.right)
    else if i.val = 16 then
      -- final: walk → the scratch ones (possibly none, k = 1); at the frontier 0 write the
      -- k-th scratch one, turn left
      if b then (⟨16, by decide⟩, (), b, Move.right)
      else (⟨17, by decide⟩, (), true, Move.left)
    else if i.val = 17 then
      -- final: walk ← the scratch block; the first 0 is the terminator — keep left
      if b then (⟨17, by decide⟩, (), b, Move.left)
      else (⟨18, by decide⟩, (), b, Move.left)
    else if i.val = 18 then
      -- final: scan ← the zeroed source zone; the first 1 is the anchor — hop over it
      if b then (⟨19, by decide⟩, (), b, Move.left)
      else (⟨18, by decide⟩, (), b, Move.left)
    else if i.val = 19 then
      -- final: scan ← gap₁; the first 1 is the entry's rightmost one — turn onto the frontier
      if b then (⟨20, by decide⟩, (), b, Move.right)
      else (⟨19, by decide⟩, (), b, Move.left)
    else if i.val = 20 then
      -- final: append the k-th entry one (the entry is complete: 2 + k ones)
      (⟨21, by decide⟩, (), true, Move.right)
    else if i.val = 21 then
      -- final: scan → the rest of gap₁; the first 1 is the anchor = the restore HOME
      if b then (⟨22, by decide⟩, (), b, Move.stay)
      else (⟨21, by decide⟩, (), b, Move.right)
    else if i.val = 22 then
      -- restore (clone of unaryTransferBody φ0): walk → dst ones (anchor + rebuilt);
      -- on the frontier 0 write the restored unit and move on
      if b then (⟨22, by decide⟩, (), true, Move.right)
      else (⟨23, by decide⟩, (), true, Move.right)
    else if i.val = 23 then
      -- restore (clone φ1): scan → the sliding gap's 0s; the first 1 is the scratch's head
      if b then (⟨24, by decide⟩, (), b, Move.stay)
      else (⟨23, by decide⟩, (), b, Move.right)
    else if i.val = 24 then
      -- restore (clone φ2): erase the scratch unit, step right to peek
      (⟨25, by decide⟩, (), false, Move.right)
    else if i.val = 25 then
      -- restore (clone φ3): peek: 1 = scratch units remain (return); 0 = done — park
      if b then (⟨26, by decide⟩, (), b, Move.left)
      else (⟨30, by decide⟩, (), b, Move.left)
    else if i.val = 26 then
      -- restore (clone φ4): scan ← the gap's 0s; the first 1 is the dst's right end
      if b then (⟨27, by decide⟩, (), b, Move.stay)
      else (⟨26, by decide⟩, (), b, Move.left)
    else if i.val = 27 then
      -- restore (clone φ5): walk ← the dst ones; the 0 left of the block delimits HOME
      if b then (⟨27, by decide⟩, (), b, Move.left)
      else (⟨28, by decide⟩, (), b, Move.stay)
    else if i.val = 28 then
      -- restore (clone φ6): re-home one step right onto the dst's leftmost one (the anchor)
      (⟨29, by decide⟩, (), b, Move.right)
    else if i.val = 29 then
      -- restore (clone φ7): the back-edge re-enters the restore walk
      (⟨22, by decide⟩, (), b, Move.stay)
    else if i.val = 30 then
      -- park: scan ← zeros; the first 1 is the source's rightmost one (or the bare anchor, k = 0)
      if b then (⟨31, by decide⟩, (), b, Move.left)
      else (⟨30, by decide⟩, (), b, Move.left)
    else if i.val = 31 then
      -- park: walk ← the source + anchor block; the first 0 is gap₁'s right end
      if b then (⟨31, by decide⟩, (), b, Move.left)
      else (⟨32, by decide⟩, (), b, Move.stay)
    else if i.val = 32 then
      -- park: scan ← gap₁; the first 1 is the entry's rightmost one
      if b then (⟨33, by decide⟩, (), b, Move.left)
      else (⟨32, by decide⟩, (), b, Move.left)
    else if i.val = 33 then
      -- park: walk ← the entry ones; the first 0 is HOME (the entry delimiter at opBase)
      if b then (⟨33, by decide⟩, (), b, Move.left)
      else (⟨34, by decide⟩, (), b, Move.stay)
    else
      -- φ34: accept — idle
      (⟨34, by decide⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem valuePushProgram_numPhases : valuePushProgram.numPhases = 35 := rfl

@[simp] theorem valuePushProgram_startPhase : (valuePushProgram.startPhase : Nat) = 0 := rfl

@[simp] theorem valuePushProgram_acceptPhase : (valuePushProgram.acceptPhase : Nat) = 34 := rfl

/-! ### Single-step transition characterizations (one per φ/bit arm) -/

theorem valuePushProgram_t0 (b : Bool) :
    valuePushProgram.transition ⟨0, by decide⟩ () b = (⟨1, by decide⟩, (), b, Move.right) := rfl

theorem valuePushProgram_t1 (b : Bool) :
    valuePushProgram.transition ⟨1, by decide⟩ () b = (⟨2, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t2 (b : Bool) :
    valuePushProgram.transition ⟨2, by decide⟩ () b = (⟨3, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t3_one :
    valuePushProgram.transition ⟨3, by decide⟩ () true
      = (⟨4, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t3_zero :
    valuePushProgram.transition ⟨3, by decide⟩ () false
      = (⟨3, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t4_one :
    valuePushProgram.transition ⟨4, by decide⟩ () true
      = (⟨5, by decide⟩, (), true, Move.stay) := rfl

theorem valuePushProgram_t4_zero :
    valuePushProgram.transition ⟨4, by decide⟩ () false
      = (⟨30, by decide⟩, (), false, Move.stay) := rfl

theorem valuePushProgram_t5 (b : Bool) :
    valuePushProgram.transition ⟨5, by decide⟩ () b
      = (⟨6, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t6_one :
    valuePushProgram.transition ⟨6, by decide⟩ () true
      = (⟨7, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t6_zero :
    valuePushProgram.transition ⟨6, by decide⟩ () false
      = (⟨16, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t7_one :
    valuePushProgram.transition ⟨7, by decide⟩ () true
      = (⟨8, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t7_zero :
    valuePushProgram.transition ⟨7, by decide⟩ () false
      = (⟨7, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t8_one :
    valuePushProgram.transition ⟨8, by decide⟩ () true
      = (⟨9, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t8_zero :
    valuePushProgram.transition ⟨8, by decide⟩ () false
      = (⟨8, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t9 (b : Bool) :
    valuePushProgram.transition ⟨9, by decide⟩ () b
      = (⟨10, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t10_one :
    valuePushProgram.transition ⟨10, by decide⟩ () true
      = (⟨11, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t10_zero :
    valuePushProgram.transition ⟨10, by decide⟩ () false
      = (⟨10, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t11_one :
    valuePushProgram.transition ⟨11, by decide⟩ () true
      = (⟨12, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t11_zero :
    valuePushProgram.transition ⟨11, by decide⟩ () false
      = (⟨11, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t12_one :
    valuePushProgram.transition ⟨12, by decide⟩ () true
      = (⟨12, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t12_zero :
    valuePushProgram.transition ⟨12, by decide⟩ () false
      = (⟨13, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t13_one :
    valuePushProgram.transition ⟨13, by decide⟩ () true
      = (⟨13, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t13_zero :
    valuePushProgram.transition ⟨13, by decide⟩ () false
      = (⟨14, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t14_one :
    valuePushProgram.transition ⟨14, by decide⟩ () true
      = (⟨14, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t14_zero :
    valuePushProgram.transition ⟨14, by decide⟩ () false
      = (⟨15, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t15_one :
    valuePushProgram.transition ⟨15, by decide⟩ () true
      = (⟨15, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t15_zero :
    valuePushProgram.transition ⟨15, by decide⟩ () false
      = (⟨5, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t16_one :
    valuePushProgram.transition ⟨16, by decide⟩ () true
      = (⟨16, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t16_zero :
    valuePushProgram.transition ⟨16, by decide⟩ () false
      = (⟨17, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t17_one :
    valuePushProgram.transition ⟨17, by decide⟩ () true
      = (⟨17, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t17_zero :
    valuePushProgram.transition ⟨17, by decide⟩ () false
      = (⟨18, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t18_one :
    valuePushProgram.transition ⟨18, by decide⟩ () true
      = (⟨19, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t18_zero :
    valuePushProgram.transition ⟨18, by decide⟩ () false
      = (⟨18, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t19_one :
    valuePushProgram.transition ⟨19, by decide⟩ () true
      = (⟨20, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t19_zero :
    valuePushProgram.transition ⟨19, by decide⟩ () false
      = (⟨19, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t20 (b : Bool) :
    valuePushProgram.transition ⟨20, by decide⟩ () b
      = (⟨21, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t21_one :
    valuePushProgram.transition ⟨21, by decide⟩ () true
      = (⟨22, by decide⟩, (), true, Move.stay) := rfl

theorem valuePushProgram_t21_zero :
    valuePushProgram.transition ⟨21, by decide⟩ () false
      = (⟨21, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t22_one :
    valuePushProgram.transition ⟨22, by decide⟩ () true
      = (⟨22, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t22_zero :
    valuePushProgram.transition ⟨22, by decide⟩ () false
      = (⟨23, by decide⟩, (), true, Move.right) := rfl

theorem valuePushProgram_t23_one :
    valuePushProgram.transition ⟨23, by decide⟩ () true
      = (⟨24, by decide⟩, (), true, Move.stay) := rfl

theorem valuePushProgram_t23_zero :
    valuePushProgram.transition ⟨23, by decide⟩ () false
      = (⟨23, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t24 (b : Bool) :
    valuePushProgram.transition ⟨24, by decide⟩ () b
      = (⟨25, by decide⟩, (), false, Move.right) := rfl

theorem valuePushProgram_t25_one :
    valuePushProgram.transition ⟨25, by decide⟩ () true
      = (⟨26, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t25_zero :
    valuePushProgram.transition ⟨25, by decide⟩ () false
      = (⟨30, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t26_one :
    valuePushProgram.transition ⟨26, by decide⟩ () true
      = (⟨27, by decide⟩, (), true, Move.stay) := rfl

theorem valuePushProgram_t26_zero :
    valuePushProgram.transition ⟨26, by decide⟩ () false
      = (⟨26, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t27_one :
    valuePushProgram.transition ⟨27, by decide⟩ () true
      = (⟨27, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t27_zero :
    valuePushProgram.transition ⟨27, by decide⟩ () false
      = (⟨28, by decide⟩, (), false, Move.stay) := rfl

theorem valuePushProgram_t28 (b : Bool) :
    valuePushProgram.transition ⟨28, by decide⟩ () b
      = (⟨29, by decide⟩, (), b, Move.right) := rfl

theorem valuePushProgram_t29 (b : Bool) :
    valuePushProgram.transition ⟨29, by decide⟩ () b
      = (⟨22, by decide⟩, (), b, Move.stay) := rfl

theorem valuePushProgram_t30_one :
    valuePushProgram.transition ⟨30, by decide⟩ () true
      = (⟨31, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t30_zero :
    valuePushProgram.transition ⟨30, by decide⟩ () false
      = (⟨30, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t31_one :
    valuePushProgram.transition ⟨31, by decide⟩ () true
      = (⟨31, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t31_zero :
    valuePushProgram.transition ⟨31, by decide⟩ () false
      = (⟨32, by decide⟩, (), false, Move.stay) := rfl

theorem valuePushProgram_t32_one :
    valuePushProgram.transition ⟨32, by decide⟩ () true
      = (⟨33, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t32_zero :
    valuePushProgram.transition ⟨32, by decide⟩ () false
      = (⟨32, by decide⟩, (), false, Move.left) := rfl

theorem valuePushProgram_t33_one :
    valuePushProgram.transition ⟨33, by decide⟩ () true
      = (⟨33, by decide⟩, (), true, Move.left) := rfl

theorem valuePushProgram_t33_zero :
    valuePushProgram.transition ⟨33, by decide⟩ () false
      = (⟨34, by decide⟩, (), false, Move.stay) := rfl

theorem valuePushProgram_t34 (b : Bool) :
    valuePushProgram.transition ⟨34, by decide⟩ () b
      = (⟨34, by decide⟩, (), b, Move.stay) := rfl

end ContractExpansion
end Frontier
end Pnp4
