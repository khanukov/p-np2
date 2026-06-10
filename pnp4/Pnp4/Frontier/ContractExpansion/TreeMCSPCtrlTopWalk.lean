import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionWriteSegment

/-!
# `ctrlTopWalk` — D2t-5b (Block A5m-4a): the settle dispatch read, one walking component

Walking left from the control top and **counting the ones** subsumes the empty probe *and* the tag
read (the A3 `≥ 2`-ones discipline exists exactly for this): `1` one then a `0` is the lone base
sentinel (**empty**); `2`/`3`/`4` ones then a `0` are the top frame's tag block — **tnot/tand/tor**
— with the head landing on the `0` **separator** left of the tag block (resp. the dead cell left of
the sentinel), where the rem-block read begins.

* `φ0` — step left off the top; `φ1`–`φ4` — count ones, branching to the verdicts;
* verdicts `φ5` (empty), `φ6` (tnot), `φ7` (tand), `φ8` (tor) idle; `φ9` rejects a fifth one.

The codec facts `encodeCtrlStackR_tagBlock_true` / `encodeCtrlStackR_tagSep_false` pin the tag
block's cells and its separator; the four **host-generic verdict hops**
(`run_ctrlTopWalk_{empty,tnot,tand,tor}_hop`, on `RegionEmbeddedMulti`) land each verdict at its
redirect target with the head on the separator, tape untouched.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component with
host-generic verdict runs; proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### Codec facts: the tag block and its separator -/

/-- The top frame's tag block: the encoded stack's last `tagCode + 2` cells are `1`. -/
theorem encodeCtrlStackR_tagBlock_true (tag : ITag) (rem : Nat) (rest : List (ITag × Nat))
    (i : Nat) (hi : i < tag.tagCode + 2) :
    (encodeCtrlStackR ((tag, rem) :: rest)).getD
      ((encodeCtrlStackR ((tag, rem) :: rest)).length - 1 - i) false = true := by
  have hsplit : encodeCtrlStackR ((tag, rem) :: rest)
      = (encodeCtrlStackR rest ++ (false :: List.replicate (rem + 1) true ++ [false]))
        ++ List.replicate (tag.tagCode + 2) true := by
    rw [encodeCtrlStackR_cons]
    show encodeCtrlStackR rest
        ++ (false :: (List.replicate (rem + 1) true
          ++ (false :: List.replicate (tag.tagCode + 2) true)))
      = _
    simp [List.append_assoc]
  rw [hsplit]
  have hlen : ((encodeCtrlStackR rest ++ (false :: List.replicate (rem + 1) true ++ [false]))
      ++ List.replicate (tag.tagCode + 2) true).length
      = (encodeCtrlStackR rest ++ (false :: List.replicate (rem + 1) true ++ [false])).length
        + (tag.tagCode + 2) := by
    rw [List.length_append, List.length_replicate]
  rw [hlen, List.getD_append_right _ _ _ _ (by omega)]
  exact getD_replicate_true _ _ (by omega)

/-- The `0` separator immediately left of the top frame's tag block. -/
theorem encodeCtrlStackR_tagSep_false (tag : ITag) (rem : Nat) (rest : List (ITag × Nat)) :
    (encodeCtrlStackR ((tag, rem) :: rest)).getD
      ((encodeCtrlStackR ((tag, rem) :: rest)).length - 1 - (tag.tagCode + 2)) false = false := by
  have hsplit : encodeCtrlStackR ((tag, rem) :: rest)
      = (encodeCtrlStackR rest ++ false :: List.replicate (rem + 1) true)
        ++ ([false] ++ List.replicate (tag.tagCode + 2) true) := by
    rw [encodeCtrlStackR_cons]
    show encodeCtrlStackR rest
        ++ (false :: (List.replicate (rem + 1) true
          ++ (false :: List.replicate (tag.tagCode + 2) true)))
      = _
    simp [List.append_assoc]
  rw [hsplit]
  have hlen : ((encodeCtrlStackR rest ++ false :: List.replicate (rem + 1) true)
      ++ ([false] ++ List.replicate (tag.tagCode + 2) true)).length
      = (encodeCtrlStackR rest ++ false :: List.replicate (rem + 1) true).length
        + (tag.tagCode + 3) := by
    simp only [List.length_append, List.length_cons, List.length_replicate,
      List.length_nil]
    omega
  rw [hlen, List.getD_append_right _ _ _ _ (by omega)]
  have : (encodeCtrlStackR rest ++ false :: List.replicate (rem + 1) true).length
      + (tag.tagCode + 3) - 1 - (tag.tagCode + 2)
      - (encodeCtrlStackR rest ++ false :: List.replicate (rem + 1) true).length = 0 := by
    omega
  rw [this]
  rfl

/-! ### The walking component -/

/-- **The control-top walk** (10 phases): step left off the top, count the ones, land on the `0`
left of the counted block — verdicts: `1` one = the base sentinel (**empty**, `φ5`); `2`/`3`/`4`
ones = the top frame's tag block (**tnot/tand/tor**, `φ6`/`φ7`/`φ8`); a fifth one rejects
(`φ9`). -/
def ctrlTopWalk : ConstStatePhasedProgram Unit where
  numPhases := 10
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨5, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.left)
    else if i.val = 1 then
      if b then (⟨2, by omega⟩, (), b, Move.left) else (⟨5, by omega⟩, (), b, Move.stay)
    else if i.val = 2 then
      if b then (⟨3, by omega⟩, (), b, Move.left) else (⟨6, by omega⟩, (), b, Move.stay)
    else if i.val = 3 then
      if b then (⟨4, by omega⟩, (), b, Move.left) else (⟨7, by omega⟩, (), b, Move.stay)
    else if i.val = 4 then
      if b then (⟨9, by omega⟩, (), b, Move.stay) else (⟨8, by omega⟩, (), b, Move.stay)
    else (⟨i.val, i.isLt⟩, (), b, Move.stay)
  timeBound := fun _ => 5

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- One in-host walk step over a `1` (phases `1`–`3`): the phase advances, the head moves left,
the tape is unchanged. -/
private theorem ctrlTopWalk_one_step (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (k : Nat)
    (hk : 1 ≤ k ∧ k ≤ 3) (hred : redirect k = none)
    (hphase : (c.state.fst : Nat) = base + k) (hbit : c.tape c.head = true)
    (hpos : 1 ≤ (c.head : Nat)) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = base + (k + 1)
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hne : ¬ (c.head : Nat) = 0 := by omega
  have hij : (c.state.fst : Nat) = base + (⟨k, by simp [ctrlTopWalk]; omega⟩
      : Fin ctrlTopWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [hUP.stepConfig_normal_phase c rfl _ hij hred]
    obtain ⟨h1, h3⟩ := hk
    interval_cases k <;> simp [ctrlTopWalk, hbit]
  · rw [hUP.stepConfig_normal_head c rfl _ hij hred]
    have hm : (ctrlTopWalk.transition ⟨k, by simp [ctrlTopWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.left := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [ctrlTopWalk, hbit]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [hUP.stepConfig_normal_tape c rfl _ hij hred]
    have hb : (ctrlTopWalk.transition ⟨k, by simp [ctrlTopWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [ctrlTopWalk, hbit]
    rw [hb]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

/-- The opening step (`φ0`): step left off the top, any bit. -/
private theorem ctrlTopWalk_open_step (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L)
    (hred : redirect 0 = none)
    (hphase : (c.state.fst : Nat) = base) (hpos : 1 ≤ (c.head : Nat)) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = base + 1
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hne : ¬ (c.head : Nat) = 0 := by omega
  have hij : (c.state.fst : Nat) = base + (⟨0, by simp [ctrlTopWalk]⟩
      : Fin ctrlTopWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [hUP.stepConfig_normal_phase c rfl _ hij hred]
    simp [ctrlTopWalk]
  · rw [hUP.stepConfig_normal_head c rfl _ hij hred]
    have hm : (ctrlTopWalk.transition ⟨0, by simp [ctrlTopWalk]⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.left := by
      simp [ctrlTopWalk]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [hUP.stepConfig_normal_tape c rfl _ hij hred]
    have hb : (ctrlTopWalk.transition ⟨0, by simp [ctrlTopWalk]⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      simp [ctrlTopWalk]
    rw [hb]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

/-- The verdict step (phases `1`–`3` on a `0`): the phase jumps to the verdict (`4 + k`), head and
tape unchanged. -/
private theorem ctrlTopWalk_verdict_step (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (k : Nat)
    (hk : 1 ≤ k ∧ k ≤ 3) (hred : redirect k = none)
    (hphase : (c.state.fst : Nat) = base + k) (hbit : c.tape c.head = false) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = base + (4 + k)
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat)
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hij : (c.state.fst : Nat) = base + (⟨k, by simp [ctrlTopWalk]; omega⟩
      : Fin ctrlTopWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [hUP.stepConfig_normal_phase c rfl _ hij hred]
    obtain ⟨h1, h3⟩ := hk
    interval_cases k <;> simp [ctrlTopWalk, hbit]
  · rw [hUP.stepConfig_normal_head c rfl _ hij hred]
    have hm : (ctrlTopWalk.transition ⟨k, by simp [ctrlTopWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.stay := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [ctrlTopWalk, hbit]
    rw [hm]
    simp [Configuration.moveHead]
  · rw [hUP.stepConfig_normal_tape c rfl _ hij hred]
    have hb : (ctrlTopWalk.transition ⟨k, by simp [ctrlTopWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [ctrlTopWalk, hbit]
    rw [hb]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

/-- The redirect step at a verdict phase `v` (`5 ≤ v ≤ 8`). -/
private theorem ctrlTopWalk_redirect_step (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (v : Nat)
    (hv : v < 10) {nxt : Nat} (hred : redirect v = some nxt)
    (hphase : (c.state.fst : Nat) = base + v) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = nxt
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat)
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hij : (c.state.fst : Nat) = base + (⟨v, by simp [ctrlTopWalk]; omega⟩
      : Fin ctrlTopWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c rfl _ hij hred
  · rw [hUP.stepConfig_redirect_head c rfl _ hij hred]
  · rw [hUP.stepConfig_redirect_tape c rfl _ hij hred]

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
