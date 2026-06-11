import Pnp4.Frontier.ContractExpansion.TreeMCSPCtrlTopWalk

/-!
# `remWalk` — D2t-5b (Block A5m-4b): the rem-block read, from the separator to the frame base

After `ctrlTopWalk` lands on the tag block's `0` separator, the settle decision needs the top
frame's remaining count: walking left and **counting the ones** of the rem block (`rem + 1` ones)
distinguishes the reachable cases — `2` ones = `rem 1` (**pop**), `3` ones = `rem 2` (**dec**) —
with the head landing on the frame's **base `0`**, exactly where the dec arm's frame rewrite
(`run_writeBits_hop`) begins.

* `φ0` — step left off the separator (onto the rem block's last `1`); `φ1`–`φ4` — count, branching;
* verdicts `φ5` (`rem = 1`, pop), `φ6` (`rem = 2`, dec) idle; `φ7` rejects.

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

/-- **The rem-block walk** (8 phases): step left off the separator, count the ones — verdicts:
`2` ones = `rem 1` (**pop**, `φ5`); `3` ones = `rem 2` (**dec**, `φ6`); zero or one ones are
unreachable and a fourth one rejects (`φ7`).  The verdicts land on the frame's base `0`. -/
def remWalk : ConstStatePhasedProgram Unit where
  numPhases := 8
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨5, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.left)
    else if i.val = 1 then
      if b then (⟨2, by omega⟩, (), b, Move.left) else (⟨7, by omega⟩, (), b, Move.stay)
    else if i.val = 2 then
      if b then (⟨3, by omega⟩, (), b, Move.left) else (⟨7, by omega⟩, (), b, Move.stay)
    else if i.val = 3 then
      if b then (⟨4, by omega⟩, (), b, Move.left) else (⟨5, by omega⟩, (), b, Move.stay)
    else if i.val = 4 then
      if b then (⟨7, by omega⟩, (), b, Move.stay) else (⟨6, by omega⟩, (), b, Move.stay)
    else (⟨i.val, i.isLt⟩, (), b, Move.stay)
  timeBound := fun _ => 5

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- The opening step (`φ0`): step left off the separator, any bit. -/
private theorem remWalk_open_step (hUP : RegionEmbeddedMulti U remWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L)
    (hred : redirect 0 = none)
    (hphase : (c.state.fst : Nat) = base) (hpos : 1 ≤ (c.head : Nat)) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = base + 1
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hne : ¬ (c.head : Nat) = 0 := by omega
  have hij : (c.state.fst : Nat) = base + (⟨0, by simp [remWalk]⟩
      : Fin remWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [hUP.stepConfig_normal_phase c rfl _ hij hred]
    simp [remWalk]
  · rw [hUP.stepConfig_normal_head c rfl _ hij hred]
    have hm : (remWalk.transition ⟨0, by simp [remWalk]⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.left := by
      simp [remWalk]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [hUP.stepConfig_normal_tape c rfl _ hij hred]
    have hb : (remWalk.transition ⟨0, by simp [remWalk]⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      simp [remWalk]
    rw [hb]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

/-- One in-host walk step over a `1` (phases `1`–`3`): the phase advances, the head moves left. -/
private theorem remWalk_one_step (hUP : RegionEmbeddedMulti U remWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (k : Nat)
    (hk : 1 ≤ k ∧ k ≤ 3) (hred : redirect k = none)
    (hphase : (c.state.fst : Nat) = base + k) (hbit : c.tape c.head = true)
    (hpos : 1 ≤ (c.head : Nat)) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = base + (k + 1)
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hne : ¬ (c.head : Nat) = 0 := by omega
  have hij : (c.state.fst : Nat) = base + (⟨k, by simp [remWalk]; omega⟩
      : Fin remWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [hUP.stepConfig_normal_phase c rfl _ hij hred]
    obtain ⟨h1, h3⟩ := hk
    interval_cases k <;> simp [remWalk, hbit]
  · rw [hUP.stepConfig_normal_head c rfl _ hij hred]
    have hm : (remWalk.transition ⟨k, by simp [remWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.left := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [remWalk, hbit]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [hUP.stepConfig_normal_tape c rfl _ hij hred]
    have hb : (remWalk.transition ⟨k, by simp [remWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [remWalk, hbit]
    rw [hb]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

/-- The verdict step (phases `3`–`4` on a `0`): the phase jumps to the verdict (`k + 2`), head and
tape unchanged. -/
private theorem remWalk_verdict_step (hUP : RegionEmbeddedMulti U remWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (k : Nat)
    (hk : 3 ≤ k ∧ k ≤ 4) (hred : redirect k = none)
    (hphase : (c.state.fst : Nat) = base + k) (hbit : c.tape c.head = false) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = base + (k + 2)
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat)
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hij : (c.state.fst : Nat) = base + (⟨k, by simp [remWalk]; omega⟩
      : Fin remWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [hUP.stepConfig_normal_phase c rfl _ hij hred]
    obtain ⟨h1, h3⟩ := hk
    interval_cases k <;> simp [remWalk, hbit]
  · rw [hUP.stepConfig_normal_head c rfl _ hij hred]
    have hm : (remWalk.transition ⟨k, by simp [remWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.stay := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [remWalk, hbit]
    rw [hm]
    simp [Configuration.moveHead]
  · rw [hUP.stepConfig_normal_tape c rfl _ hij hred]
    have hb : (remWalk.transition ⟨k, by simp [remWalk]; omega⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      obtain ⟨h1, h3⟩ := hk
      interval_cases k <;> simp [remWalk, hbit]
    rw [hb]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

/-- The redirect step at a verdict phase. -/
private theorem remWalk_redirect_step (hUP : RegionEmbeddedMulti U remWalk base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (v : Nat)
    (hv : v < 8) {nxt : Nat} (hred : redirect v = some nxt)
    (hphase : (c.state.fst : Nat) = base + v) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = nxt
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat)
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hij : (c.state.fst : Nat) = base + (⟨v, by simp [remWalk]; omega⟩
      : Fin remWalk.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c rfl _ hij hred
  · rw [hUP.stepConfig_redirect_head c rfl _ hij hred]
  · rw [hUP.stepConfig_redirect_tape c rfl _ hij hred]

/-- **The pop hop** (`rem = 1`, two counted ones): `5` steps end at the pop verdict's redirect
target, head three left of the start (the frame base), tape unchanged. -/
theorem run_rem_pop_hop (hUP : RegionEmbeddedMulti U remWalk base redirect)
    {L : Nat} (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    (hred2 : redirect 2 = none) (hred3 : redirect 3 = none)
    {nxt : Nat} (hred5 : redirect 5 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 3 ≤ (c0.head : Nat))
    (hone1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = true)
    (hone2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 2 → c0.tape p = true)
    (hbase : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 3 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 5).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 5).head : Nat) = (c0.head : Nat) - 3
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 5).tape = c0.tape := by
  rw [show (5 : Nat) = (((1 + 1) + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one,
    TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := remWalk_open_step hUP c0 hred0 hphase (by omega)
  rw [← hc1] at hp1 hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hb1 : c1.tape c1.head = true := by
    rw [ht1]; exact hone1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := remWalk_one_step hUP c1 1 (by omega) hred1 hp1 hb1 (by omega)
  rw [← hc2] at hp2 hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hb2 : c2.tape c2.head = true := by
    rw [ht2, ht1]; exact hone2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := remWalk_one_step hUP c2 2 (by omega) hred2 hp2 hb2 (by omega)
  rw [← hc3] at hp3 hh3 ht3
  set c4 := TM.stepConfig (M := U.toPhased.toTM) c3 with hc4
  have hb3 : c3.tape c3.head = false := by
    rw [ht3, ht2, ht1]; exact hbase c3.head (by omega)
  obtain ⟨hp4, hh4, ht4⟩ := remWalk_verdict_step hUP c3 3 (by omega) hred3 hp3 hb3
  rw [← hc4] at hp4 hh4 ht4
  obtain ⟨hp5, hh5, ht5⟩ := remWalk_redirect_step hUP c4 5 (by omega) hred5 (by rw [hp4])
  refine ⟨hp5, ?_, ?_⟩
  · rw [hh5, hh4, hh3, hh2, hh1]
    omega
  · rw [ht5, ht4, ht3, ht2, ht1]

/-- **The dec hop** (`rem = 2`, three counted ones): `6` steps end at the dec verdict's redirect
target, head four left of the start (the frame base), tape unchanged. -/
theorem run_rem_dec_hop (hUP : RegionEmbeddedMulti U remWalk base redirect)
    {L : Nat} (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    (hred2 : redirect 2 = none) (hred3 : redirect 3 = none) (hred4 : redirect 4 = none)
    {nxt : Nat} (hred6 : redirect 6 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 4 ≤ (c0.head : Nat))
    (hone1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = true)
    (hone2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 2 → c0.tape p = true)
    (hone3 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 3 → c0.tape p = true)
    (hbase : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 4 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 6).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 6).head : Nat) = (c0.head : Nat) - 4
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 6).tape = c0.tape := by
  rw [show (6 : Nat) = ((((1 + 1) + 1) + 1) + 1) + 1 from rfl, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_add, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one,
    TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := remWalk_open_step hUP c0 hred0 hphase (by omega)
  rw [← hc1] at hp1 hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hb1 : c1.tape c1.head = true := by
    rw [ht1]; exact hone1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := remWalk_one_step hUP c1 1 (by omega) hred1 hp1 hb1 (by omega)
  rw [← hc2] at hp2 hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hb2 : c2.tape c2.head = true := by
    rw [ht2, ht1]; exact hone2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := remWalk_one_step hUP c2 2 (by omega) hred2 hp2 hb2 (by omega)
  rw [← hc3] at hp3 hh3 ht3
  set c4 := TM.stepConfig (M := U.toPhased.toTM) c3 with hc4
  have hb3 : c3.tape c3.head = true := by
    rw [ht3, ht2, ht1]; exact hone3 c3.head (by omega)
  obtain ⟨hp4, hh4, ht4⟩ := remWalk_one_step hUP c3 3 (by omega) hred3 hp3 hb3 (by omega)
  rw [← hc4] at hp4 hh4 ht4
  set c5 := TM.stepConfig (M := U.toPhased.toTM) c4 with hc5
  have hb4 : c4.tape c4.head = false := by
    rw [ht4, ht3, ht2, ht1]; exact hbase c4.head (by omega)
  obtain ⟨hp5, hh5, ht5⟩ := remWalk_verdict_step hUP c4 4 (by omega) hred4 hp4 hb4
  rw [← hc5] at hp5 hh5 ht5
  obtain ⟨hp6, hh6, ht6⟩ := remWalk_redirect_step hUP c5 6 (by omega) hred6 (by rw [hp5])
  refine ⟨hp6, ?_, ?_⟩
  · rw [hh6, hh5, hh4, hh3, hh2, hh1]
    omega
  · rw [ht6, ht5, ht4, ht3, ht2, ht1]

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
