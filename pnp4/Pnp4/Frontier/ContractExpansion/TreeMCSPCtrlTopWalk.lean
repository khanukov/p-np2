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
    (hk : 1 ≤ k ∧ k ≤ 4) (hred : redirect k = none)
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

/-- **The empty hop**: one counted one (the lone sentinel) — `3` steps end at the empty verdict's
redirect target, head one left of the start (the dead cell), tape unchanged. -/
theorem run_ctrlTop_empty_hop (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    {nxt : Nat} (hred5 : redirect 5 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 1 ≤ (c0.head : Nat))
    (hpeek : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 3).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 3).tape = c0.tape := by
  rw [show (3 : Nat) = (1 + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := ctrlTopWalk_open_step hUP c0 hred0 hphase hpos
  rw [← hc1] at hp1 hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hb1 : c1.tape c1.head = false := by
    rw [ht1]; exact hpeek c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := ctrlTopWalk_verdict_step hUP c1 1 (by omega) hred1 hp1 hb1
  rw [← hc2] at hp2 hh2 ht2
  obtain ⟨hp3, hh3, ht3⟩ := ctrlTopWalk_redirect_step hUP c2 5 (by omega) hred5
    (by rw [hp2])
  refine ⟨hp3, ?_, ?_⟩
  · rw [hh3, hh2, hh1]
  · rw [ht3, ht2, ht1]

/-- **The tnot hop**: two counted ones — `4` steps end at the tnot verdict's redirect target, head
two left of the start (the separator), tape unchanged. -/
theorem run_ctrlTop_tnot_hop (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    (hred2 : redirect 2 = none) {nxt : Nat} (hred6 : redirect 6 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 2 ≤ (c0.head : Nat))
    (hone1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = true)
    (hsep : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 2 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 4).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 4).head : Nat) = (c0.head : Nat) - 2
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 4).tape = c0.tape := by
  rw [show (4 : Nat) = ((1 + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := ctrlTopWalk_open_step hUP c0 hred0 hphase (by omega)
  rw [← hc1] at hp1 hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hb1 : c1.tape c1.head = true := by
    rw [ht1]; exact hone1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := ctrlTopWalk_one_step hUP c1 1 (by omega) hred1 hp1 hb1 (by omega)
  rw [← hc2] at hp2 hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hb2 : c2.tape c2.head = false := by
    rw [ht2, ht1]; exact hsep c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := ctrlTopWalk_verdict_step hUP c2 2 (by omega) hred2 hp2 hb2
  rw [← hc3] at hp3 hh3 ht3
  obtain ⟨hp4, hh4, ht4⟩ := ctrlTopWalk_redirect_step hUP c3 6 (by omega) hred6
    (by rw [hp3])
  refine ⟨hp4, ?_, ?_⟩
  · rw [hh4, hh3, hh2, hh1]
    omega
  · rw [ht4, ht3, ht2, ht1]

/-- **The tand hop**: three counted ones — `5` steps end at the tand verdict's redirect target,
head three left of the start (the separator), tape unchanged. -/
theorem run_ctrlTop_tand_hop (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    (hred2 : redirect 2 = none) (hred3 : redirect 3 = none)
    {nxt : Nat} (hred7 : redirect 7 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 3 ≤ (c0.head : Nat))
    (hone1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = true)
    (hone2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 2 → c0.tape p = true)
    (hsep : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 3 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 5).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 5).head : Nat) = (c0.head : Nat) - 3
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 5).tape = c0.tape := by
  rw [show (5 : Nat) = (((1 + 1) + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one,
    TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := ctrlTopWalk_open_step hUP c0 hred0 hphase (by omega)
  rw [← hc1] at hp1 hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hb1 : c1.tape c1.head = true := by
    rw [ht1]; exact hone1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := ctrlTopWalk_one_step hUP c1 1 (by omega) hred1 hp1 hb1 (by omega)
  rw [← hc2] at hp2 hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hb2 : c2.tape c2.head = true := by
    rw [ht2, ht1]; exact hone2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := ctrlTopWalk_one_step hUP c2 2 (by omega) hred2 hp2 hb2 (by omega)
  rw [← hc3] at hp3 hh3 ht3
  set c4 := TM.stepConfig (M := U.toPhased.toTM) c3 with hc4
  have hb3 : c3.tape c3.head = false := by
    rw [ht3, ht2, ht1]; exact hsep c3.head (by omega)
  obtain ⟨hp4, hh4, ht4⟩ := ctrlTopWalk_verdict_step hUP c3 3 (by omega) hred3 hp3 hb3
  rw [← hc4] at hp4 hh4 ht4
  obtain ⟨hp5, hh5, ht5⟩ := ctrlTopWalk_redirect_step hUP c4 7 (by omega) hred7
    (by rw [hp4])
  refine ⟨hp5, ?_, ?_⟩
  · rw [hh5, hh4, hh3, hh2, hh1]
    omega
  · rw [ht5, ht4, ht3, ht2, ht1]

/-- **The tor hop**: four counted ones — `6` steps end at the tor verdict's redirect target, head
four left of the start (the separator), tape unchanged. -/
theorem run_ctrlTop_tor_hop (hUP : RegionEmbeddedMulti U ctrlTopWalk base redirect)
    {L : Nat} (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    (hred2 : redirect 2 = none) (hred3 : redirect 3 = none) (hred4 : redirect 4 = none)
    {nxt : Nat} (hred8 : redirect 8 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 4 ≤ (c0.head : Nat))
    (hone1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = true)
    (hone2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 2 → c0.tape p = true)
    (hone3 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 3 → c0.tape p = true)
    (hsep : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 4 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 6).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 6).head : Nat) = (c0.head : Nat) - 4
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 6).tape = c0.tape := by
  rw [show (6 : Nat) = ((((1 + 1) + 1) + 1) + 1) + 1 from rfl, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_add, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one,
    TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := ctrlTopWalk_open_step hUP c0 hred0 hphase (by omega)
  rw [← hc1] at hp1 hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hb1 : c1.tape c1.head = true := by
    rw [ht1]; exact hone1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := ctrlTopWalk_one_step hUP c1 1 (by omega) hred1 hp1 hb1 (by omega)
  rw [← hc2] at hp2 hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hb2 : c2.tape c2.head = true := by
    rw [ht2, ht1]; exact hone2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := ctrlTopWalk_one_step hUP c2 2 (by omega) hred2 hp2 hb2 (by omega)
  rw [← hc3] at hp3 hh3 ht3
  set c4 := TM.stepConfig (M := U.toPhased.toTM) c3 with hc4
  have hb3 : c3.tape c3.head = true := by
    rw [ht3, ht2, ht1]; exact hone3 c3.head (by omega)
  obtain ⟨hp4, hh4, ht4⟩ := ctrlTopWalk_one_step hUP c3 3 (by omega) hred3 hp3 hb3 (by omega)
  rw [← hc4] at hp4 hh4 ht4
  set c5 := TM.stepConfig (M := U.toPhased.toTM) c4 with hc5
  have hb4 : c4.tape c4.head = false := by
    rw [ht4, ht3, ht2, ht1]; exact hsep c4.head (by omega)
  obtain ⟨hp5, hh5, ht5⟩ := ctrlTopWalk_verdict_step hUP c4 4 (by omega) hred4 hp4 hb4
  rw [← hc5] at hp5 hh5 ht5
  obtain ⟨hp6, hh6, ht6⟩ := ctrlTopWalk_redirect_step hUP c5 8 (by omega) hred8
    (by rw [hp5])
  refine ⟨hp6, ?_, ?_⟩
  · rw [hh6, hh5, hh4, hh3, hh2, hh1]
    omega
  · rw [ht6, ht5, ht4, ht3, ht2, ht1]

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
