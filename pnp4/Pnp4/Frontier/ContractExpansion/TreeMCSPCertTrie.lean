import Pnp4.Frontier.ContractExpansion.TreeMCSPDecIterRun

/-!
# `certTrie` — D2t-5b (Block A5m-5a): the certificate tag trie (the read dispatch)

The reading dispatch: from the cursor (the next token's first tag cell), read the three binary tag
cells rightward and branch — `000` input, `001` const, `010` not, `011` and, `100` or
(`encodePreToken`'s patterns); `101`/`11_` reject.  One component subsumes the whole read dispatch,
with a verdict phase per token kind and host-generic 4-step hops (three reads plus the redirect),
each ending with the head **three cells right** of the cursor (just past the tag), tape untouched.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component with
host-generic verdict hops; proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The certificate tag trie** (12 phases): three rightward reads branching on the binary tag —
verdicts `φ6` input (`000`), `φ7` const (`001`), `φ8` not (`010`), `φ9` and (`011`), `φ10` or
(`100`); `φ11` rejects. -/
def certTrie : ConstStatePhasedProgram Unit where
  numPhases := 12
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨6, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      ((if b then ⟨2, by omega⟩ else ⟨1, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 1 then
      ((if b then ⟨4, by omega⟩ else ⟨3, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 2 then
      ((if b then ⟨11, by omega⟩ else ⟨5, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 3 then
      ((if b then ⟨7, by omega⟩ else ⟨6, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 4 then
      ((if b then ⟨9, by omega⟩ else ⟨8, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 5 then
      ((if b then ⟨11, by omega⟩ else ⟨10, by omega⟩ : Fin 12), (), b, Move.right)
    else (⟨i.val, i.isLt⟩, (), b, Move.stay)
  timeBound := fun _ => 4

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- One in-host trie read (phases `0`–`5`): the phase branches per the table, the head moves
right, the tape is unchanged. -/
private theorem certTrie_read_step (hUP : RegionEmbeddedMulti U certTrie base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (k t0 t1 : Nat)
    (hk : k ≤ 5) (hred : redirect k = none)
    (htab : ∀ b : Bool, (certTrie.transition ⟨k, by simp [certTrie]; omega⟩ () b).fst.val
      = if b then t1 else t0)
    (hphase : (c.state.fst : Nat) = base + k)
    (hroom : (c.head : Nat) + 1 < U.toPhased.toTM.tapeLength L) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat)
        = base + (if c.tape c.head then t1 else t0)
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hij : (c.state.fst : Nat) = base + (⟨k, by simp [certTrie]; omega⟩
      : Fin certTrie.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · rw [hUP.stepConfig_normal_phase c rfl _ hij hred]
    congr 1
    exact htab (c.tape c.head)
  · rw [hUP.stepConfig_normal_head c rfl _ hij hred]
    have hm : (certTrie.transition ⟨k, by simp [certTrie]; omega⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.right := by
      have hk5 : k ≤ 5 := hk
      interval_cases k <;> (cases hb : c.tape c.head <;> simp [certTrie, hb])
    rw [hm]
    simp only [Configuration.moveHead, dif_pos hroom]
  · rw [hUP.stepConfig_normal_tape c rfl _ hij hred]
    have hb : (certTrie.transition ⟨k, by simp [certTrie]; omega⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      have hk5 : k ≤ 5 := hk
      interval_cases k <;> (cases hbb : c.tape c.head <;> simp [certTrie, hbb])
    rw [hb]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

/-- The redirect step at a verdict phase. -/
private theorem certTrie_redirect_step (hUP : RegionEmbeddedMulti U certTrie base redirect)
    {L : Nat} (c : Configuration (M := U.toPhased.toTM) L) (v : Nat)
    (hv : v < 12) {nxt : Nat} (hred : redirect v = some nxt)
    (hphase : (c.state.fst : Nat) = base + v) :
    (((TM.stepConfig (M := U.toPhased.toTM) c).state).fst : Nat) = nxt
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) c).head : Nat) = (c.head : Nat)
      ∧ (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.tape := by
  have hij : (c.state.fst : Nat) = base + (⟨v, by simp [certTrie]; omega⟩
      : Fin certTrie.numPhases).val := by simpa using hphase
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c rfl _ hij hred
  · rw [hUP.stepConfig_redirect_head c rfl _ hij hred]
  · rw [hUP.stepConfig_redirect_tape c rfl _ hij hred]



/-- **The input hop** (`fff` read rightward): `4` steps end at the input
verdict's redirect target, head three cells right (just past the tag), tape unchanged. -/
theorem run_certTrie_input_hop (hUP : RegionEmbeddedMulti U certTrie base redirect)
    {L : Nat}
    (hred0 : redirect 0 = none)
    (hred1 : redirect 1 = none)
    (hred3 : redirect 3 = none)
    {nxt : Nat} (hredV : redirect 6 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 3 < U.toPhased.toTM.tapeLength L)
    (hb0 : c0.tape c0.head = false)
    (hb1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false)
    (hb2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 4).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 4).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 4).tape = c0.tape := by
  rw [show (4 : Nat) = ((1 + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := certTrie_read_step hUP c0 0 1 2 (by omega) hred0
    (fun b => by cases b <;> simp [certTrie]) hphase (by omega)
  rw [← hc1, hb0] at hp1
  rw [← hc1] at hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = false := by
    rw [ht1]; exact hb1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := certTrie_read_step hUP c1 1 3 4 (by omega) hred1
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp1) (by omega)
  rw [← hc2, hbit1] at hp2
  rw [← hc2] at hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hbit2 : c2.tape c2.head = false := by
    rw [ht2, ht1]; exact hb2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := certTrie_read_step hUP c2 3 6 7 (by omega) hred3
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp2) (by omega)
  rw [← hc3, hbit2] at hp3
  rw [← hc3] at hh3 ht3
  obtain ⟨hp4, hh4, ht4⟩ := certTrie_redirect_step hUP c3 6 (by omega) hredV
    (by simpa using hp3)
  refine ⟨hp4, ?_, ?_⟩
  · rw [hh4, hh3, hh2, hh1]
  · rw [ht4, ht3, ht2, ht1]


/-- **The const hop** (`fft` read rightward): `4` steps end at the const
verdict's redirect target, head three cells right (just past the tag), tape unchanged. -/
theorem run_certTrie_const_hop (hUP : RegionEmbeddedMulti U certTrie base redirect)
    {L : Nat}
    (hred0 : redirect 0 = none)
    (hred1 : redirect 1 = none)
    (hred3 : redirect 3 = none)
    {nxt : Nat} (hredV : redirect 7 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 3 < U.toPhased.toTM.tapeLength L)
    (hb0 : c0.tape c0.head = false)
    (hb1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false)
    (hb2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = true) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 4).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 4).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 4).tape = c0.tape := by
  rw [show (4 : Nat) = ((1 + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := certTrie_read_step hUP c0 0 1 2 (by omega) hred0
    (fun b => by cases b <;> simp [certTrie]) hphase (by omega)
  rw [← hc1, hb0] at hp1
  rw [← hc1] at hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = false := by
    rw [ht1]; exact hb1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := certTrie_read_step hUP c1 1 3 4 (by omega) hred1
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp1) (by omega)
  rw [← hc2, hbit1] at hp2
  rw [← hc2] at hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hbit2 : c2.tape c2.head = true := by
    rw [ht2, ht1]; exact hb2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := certTrie_read_step hUP c2 3 6 7 (by omega) hred3
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp2) (by omega)
  rw [← hc3, hbit2] at hp3
  rw [← hc3] at hh3 ht3
  obtain ⟨hp4, hh4, ht4⟩ := certTrie_redirect_step hUP c3 7 (by omega) hredV
    (by simpa using hp3)
  refine ⟨hp4, ?_, ?_⟩
  · rw [hh4, hh3, hh2, hh1]
  · rw [ht4, ht3, ht2, ht1]


/-- **The not hop** (`ftf` read rightward): `4` steps end at the not
verdict's redirect target, head three cells right (just past the tag), tape unchanged. -/
theorem run_certTrie_not_hop (hUP : RegionEmbeddedMulti U certTrie base redirect)
    {L : Nat}
    (hred0 : redirect 0 = none)
    (hred1 : redirect 1 = none)
    (hred4 : redirect 4 = none)
    {nxt : Nat} (hredV : redirect 8 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 3 < U.toPhased.toTM.tapeLength L)
    (hb0 : c0.tape c0.head = false)
    (hb1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true)
    (hb2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 4).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 4).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 4).tape = c0.tape := by
  rw [show (4 : Nat) = ((1 + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := certTrie_read_step hUP c0 0 1 2 (by omega) hred0
    (fun b => by cases b <;> simp [certTrie]) hphase (by omega)
  rw [← hc1, hb0] at hp1
  rw [← hc1] at hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = true := by
    rw [ht1]; exact hb1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := certTrie_read_step hUP c1 1 3 4 (by omega) hred1
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp1) (by omega)
  rw [← hc2, hbit1] at hp2
  rw [← hc2] at hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hbit2 : c2.tape c2.head = false := by
    rw [ht2, ht1]; exact hb2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := certTrie_read_step hUP c2 4 8 9 (by omega) hred4
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp2) (by omega)
  rw [← hc3, hbit2] at hp3
  rw [← hc3] at hh3 ht3
  obtain ⟨hp4, hh4, ht4⟩ := certTrie_redirect_step hUP c3 8 (by omega) hredV
    (by simpa using hp3)
  refine ⟨hp4, ?_, ?_⟩
  · rw [hh4, hh3, hh2, hh1]
  · rw [ht4, ht3, ht2, ht1]


/-- **The and hop** (`ftt` read rightward): `4` steps end at the and
verdict's redirect target, head three cells right (just past the tag), tape unchanged. -/
theorem run_certTrie_and_hop (hUP : RegionEmbeddedMulti U certTrie base redirect)
    {L : Nat}
    (hred0 : redirect 0 = none)
    (hred1 : redirect 1 = none)
    (hred4 : redirect 4 = none)
    {nxt : Nat} (hredV : redirect 9 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 3 < U.toPhased.toTM.tapeLength L)
    (hb0 : c0.tape c0.head = false)
    (hb1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true)
    (hb2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = true) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 4).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 4).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 4).tape = c0.tape := by
  rw [show (4 : Nat) = ((1 + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := certTrie_read_step hUP c0 0 1 2 (by omega) hred0
    (fun b => by cases b <;> simp [certTrie]) hphase (by omega)
  rw [← hc1, hb0] at hp1
  rw [← hc1] at hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = true := by
    rw [ht1]; exact hb1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := certTrie_read_step hUP c1 1 3 4 (by omega) hred1
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp1) (by omega)
  rw [← hc2, hbit1] at hp2
  rw [← hc2] at hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hbit2 : c2.tape c2.head = true := by
    rw [ht2, ht1]; exact hb2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := certTrie_read_step hUP c2 4 8 9 (by omega) hred4
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp2) (by omega)
  rw [← hc3, hbit2] at hp3
  rw [← hc3] at hh3 ht3
  obtain ⟨hp4, hh4, ht4⟩ := certTrie_redirect_step hUP c3 9 (by omega) hredV
    (by simpa using hp3)
  refine ⟨hp4, ?_, ?_⟩
  · rw [hh4, hh3, hh2, hh1]
  · rw [ht4, ht3, ht2, ht1]


/-- **The or hop** (`tff` read rightward): `4` steps end at the or
verdict's redirect target, head three cells right (just past the tag), tape unchanged. -/
theorem run_certTrie_or_hop (hUP : RegionEmbeddedMulti U certTrie base redirect)
    {L : Nat}
    (hred0 : redirect 0 = none)
    (hred2 : redirect 2 = none)
    (hred5 : redirect 5 = none)
    {nxt : Nat} (hredV : redirect 10 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 3 < U.toPhased.toTM.tapeLength L)
    (hb0 : c0.tape c0.head = true)
    (hb1 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false)
    (hb2 : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 4).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 4).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 4).tape = c0.tape := by
  rw [show (4 : Nat) = ((1 + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_add, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  obtain ⟨hp1, hh1, ht1⟩ := certTrie_read_step hUP c0 0 1 2 (by omega) hred0
    (fun b => by cases b <;> simp [certTrie]) hphase (by omega)
  rw [← hc1, hb0] at hp1
  rw [← hc1] at hh1 ht1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = false := by
    rw [ht1]; exact hb1 c1.head (by omega)
  obtain ⟨hp2, hh2, ht2⟩ := certTrie_read_step hUP c1 2 5 11 (by omega) hred2
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp1) (by omega)
  rw [← hc2, hbit1] at hp2
  rw [← hc2] at hh2 ht2
  set c3 := TM.stepConfig (M := U.toPhased.toTM) c2 with hc3
  have hbit2 : c2.tape c2.head = false := by
    rw [ht2, ht1]; exact hb2 c2.head (by omega)
  obtain ⟨hp3, hh3, ht3⟩ := certTrie_read_step hUP c2 5 10 11 (by omega) hred5
    (fun b => by cases b <;> simp [certTrie]) (by simpa using hp2) (by omega)
  rw [← hc3, hbit2] at hp3
  rw [← hc3] at hh3 ht3
  obtain ⟨hp4, hh4, ht4⟩ := certTrie_redirect_step hUP c3 10 (by omega) hredV
    (by simpa using hp3)
  refine ⟨hp4, ?_, ?_⟩
  · rw [hh4, hh3, hh2, hh1]
  · rw [ht4, ht3, ht2, ht1]

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
