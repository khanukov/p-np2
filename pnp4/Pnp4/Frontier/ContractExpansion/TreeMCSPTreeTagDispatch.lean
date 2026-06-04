import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
-- `BoundedLoopProgram` supplies the `ConstStatePhasedProgram.toTM_stepConfig_{phase,head,tape}` lemmas
-- used throughout (referenced via the `ConstStatePhasedProgram.` namespace, so the module name does not
-- appear literally below).

/-!
# CircuitTree 3-bit tag dispatcher (NP-verifier track — D2 transcoder, parser entry layer)

The on-tape transcoder (`TM_VERIFIER_STRATEGY.md` §9, §11) must read the **witness** — a recursive
`CircuitTree` serialised by `encodeCircuitTree` (`Encoding.lean`) with **3-bit binary tags**:

```
input  = [false,false,false] ++ encodeFin width i      not = [false,true ,false] ++ ‹sub›
const  = [false,false,true ] ++ [b]                    and = [false,true ,true ] ++ ‹sub1›‹sub2›
                                                        or  = [true ,false,false] ++ ‹sub1›‹sub2›
```

This brick is the transcoder's **parser entry**: a `ConstStatePhasedProgram Unit` that reads the 3 tag
bits off the tape — a depth-3 **binary trie** in finite control — and dispatches to a per-tag phase
(`input/const/not/and/or`), routing the three undefined tag codes `101/110/111` to a reject sink. It is
the binary-tag analogue of D1b's unary `gateTagDispatch`, and like it the dispatch phases are *internal
entrypoints* for the per-tag continuations (read a binary index / read a literal / recurse into
subtrees), reached by phase-routing within one program (not by `seq`).

It is **scratch-free** (reads 3 fixed cells, never writes), so it is completable on its own; the
scratch-arithmetic parts of the transcoder (the binary→unary index conversion and the preorder→postorder
**tape stack**) are the documented follow-up sub-bricks (§11).

Phase layout (`numPhases = 12`), reading bits `b0 b1 b2` left-to-right (head advancing right):
`0` reads `b0`; `1` (prefix `0`), `2` (prefix `1`) read `b1`; `3` (`00`), `4` (`01`), `5` (`10`) read
`b2`; accept phases `6`=input, `7`=const, `8`=not, `9`=and, `10`=or; `11` = reject sink (codes
`101/110/111`). After the valid 3-bit tag the dispatcher lands in `6..10`, head advanced by `3`, tape
unchanged.

**Composition note (the nominal `acceptPhase`; `TM.accepts` is NOT this dispatcher's API).** Per the
repo's all-`Unit` state-uniformity discipline (§6a), control is **phase-encoded**, not state-carried, and
a 5-way tag branch cannot be `seq`-composed (`ConstStatePhasedProgram.seq` hands off at one `acceptPhase`
and resets the state). So — exactly as in D1b's `gateTagDispatch` — the five dispatch phases `6..10` are
**internal entrypoints** for the per-tag continuations (read a binary index / a literal / recurse),
reached by phase-routing **within one program**, not by `seq`. The structure's single `acceptPhase` is
therefore a **nominal placeholder** set to the reject sink `11`; consequently the compiled
`treeTagDispatch.toPhased.toTM` has `TM.accepts ↔ reached phase 11` (a *malformed*-tag halt), which is
**not** a "valid tag recognised" predicate. Downstream code must use the dispatcher's real API — the
`runConfig` phase-position lemmas below (`treeTagDispatch_runConfig_{input,const,not,and,or}` land in
`6..10`; `_malformed` lands in `11`) — and must **not** read `TM.accepts (treeTagDispatch.toPhased.toTM)`
as tag recognition.

**Progress classification (AGENTS.md): Infrastructure** — toolkit toward the NP-membership leg of
`VerifiedNPDAGLowerBoundSource`; it builds no verifier and proves no separation. All surfaces carry only
the standard `[propext, Classical.choice, Quot.sound]`.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- The dispatcher's phase-routing function, as a pure `Nat → Bool → Nat` (the `.val` of the transition's
next phase at a reading phase). Lets the per-tag run lemmas compute the landing phase by reduction. -/
def treeTagDispatchNext (iv : Nat) (b : Bool) : Nat :=
  if iv = 0 then (if b then 2 else 1)
  else if iv = 1 then (if b then 4 else 3)
  else if iv = 2 then (if b then 11 else 5)
  else if iv = 3 then (if b then 7 else 6)
  else if iv = 4 then (if b then 9 else 8)
  else if iv = 5 then (if b then 11 else 10)
  else iv

/-- CircuitTree 3-bit tag dispatcher: a depth-3 binary trie in finite control. -/
def treeTagDispatch : ConstStatePhasedProgram Unit where
  numPhases := 12
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨11, by omega⟩  -- nominal placeholder = reject sink; see the composition note above:
                                  -- `TM.accepts` is NOT tag recognition — the API is the runConfig lemmas
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then ((if b then ⟨2, by omega⟩ else ⟨1, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 1 then ((if b then ⟨4, by omega⟩ else ⟨3, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 2 then ((if b then ⟨11, by omega⟩ else ⟨5, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 3 then ((if b then ⟨7, by omega⟩ else ⟨6, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 4 then ((if b then ⟨9, by omega⟩ else ⟨8, by omega⟩ : Fin 12), (), b, Move.right)
    else if i.val = 5 then ((if b then ⟨11, by omega⟩ else ⟨10, by omega⟩ : Fin 12), (), b, Move.right)
    else (i, (), b, Move.stay)
  timeBound := fun _ => 3

@[simp] theorem treeTagDispatch_timeBound (n : Nat) : treeTagDispatch.timeBound n = 3 := rfl
@[simp] theorem treeTagDispatch_numPhases : treeTagDispatch.numPhases = 12 := rfl
@[simp] theorem treeTagDispatch_startPhase_val : (treeTagDispatch.startPhase : Nat) = 0 := rfl

/-- The dispatcher never moves the head left (it advances right while reading the tag, and idles
otherwise). -/
theorem treeTagDispatch_transition_move (i : Fin 12) (s : Unit) (b : Bool) :
    (treeTagDispatch.transition i s b).2.2.2 ≠ Move.left := by
  unfold treeTagDispatch
  dsimp only
  split_ifs <;> simp

theorem treeTagDispatch_neverMovesLeft : TMNeverMovesLeft (treeTagDispatch.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact treeTagDispatch_transition_move i s b

/-- Every step writes back the scanned bit, so the tape is unchanged. -/
theorem treeTagDispatch_transition_bit (i : Fin 12) (s : Unit) (b : Bool) :
    (treeTagDispatch.transition i s b).2.2.1 = b := by
  unfold treeTagDispatch
  dsimp only
  split_ifs <;> simp

theorem treeTagDispatch_stepConfig_tape {L : Nat}
    (c : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    {i : Fin 12} {s : Unit} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := treeTagDispatch.toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape treeTagDispatch c hstate,
    treeTagDispatch_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Single-step: one reading move

At any reading phase (`i.val < 6`) the dispatcher routes to `treeTagDispatchNext i.val b`, advances the
head one cell, and leaves the tape unchanged. The per-tag run lemmas compose three of these. -/
theorem treeTagDispatch_stepConfig_read {L : Nat}
    (c : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    {i : Fin 12} {s : Unit} (hi : i.val < 6) (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < treeTagDispatch.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := treeTagDispatch.toPhased.toTM) c).state).fst.val
        = treeTagDispatchNext i.val (c.tape c.head)
      ∧ ((TM.stepConfig (M := treeTagDispatch.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := treeTagDispatch.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase treeTagDispatch c hstate]
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 from by omega)
      with h | h | h | h | h | h <;>
      cases c.tape c.head <;>
      simp [treeTagDispatch, treeTagDispatchNext, h]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head treeTagDispatch c hstate]
    have hmove : (treeTagDispatch.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 from by omega)
        with h | h | h | h | h | h <;>
        cases c.tape c.head <;>
        simp [treeTagDispatch, h]
    rw [hmove]
    simp only [Configuration.moveHead, dif_pos hbound]
  · exact treeTagDispatch_stepConfig_tape c hstate

/-! ### Three-step dispatch (valid tags)

The reusable composition: from start phase `0`, three reading moves (when the first two land in reading
phases, i.e. the tag is not an early-reject `11_`) take the head past the 3 tag bits and land in
`treeTagDispatchNext³`. The five valid-tag corollaries instantiate the bits and reduce the landing phase. -/
theorem treeTagDispatch_runConfig_three {L : Nat}
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L) (b0 b1 b2 : Bool)
    (hphase : (c0.state.fst : Nat) = 0)
    (hp1 : treeTagDispatchNext 0 b0 < 6)
    (hp2 : treeTagDispatchNext (treeTagDispatchNext 0 b0) b1 < 6)
    (hb : (c0.head : Nat) + 3 < treeTagDispatch.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = b0)
    (h1 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = b1)
    (h2 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = b2) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat)
        = treeTagDispatchNext (treeTagDispatchNext (treeTagDispatchNext 0 b0) b1) b2
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  have e1 : TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1
      = TM.stepConfig (M := treeTagDispatch.toPhased.toTM) c0 := TM.runConfig_one c0
  have e2 : TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2
      = TM.stepConfig (M := treeTagDispatch.toPhased.toTM)
          (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1) := TM.runConfig_succ c0 1
  have e3 : TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3
      = TM.stepConfig (M := treeTagDispatch.toPhased.toTM)
          (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2) := TM.runConfig_succ c0 2
  -- Step 1 (phase 0, bit b0)
  obtain ⟨s1p, s1h, s1t⟩ := treeTagDispatch_stepConfig_read c0 (i := c0.state.fst) (s := c0.state.snd)
    (by rw [hphase]; omega) rfl (by omega)
  rw [hphase, h0 c0.head rfl] at s1p
  rw [← e1] at s1p s1h s1t
  -- Step 2 (phase `treeTagDispatchNext 0 b0`, bit b1)
  have hbit1 : (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).tape
      (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).head = b1 := by
    rw [s1t]; exact h1 _ s1h
  obtain ⟨s2p, s2h, s2t⟩ := treeTagDispatch_stepConfig_read
    (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1)
    (i := (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).state.fst)
    (s := (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).state.snd)
    (by rw [s1p]; exact hp1) rfl (by rw [s1h]; omega)
  rw [s1p, hbit1] at s2p
  rw [← e2] at s2p s2h s2t
  -- Step 3 (phase `treeTagDispatchNext (treeTagDispatchNext 0 b0) b1`, bit b2)
  have hbit2 : (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2).tape
      (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2).head = b2 := by
    rw [s2t, s1t]; exact h2 _ (by rw [s2h, s1h])
  obtain ⟨s3p, s3h, s3t⟩ := treeTagDispatch_stepConfig_read
    (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2)
    (i := (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2).state.fst)
    (s := (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2).state.snd)
    (by rw [s2p]; exact hp2) rfl (by rw [s2h, s1h]; omega)
  rw [s2p, hbit2] at s3p
  rw [← e3] at s3p s3h s3t
  refine ⟨s3p, ?_, ?_⟩
  · rw [s3h, s2h, s1h]
  · rw [s3t, s2t, s1t]

/-! ### Per-tag dispatch corollaries (the deliverable)

For each valid tag, the 3 tag bits drive the dispatcher to that tag's accept phase, head advanced by 3,
tape unchanged. The cell hypotheses are exactly `encodeCircuitTree`'s tag prefix for that constructor. -/

/-- `input` tag `000` ⇒ accept phase `6`. -/
theorem treeTagDispatch_runConfig_input {L : Nat}
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 3 < treeTagDispatch.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = false)
    (h1 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false)
    (h2 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 6
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hp, hh, ht⟩ := treeTagDispatch_runConfig_three c0 false false false hphase
    (by decide) (by decide) hb h0 h1 h2
  exact ⟨by rw [hp]; decide, hh, ht⟩

/-- `const` tag `001` ⇒ accept phase `7`. -/
theorem treeTagDispatch_runConfig_const {L : Nat}
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 3 < treeTagDispatch.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = false)
    (h1 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false)
    (h2 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = true) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 7
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hp, hh, ht⟩ := treeTagDispatch_runConfig_three c0 false false true hphase
    (by decide) (by decide) hb h0 h1 h2
  exact ⟨by rw [hp]; decide, hh, ht⟩

/-- `not` tag `010` ⇒ accept phase `8`. -/
theorem treeTagDispatch_runConfig_not {L : Nat}
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 3 < treeTagDispatch.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = false)
    (h1 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true)
    (h2 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 8
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hp, hh, ht⟩ := treeTagDispatch_runConfig_three c0 false true false hphase
    (by decide) (by decide) hb h0 h1 h2
  exact ⟨by rw [hp]; decide, hh, ht⟩

/-- `and` tag `011` ⇒ accept phase `9`. -/
theorem treeTagDispatch_runConfig_and {L : Nat}
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 3 < treeTagDispatch.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = false)
    (h1 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true)
    (h2 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = true) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 9
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hp, hh, ht⟩ := treeTagDispatch_runConfig_three c0 false true true hphase
    (by decide) (by decide) hb h0 h1 h2
  exact ⟨by rw [hp]; decide, hh, ht⟩

/-- `or` tag `100` ⇒ accept phase `10`. -/
theorem treeTagDispatch_runConfig_or {L : Nat}
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 3 < treeTagDispatch.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = true)
    (h1 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false)
    (h2 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 2 → c0.tape p = false) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 10
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hp, hh, ht⟩ := treeTagDispatch_runConfig_three c0 true false false hphase
    (by decide) (by decide) hb h0 h1 h2
  exact ⟨by rw [hp]; decide, hh, ht⟩

/-! ### Malformed-tag reject

The prefix `11` (tag codes `110`/`111`) routes to the reject sink `11` after two steps — the dispatcher
recognises the undefined codes. (Code `101` reaches the sink on the third step, covered by the `b0=true`
branch of `runConfig_three` landing in `11`.) -/
theorem treeTagDispatch_runConfig_malformed {L : Nat}
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 2 < treeTagDispatch.toPhased.toTM.tapeLength L)
    (h0 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) → c0.tape p = true)
    (h1 : ∀ p : Fin (treeTagDispatch.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2).state).fst : Nat) = 11 := by
  have e1 : TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1
      = TM.stepConfig (M := treeTagDispatch.toPhased.toTM) c0 := TM.runConfig_one c0
  have e2 : TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 2
      = TM.stepConfig (M := treeTagDispatch.toPhased.toTM)
          (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1) := TM.runConfig_succ c0 1
  obtain ⟨s1p, s1h, s1t⟩ := treeTagDispatch_stepConfig_read c0 (i := c0.state.fst) (s := c0.state.snd)
    (by rw [hphase]; omega) rfl (by omega)
  rw [hphase, h0 c0.head rfl] at s1p
  rw [← e1] at s1p s1h s1t
  have hbit1 : (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).tape
      (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).head = true := by
    rw [s1t]; exact h1 _ s1h
  obtain ⟨s2p, _, _⟩ := treeTagDispatch_stepConfig_read
    (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1)
    (i := (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).state.fst)
    (s := (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 1).state.snd)
    (by rw [s1p]; decide) rfl (by rw [s1h]; omega)
  rw [s1p, hbit1] at s2p
  rw [← e2] at s2p
  rw [s2p]; decide

end ContractExpansion
end Frontier
end Pnp4
