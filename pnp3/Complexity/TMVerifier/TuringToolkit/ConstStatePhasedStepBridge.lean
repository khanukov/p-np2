import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

/-!
# Generic `ConstStatePhasedProgram` transition → `stepConfig` bridge

Every concrete `ConstStatePhasedProgram` built in `TuringToolkit` eventually
has to answer the same question: *given that the finite control's transition
table returns `(phaseNext, localNext, write, move)` on the current
`(phase, local, scan)` triple, what is `TM.stepConfig` of the compiled machine
`P.toPhased.toTM`?*

Answering it inline forces `simp`/`whnf` through the program's own
`transition` definition.  For a control table with many branches that is both
slow and fragile: the `match` on the local state is reduced *before* the
transition hypothesis can fire, so the proof pays for every branch even though
exactly one of them is relevant.

This module answers the question **once**, generically in `S`, `P` and `c`.
The transition appears only as the opaque applied term
`P.transition c.state.fst c.state.snd (c.tape c.head)`, discharged by a
hypothesis; nothing in these proofs ever unfolds a concrete `transition`.
Consumers supply that hypothesis by whatever means is cheapest for their
program (`rfl`, `decide`, or a dedicated table lemma) and then get an exact,
complete `TM.stepConfig` equality for free.

Layering (every exported declaration of this module, in dependency order):

* `toTM_step_of_transition` — the compiled `TM.step` equation;
* `toTM_step_config_of_transition` — the same equation instantiated at a
  configuration's own state and scanned bit;
* `stepConfig_state_of_transition` / `_head_` / `_tape_` — the three
  components, each stated in the canonical `Sigma` / `moveHead` /
  `Configuration.write` normal form;
* `stepConfig_tape_apply_of_transition` — the pointwise form of the tape
  component, with `Configuration.write`'s `dite` resolved to a `Nat` test;
* `stepConfig_of_transition` — the complete configuration equality;
* `stepConfig_eq_of_transition_left` / `_left_clamped` / `_right` /
  `_right_clamped` / `_stay` — ergonomic corollaries that identify
  `stepConfig c` with a *caller-supplied* target configuration `c'`, given the
  head-value equation under the exact boundary premise and a pointwise
  (extensional) description of the target tape.  The two `left` and the two
  `right` corollaries have pairwise complementary boundary premises, so the
  five together cover every move at every head position.

The corollaries are the intended entry point: they let a caller keep its own
aligned-configuration constructor on the right-hand side and discharge the
match with three value-level equations, never touching `Configuration.write`
or `Configuration.moveHead` normal forms.

The three `stepConfig_*` component lemmas of `Foundation` are reused verbatim,
as are its head-movement micro-API (`moveHead_right_lt`,
`moveHead_right_clamp`, `moveHead_left_val_of_pos`, `moveHead_left_clamp`,
`moveHead_stay`) and its componentwise extensionality lemma
`Configuration.ext_of_components`; all of those are generic in the machine and
live in `Foundation`, so a consumer needs no step-bridge import to use them.
No new axioms, no placeholders, and no program-specific imports.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

universe v

namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

variable {S : Type v} [Fintype S] [DecidableEq S]

/-! ### The compiled step equation

`toTM_step_of_transition` is the single place where the compilation
`ConstStatePhasedProgram → PhasedProgram → TM` is unwound.  Everything below
is a corollary of it, so no later proof re-enters `toPhased` or `toTM`. -/

/-- The compiled machine's `step`, read off an opaque transition-table fact.

The hypothesis mentions `U.transition` only as an applied term, so the proof
never reduces a concrete control table: `show` puts the goal into the
definitional normal form of `PhasedProgram.toTM`, and `htr` rewrites the
single remaining occurrence. -/
theorem toTM_step_of_transition (U : ConstStatePhasedProgram S)
    (i : Fin U.numPhases) (q : S) (scan : Bool)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition i q scan = (phaseNext, localNext, w, mv)) :
    U.toPhased.toTM.step (⟨i, q⟩ : U.toPhased.State) scan =
      ((⟨phaseNext, localNext⟩ : U.toPhased.State), w, mv) := by
  show ((⟨(U.transition i q scan).fst,
          (U.transition i q scan).snd.fst⟩ : U.toPhased.State),
        (U.transition i q scan).snd.snd.fst,
        (U.transition i q scan).snd.snd.snd) = _
  -- Generalising the (opaque) transition result before substituting `htr`
  -- keeps the dependent `Sigma` position out of a rewrite motive.
  revert htr
  generalize U.transition i q scan = r
  rintro rfl
  rfl

/-- Configuration-level form of `toTM_step_of_transition`: the machine's step
at the configuration's own state and scanned bit. -/
theorem toTM_step_config_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    U.toPhased.toTM.step c.state (c.tape c.head) =
      ((⟨phaseNext, localNext⟩ : U.toPhased.State), w, mv) :=
  toTM_step_of_transition U c.state.fst c.state.snd (c.tape c.head) htr

/-! ### The three components of `stepConfig`

Each lemma is `Foundation`'s definitional `stepConfig_*` equation followed by
the step equation above.  They are stated in the canonical normal forms:
the state as an explicit `Sigma`, the head as `Configuration.moveHead`, and
the tape as `Configuration.write`. -/

/-- New control state after one step: the `Sigma` pair named by the
transition. -/
theorem stepConfig_state_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).state =
      (⟨phaseNext, localNext⟩ : U.toPhased.State) := by
  rw [stepConfig_state, toTM_step_config_of_transition U c htr]

/-- New head position after one step: `moveHead` under the transition's
move. -/
theorem stepConfig_head_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).head =
      Configuration.moveHead (c := c) mv := by
  rw [stepConfig_head, toTM_step_config_of_transition U c htr]

/-- New tape after one step: the old tape with the transition's bit written
at the old head position. -/
theorem stepConfig_tape_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).tape = c.write c.head w := by
  rw [stepConfig_tape, toTM_step_config_of_transition U c htr]

/-- Pointwise form of `stepConfig_tape_of_transition`, with the `dite` of
`Configuration.write` already resolved into a `Nat`-level test.  This is the
shape callers with an explicit tape-update function need. -/
theorem stepConfig_tape_apply_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv))
    (i : Fin (U.toPhased.toTM.tapeLength n)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).tape i =
      if (i : Nat) = (c.head : Nat) then w else c.tape i := by
  rw [stepConfig_tape_of_transition U c htr]
  simp [Configuration.write, Fin.ext_iff]

/-! ### The complete `stepConfig` equality -/

/-- **The bridge.**  One `TM.stepConfig` of a compiled
`ConstStatePhasedProgram`, in full, from an opaque transition-table fact.

All three fields are pinned exactly: the `Sigma`-encoded next state, the
`Configuration.moveHead` of the transition's move, and the
`Configuration.write` of the transition's bit at the old head. -/
theorem stepConfig_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    TM.stepConfig (M := U.toPhased.toTM) c =
      { state := (⟨phaseNext, localNext⟩ : U.toPhased.State)
        head := Configuration.moveHead (c := c) mv
        tape := c.write c.head w } :=
  Configuration.ext_of_components
    (stepConfig_state_of_transition U c htr)
    (stepConfig_head_of_transition U c htr)
    (stepConfig_tape_of_transition U c htr)

/-! ### Ergonomic move-specific corollaries

These identify `stepConfig c` with a **caller-supplied** configuration `c'`.
The caller keeps its own aligned-configuration constructor on the right and
only has to supply

* the next control state,
* the head *value* equation (under the exact boundary premise for the move),
* a pointwise description of the target tape.

No `Configuration.write` or `Configuration.moveHead` ever appears in the
premises, and the concrete `transition` is still never unfolded. -/

/-- `Move.right` step, at a head position that is not at the right edge:
the head value advances by exactly one. -/
theorem stepConfig_eq_of_transition_right (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, Move.right))
    (hb : (c.head : Nat) + 1 < U.toPhased.toTM.tapeLength n)
    (c' : Configuration (M := U.toPhased.toTM) n)
    (hstate : c'.state = (⟨phaseNext, localNext⟩ : U.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat) + 1)
    (htape : ∀ i : Fin (U.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then w else c.tape i) :
    TM.stepConfig (M := U.toPhased.toTM) c = c' := by
  refine Configuration.ext_of_components ?_ ?_ ?_
  · rw [stepConfig_state_of_transition U c htr, hstate]
  · apply Fin.ext
    rw [stepConfig_head_of_transition U c htr,
      Configuration.moveHead_right_lt (c := c) hb, hhead]
  · funext i
    rw [stepConfig_tape_apply_of_transition U c htr i, htape i]

/-- `Move.left` step, at a strictly positive head position: the head value
decreases by exactly one. -/
theorem stepConfig_eq_of_transition_left (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, Move.left))
    (hpos : 0 < (c.head : Nat))
    (c' : Configuration (M := U.toPhased.toTM) n)
    (hstate : c'.state = (⟨phaseNext, localNext⟩ : U.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat) - 1)
    (htape : ∀ i : Fin (U.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then w else c.tape i) :
    TM.stepConfig (M := U.toPhased.toTM) c = c' := by
  refine Configuration.ext_of_components ?_ ?_ ?_
  · rw [stepConfig_state_of_transition U c htr, hstate]
  · apply Fin.ext
    rw [stepConfig_head_of_transition U c htr,
      Configuration.moveHead_left_val_of_pos (c := c) hpos, hhead]
  · funext i
    rw [stepConfig_tape_apply_of_transition U c htr i, htape i]

/-- `Move.stay` step: the head value is unchanged.  No boundary premise is
needed. -/
theorem stepConfig_eq_of_transition_stay (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, Move.stay))
    (c' : Configuration (M := U.toPhased.toTM) n)
    (hstate : c'.state = (⟨phaseNext, localNext⟩ : U.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat))
    (htape : ∀ i : Fin (U.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then w else c.tape i) :
    TM.stepConfig (M := U.toPhased.toTM) c = c' := by
  refine Configuration.ext_of_components ?_ ?_ ?_
  · rw [stepConfig_state_of_transition U c htr, hstate]
  · apply Fin.ext
    rw [stepConfig_head_of_transition U c htr,
      Configuration.moveHead_stay (c := c), hhead]
  · funext i
    rw [stepConfig_tape_apply_of_transition U c htr i, htape i]

/-- `Move.left` step at the left edge of the tape: the move clamps and the
head does not change.  The premise `(c.head : Nat) = 0` is exactly
complementary to `stepConfig_eq_of_transition_left`'s `0 < (c.head : Nat)`,
so together the two corollaries cover every `Move.left` step. -/
theorem stepConfig_eq_of_transition_left_clamped (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, Move.left))
    (hzero : (c.head : Nat) = 0)
    (c' : Configuration (M := U.toPhased.toTM) n)
    (hstate : c'.state = (⟨phaseNext, localNext⟩ : U.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat))
    (htape : ∀ i : Fin (U.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then w else c.tape i) :
    TM.stepConfig (M := U.toPhased.toTM) c = c' := by
  refine Configuration.ext_of_components ?_ ?_ ?_
  · rw [stepConfig_state_of_transition U c htr, hstate]
  · apply Fin.ext
    rw [stepConfig_head_of_transition U c htr,
      Configuration.moveHead_left_clamp (c := c) hzero, hhead]
  · funext i
    rw [stepConfig_tape_apply_of_transition U c htr i, htape i]

/-- `Move.right` step at the right edge of the tape: the move clamps and the
head does not change.  Stated separately so that callers never have to guess
which regime they are in — the two `Move.right` corollaries have
complementary premises. -/
theorem stepConfig_eq_of_transition_right_clamped (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, Move.right))
    (hb : ¬ ((c.head : Nat) + 1 < U.toPhased.toTM.tapeLength n))
    (c' : Configuration (M := U.toPhased.toTM) n)
    (hstate : c'.state = (⟨phaseNext, localNext⟩ : U.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat))
    (htape : ∀ i : Fin (U.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then w else c.tape i) :
    TM.stepConfig (M := U.toPhased.toTM) c = c' := by
  refine Configuration.ext_of_components ?_ ?_ ?_
  · rw [stepConfig_state_of_transition U c htr, hstate]
  · apply Fin.ext
    rw [stepConfig_head_of_transition U c htr,
      Configuration.moveHead_right_clamp (c := c) hb, hhead]
  · funext i
    rw [stepConfig_tape_apply_of_transition U c htr i, htape i]

end ConstStatePhasedProgram

end TM
end PsubsetPpoly
end Internal
end Pnp3
