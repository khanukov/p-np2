import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridgeExamples

/-!
# `ConstStatePhasedProgram` step-bridge surface tests

Compile-time probes that pin the public signatures of the generic
transition → `stepConfig` bridge and of its concrete one-phase probe.

Each check restates the exported signature and closes it by direct
reference, so any change to a public type — the shape of the opaque
transition hypothesis, the boundary premises of the move corollaries, or the
`Sigma` / `moveHead` / `Configuration.write` normal forms in the conclusion —
breaks this file.

The surface is deliberately narrow: one machine-independent bridge, five
move-specific corollaries (`left`, `left_clamped`, `right`, `right_clamped`,
`stay`), and a probe.  Nothing here claims acceptance, a runtime bound, or any
verifier property.
-/

namespace Pnp3.Tests.TMStepBridgeSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

variable {S : Type} [Fintype S] [DecidableEq S]

#check @Configuration.ext_of_components
#check @toTM_step_of_transition
#check @toTM_step_config_of_transition
#check @stepConfig_tape_of_transition
#check @stepBridgeProbeCS
#check @stepBridgeProbeCS_transition_true
#check @stepBridgeProbeCS_transition_false
#check @stepBridgeProbeCS_step_left
#check @stepBridgeProbeCS_step_left_clamped
#check @stepBridgeProbeCS_stepConfig_true
#check @Configuration.moveHead_left_clamp

/-- The complete bridge: an opaque transition fact yields the exact
`TM.stepConfig`, generically in `S`, the program, and the configuration. -/
theorem check_stepConfig_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    TM.stepConfig (M := U.toPhased.toTM) c =
      { state := (⟨phaseNext, localNext⟩ : U.toPhased.State)
        head := Configuration.moveHead (c := c) mv
        tape := c.write c.head w } :=
  stepConfig_of_transition U c htr

/-- Component surfaces: state, head, tape. -/
theorem check_stepConfig_state_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).state =
      (⟨phaseNext, localNext⟩ : U.toPhased.State) :=
  stepConfig_state_of_transition U c htr

theorem check_stepConfig_head_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).head =
      Configuration.moveHead (c := c) mv :=
  stepConfig_head_of_transition U c htr

theorem check_stepConfig_tape_apply_of_transition (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool} {mv : Move}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, mv))
    (i : Fin (U.toPhased.toTM.tapeLength n)) :
    (TM.stepConfig (M := U.toPhased.toTM) c).tape i =
      if (i : Nat) = (c.head : Nat) then w else c.tape i :=
  stepConfig_tape_apply_of_transition U c htr i

/-- `Move.right` corollary: exact `+1` head value under the in-bounds
premise, with the target tape given extensionally. -/
theorem check_stepConfig_eq_of_transition_right (U : ConstStatePhasedProgram S)
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
    TM.stepConfig (M := U.toPhased.toTM) c = c' :=
  stepConfig_eq_of_transition_right U c htr hb c' hstate hhead htape

/-- `Move.left` corollary: exact `-1` head value under the strictly-positive
head premise. -/
theorem check_stepConfig_eq_of_transition_left (U : ConstStatePhasedProgram S)
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
    TM.stepConfig (M := U.toPhased.toTM) c = c' :=
  stepConfig_eq_of_transition_left U c htr hpos c' hstate hhead htape

/-- `Move.left` at the left edge: the clamped regime, with the premise
complementary to `check_stepConfig_eq_of_transition_left`. -/
theorem check_stepConfig_eq_of_transition_left_clamped
    (U : ConstStatePhasedProgram S)
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
    TM.stepConfig (M := U.toPhased.toTM) c = c' :=
  stepConfig_eq_of_transition_left_clamped U c htr hzero c' hstate hhead htape

/-- The generic head-movement lemma the clamped `Move.left` corollary rests
on: at head `0` the move clamps, as a full `Fin` equality. -/
theorem check_moveHead_left_clamp {M : TM.{0}} {n : Nat}
    (c : Configuration (M := M) n) (h : (c.head : Nat) = 0) :
    Configuration.moveHead (c := c) Move.left = c.head :=
  Configuration.moveHead_left_clamp c h

/-- `Move.stay` corollary: unchanged head value, no boundary premise. -/
theorem check_stepConfig_eq_of_transition_stay (U : ConstStatePhasedProgram S)
    {n : Nat} (c : Configuration (M := U.toPhased.toTM) n)
    {phaseNext : Fin U.numPhases} {localNext : S} {w : Bool}
    (htr : U.transition c.state.fst c.state.snd (c.tape c.head) =
      (phaseNext, localNext, w, Move.stay))
    (c' : Configuration (M := U.toPhased.toTM) n)
    (hstate : c'.state = (⟨phaseNext, localNext⟩ : U.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat))
    (htape : ∀ i : Fin (U.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then w else c.tape i) :
    TM.stepConfig (M := U.toPhased.toTM) c = c' :=
  stepConfig_eq_of_transition_stay U c htr c' hstate hhead htape

/-- `Move.right` at the right edge: the clamped regime, with the premise
complementary to `check_stepConfig_eq_of_transition_right`. -/
theorem check_stepConfig_eq_of_transition_right_clamped
    (U : ConstStatePhasedProgram S)
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
    TM.stepConfig (M := U.toPhased.toTM) c = c' :=
  stepConfig_eq_of_transition_right_clamped U c htr hb c' hstate hhead htape

/-- The concrete one-phase probe still applies the bridge at its exported
signature. -/
theorem check_stepBridgeProbeCS_step_right {n : Nat}
    (c : Configuration (M := stepBridgeProbeCS.toPhased.toTM) n)
    (hscan : c.tape c.head = true)
    (hb : (c.head : Nat) + 1 < stepBridgeProbeCS.toPhased.toTM.tapeLength n)
    (c' : Configuration (M := stepBridgeProbeCS.toPhased.toTM) n)
    (hstate : c'.state =
      (⟨⟨0, Nat.zero_lt_one⟩, !c.state.snd⟩ :
        stepBridgeProbeCS.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat) + 1)
    (htape : ∀ i : Fin (stepBridgeProbeCS.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then true else c.tape i) :
    TM.stepConfig (M := stepBridgeProbeCS.toPhased.toTM) c = c' :=
  stepBridgeProbeCS_step_right c hscan hb c' hstate hhead htape

end Pnp3.Tests.TMStepBridgeSurface
