import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridge

/-!
# Concrete probe for the `ConstStatePhasedProgram` step bridge

A deliberately tiny one-phase program, used only to show that the generic
bridge of `ConstStatePhasedStepBridge` actually compiles against a concrete
finite control, and that it does so **without unfolding the control table
inside the `stepConfig` proof**.

The discipline the probe pins down is the one T1b needs:

1. the control table is unfolded exactly once, in a standalone `rfl` lemma
   (`stepBridgeProbeCS_transition_*`), whose statement is a plain tuple
   equation;
2. every `TM.stepConfig` fact is then obtained by *applying* a bridge
   corollary to that lemma — the proof terms below contain no `simp`, no
   `decide`, and no reference to `stepBridgeProbeCS`'s definition, so no
   branch of the control table is ever reduced during the step proof.

The probe makes no acceptance, runtime, or verifier claim; it is a
compilation and API-shape witness only.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

/-- One-phase probe control with `S := Bool`.

On a scanned `true` it flips the local bit, writes `true` and moves right;
on a scanned `false` it keeps the local bit, writes `false` and moves left.
Both branches stay in the single phase `0`. -/
def stepBridgeProbeCS : ConstStatePhasedProgram Bool where
  numPhases := 1
  startPhase := ⟨0, Nat.zero_lt_one⟩
  startState := false
  acceptPhase := ⟨0, Nat.zero_lt_one⟩
  acceptState := true
  transition := fun _ q scan =>
    if scan then (⟨0, Nat.zero_lt_one⟩, !q, true, Move.right)
    else (⟨0, Nat.zero_lt_one⟩, q, false, Move.left)
  timeBound := fun n => n + 1

/-- The only place the probe's control table is unfolded: scanned bit
`true`. -/
theorem stepBridgeProbeCS_transition_true
    (i : Fin stepBridgeProbeCS.numPhases) (q : Bool) :
    stepBridgeProbeCS.transition i q true =
      (⟨0, Nat.zero_lt_one⟩, !q, true, Move.right) := rfl

/-- The only place the probe's control table is unfolded: scanned bit
`false`. -/
theorem stepBridgeProbeCS_transition_false
    (i : Fin stepBridgeProbeCS.numPhases) (q : Bool) :
    stepBridgeProbeCS.transition i q false =
      (⟨0, Nat.zero_lt_one⟩, q, false, Move.left) := rfl

/-- Probe of `stepConfig_eq_of_transition_right`: on a scanned `true`, one
step lands exactly on any caller-supplied configuration whose state, head
value and tape agree with the three premises.

The proof is a single application of the bridge to the table lemma; the
control table is not reduced here. -/
theorem stepBridgeProbeCS_step_right {n : Nat}
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
  stepConfig_eq_of_transition_right stepBridgeProbeCS c
    (by rw [hscan]; exact stepBridgeProbeCS_transition_true c.state.fst c.state.snd)
    hb c' hstate hhead htape

/-- Probe of `stepConfig_eq_of_transition_left`: on a scanned `false` at a
strictly positive head position, one step moves the head back by one and
writes `false`. -/
theorem stepBridgeProbeCS_step_left {n : Nat}
    (c : Configuration (M := stepBridgeProbeCS.toPhased.toTM) n)
    (hscan : c.tape c.head = false)
    (hpos : 0 < (c.head : Nat))
    (c' : Configuration (M := stepBridgeProbeCS.toPhased.toTM) n)
    (hstate : c'.state =
      (⟨⟨0, Nat.zero_lt_one⟩, c.state.snd⟩ :
        stepBridgeProbeCS.toPhased.State))
    (hhead : (c'.head : Nat) = (c.head : Nat) - 1)
    (htape : ∀ i : Fin (stepBridgeProbeCS.toPhased.toTM.tapeLength n),
      c'.tape i = if (i : Nat) = (c.head : Nat) then false else c.tape i) :
    TM.stepConfig (M := stepBridgeProbeCS.toPhased.toTM) c = c' :=
  stepConfig_eq_of_transition_left stepBridgeProbeCS c
    (by rw [hscan]; exact stepBridgeProbeCS_transition_false c.state.fst c.state.snd)
    hpos c' hstate hhead htape

/-- Probe of the raw complete bridge `stepConfig_of_transition`: the canonical
normal form (`Sigma` state, `moveHead`, `Configuration.write`) is available
for the probe too, again with no table reduction in the proof. -/
theorem stepBridgeProbeCS_stepConfig_true {n : Nat}
    (c : Configuration (M := stepBridgeProbeCS.toPhased.toTM) n)
    (hscan : c.tape c.head = true) :
    TM.stepConfig (M := stepBridgeProbeCS.toPhased.toTM) c =
      { state := (⟨⟨0, Nat.zero_lt_one⟩, !c.state.snd⟩ :
          stepBridgeProbeCS.toPhased.State)
        head := Configuration.moveHead (c := c) Move.right
        tape := c.write c.head true } :=
  stepConfig_of_transition stepBridgeProbeCS c
    (by rw [hscan]; exact stepBridgeProbeCS_transition_true c.state.fst c.state.snd)

end ConstStatePhasedProgram

end TM
end PsubsetPpoly
end Internal
end Pnp3
