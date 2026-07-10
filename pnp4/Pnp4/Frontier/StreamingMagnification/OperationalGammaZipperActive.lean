import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperGlobal
import Mathlib.Tactic.Ring

/-!
# First-hit control theorem for the value-preserving gamma zipper

The exact endpoint theorem in `OperationalGammaZipperGlobal` says that the
canonical run is in `done` after `gammaBodyTime payload.length` steps.  This
module proves that this is the first visit to either absorbing terminal state:
at every strictly earlier time the control is neither `done` nor `reject`.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalGammaZipper

/-! ## Absorbing terminal controls -/

@[simp] theorem natStep_reject (head : Nat) (tape : Nat -> Bool) :
    natStep ⟨.reject, head, tape⟩ = ⟨.reject, head, tape⟩ := by
  simp [natStep, gammaZipper, moveNat]

@[simp] theorem natRun_done (head : Nat) (tape : Nat -> Bool)
    (steps : Nat) :
    natRun ⟨.done, head, tape⟩ steps = ⟨.done, head, tape⟩ := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [natRun_succ, ih]
      exact natStep_done head tape

@[simp] theorem natRun_reject (head : Nat) (tape : Nat -> Bool)
    (steps : Nat) :
    natRun ⟨.reject, head, tape⟩ steps = ⟨.reject, head, tape⟩ := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [natRun_succ, ih]
      exact natStep_reject head tape

theorem natRun_state_done {config : NatConfig}
    (hstate : config.state = .done) (steps : Nat) :
    (natRun config steps).state = .done := by
  rcases config with ⟨state, head, tape⟩
  change state = .done at hstate
  subst state
  simp

theorem natRun_state_reject {config : NatConfig}
    (hstate : config.state = .reject) (steps : Nat) :
    (natRun config steps).state = .reject := by
  rcases config with ⟨state, head, tape⟩
  change state = .reject at hstate
  subst state
  simp

/-! ## The exact penultimate successful configuration -/

/-- One step before a final canonical cycle halts, its control is the
successful final-marker branch, not a terminal control. -/
theorem natRun_canonicalCycle_penultimate (processed : List Bool)
    (current : Bool) (suffix : Nat -> Bool) :
    exists resultTape,
      natRun (canonicalCycleConfig 1 processed current [] suffix)
          (10 * processed.length + 6) =
        ⟨.forwardBlockStart true current, 2 * processed.length + 3,
          resultTape⟩ := by
  let sourceTape := framedTape (cycleFrame 1 processed []) suffix
  have hD : sourceTape 2 = true := by
    simpa [sourceTape] using framedCycle_delimiter 1 processed [] suffix
  have hnew : sourceTape 1 = false := by
    simpa [sourceTape] using
      framedCycle_new_zero 1 processed [] suffix (by omega)
  have hprobe : sourceTape 0 = true := by
    simpa [sourceTape] using framedCycle_sentinel 1 processed [] suffix
  have hpairs : RightPairsAt sourceTape 3 processed := by
    simpa [sourceTape] using framedCycle_rightPairs 1 processed [] suffix
  have hmarker : sourceTape (3 + 2 * processed.length) = true := by
    simpa [sourceTape] using framedCycle_marker 1 processed [] suffix
  obtain ⟨resultTape, hrun, _⟩ :=
    natRun_cycleToMarker true current 2 processed sourceTape (by omega) hD
      hnew hprobe hpairs (by simpa using hmarker)
  refine ⟨resultTape, ?_⟩
  convert hrun using 1 <;>
    simp [canonicalCycleConfig, sourceTape] <;> omega

/-- Composing every nonfinal cycle, but stopping one step before the final
cycle halts, always exposes the successful final-marker control. -/
theorem natRun_cycles_penultimate (processed unprocessed : List Bool)
    (current : Bool) (suffix : Nat -> Bool) :
    exists finalCurrent head resultTape,
      natRun
          (canonicalCycleConfig (unprocessed.length + 1) processed current
            unprocessed suffix)
          (cycleFinishTime processed.length unprocessed - 1) =
        ⟨.forwardBlockStart true finalCurrent, head, resultTape⟩ := by
  induction unprocessed generalizing processed current with
  | nil =>
      obtain ⟨resultTape, hrun⟩ :=
        natRun_canonicalCycle_penultimate processed current suffix
      refine ⟨current, 2 * processed.length + 3, resultTape, ?_⟩
      simpa [cycleFinishTime] using hrun
  | cons next rest ih =>
      have hcycle := natRun_canonicalCycle_nonfinal
        (rest.length + 2) processed rest current next suffix (by omega)
      have hcycle' :
          natRun
              (canonicalCycleConfig ((next :: rest).length + 1) processed
                current (next :: rest) suffix)
              (10 * processed.length + 8) =
            canonicalCycleConfig (rest.length + 1) (processed ++ [current])
              next rest suffix := by
        convert hcycle using 1 <;> simp <;> omega
      obtain ⟨finalCurrent, head, resultTape, hpenultimate⟩ :=
        ih (processed := processed ++ [current]) (current := next)
      have htailPositive :
          0 < cycleFinishTime (processed ++ [current]).length rest := by
        rw [cycleFinishTime_closed]
        omega
      have htime :
          cycleFinishTime processed.length (next :: rest) - 1 =
            (10 * processed.length + 8) +
              (cycleFinishTime (processed ++ [current]).length rest - 1) := by
        rw [cycleFinishTime]
        simp only [List.length_append, List.length_singleton]
        have htailPositive' :
            0 < cycleFinishTime (processed.length + 1) rest := by
          simpa only [List.length_append, List.length_singleton] using
            htailPositive
        omega
      refine ⟨finalCurrent, head, resultTape, ?_⟩
      rw [htime, natRun_add, hcycle', hpenultimate]

/-- For a nonempty payload, the scan-to-final run is still in the
successful final-marker control exactly one step before its endpoint. -/
theorem natRun_scanFirst_penultimate_nonempty (current : Bool)
    (rest : List Bool) (suffix : Nat -> Bool) :
    exists finalCurrent head resultTape,
      natRun
          ⟨.scanFirst, 1,
            framedTape (initialFrame (rest.length + 1) (current :: rest))
              suffix⟩
          (gammaBodyTime (rest.length + 1) - 1) =
        ⟨.forwardBlockStart true finalCurrent, head, resultTape⟩ := by
  obtain ⟨finalCurrent, head, resultTape, hcycles⟩ :=
    natRun_cycles_penultimate [] rest current suffix
  have htotal :
      gammaBodyTime (rest.length + 1) =
        (rest.length + 3) + cycleFinishTime 0 rest := by
    rw [cycleFinishTime_closed]
    simp [gammaBodyTime]
    ring
  have hcyclesPositive : 0 < cycleFinishTime 0 rest := by
    rw [cycleFinishTime_closed]
    omega
  have htime :
      gammaBodyTime (rest.length + 1) - 1 =
        (rest.length + 3) + (cycleFinishTime 0 rest - 1) := by
    omega
  refine ⟨finalCurrent, head, resultTape, ?_⟩
  rw [htime, natRun_add, natRun_scanFirst_to_firstCycle]
  simpa only [List.length_nil] using hcycles

theorem natRun_scanFirst_penultimate_not_done (payload : List Bool)
    (suffix : Nat -> Bool) :
    (natRun
        ⟨.scanFirst, 1,
          framedTape (initialFrame payload.length payload) suffix⟩
        (gammaBodyTime payload.length - 1)).state ≠ .done := by
  cases payload with
  | nil => simp [gammaBodyTime, natRun]
  | cons current rest =>
      obtain ⟨finalCurrent, head, resultTape, hrun⟩ :=
        natRun_scanFirst_penultimate_nonempty current rest suffix
      have hrun' :
          natRun
              ⟨.scanFirst, 1,
                framedTape (initialFrame (current :: rest).length
                  (current :: rest)) suffix⟩
              (gammaBodyTime (current :: rest).length - 1) =
            ⟨.forwardBlockStart true finalCurrent, head, resultTape⟩ := by
        simpa only [List.length_cons] using hrun
      rw [hrun']
      simp

/-! ## First-hit theorem -/

/-- Before the exact quadratic endpoint, the canonical scan-first run has
visited neither absorbing terminal control. -/
theorem natRun_scanFirst_active (payload : List Bool)
    (suffix : Nat -> Bool) (elapsed : Nat)
    (helapsed : elapsed < gammaBodyTime payload.length) :
    let config :=
      natRun
        ⟨.scanFirst, 1,
          framedTape (initialFrame payload.length payload) suffix⟩ elapsed
    config.state ≠ .done ∧ config.state ≠ .reject := by
  dsimp only
  let initial : NatConfig :=
    ⟨.scanFirst, 1,
      framedTape (initialFrame payload.length payload) suffix⟩
  have hpositive : 0 < gammaBodyTime payload.length := by
    simp [gammaBodyTime]
  constructor
  · intro hdone
    have hpersist := natRun_state_done hdone
      (gammaBodyTime payload.length - 1 - elapsed)
    have htime :
        gammaBodyTime payload.length - 1 =
          elapsed + (gammaBodyTime payload.length - 1 - elapsed) := by
      omega
    have hpenultimate :=
      natRun_scanFirst_penultimate_not_done payload suffix
    apply hpenultimate
    rw [htime, natRun_add]
    exact hpersist
  · intro hreject
    have hpersist := natRun_state_reject hreject
      (gammaBodyTime payload.length - elapsed)
    have htime :
        gammaBodyTime payload.length =
          elapsed + (gammaBodyTime payload.length - elapsed) := by
      omega
    have hfinal := natRun_scanFirst_payload payload suffix
    have hfinalState := congrArg NatConfig.state hfinal
    rw [htime, natRun_add] at hfinalState
    rw [hpersist] at hfinalState
    simp [canonicalFinalConfig] at hfinalState

end OperationalGammaZipper
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_canonicalCycle_penultimate
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_cycles_penultimate
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_scanFirst_active
