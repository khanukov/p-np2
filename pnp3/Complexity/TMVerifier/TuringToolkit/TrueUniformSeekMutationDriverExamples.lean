import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriver

/-!
# Concrete T1b-C driver probes

These named proof values instantiate the loop driver, the success tail and
the three terminal cases at concrete requests, so that the driver surface is
demonstrably non-vacuous.  They are not evaluator tests, and they make no
acceptance, output or restoration claim: `successStart` and `oobStart` stay
idle semantic boundaries.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## The closed-form clock at small arguments -/

example : t1LoopSteps 0 = 0 := rfl
example : t1LoopSteps 1 = 37 := rfl
example : t1LoopSteps 2 = 90 := rfl
example : t1LoopSteps 3 = 159 := rfl

/-- The recurrence, spelled out at `m = 2`: `90 = 37 + (16 * 1 + 37)`. -/
example : t1LoopSteps 2 = t1LoopSteps 1 + (16 * 1 + 37) := t1LoopSteps_succ 1

/-! ## Success: the selected slot exists -/

/-- Three data cells and two unary index units: slot `2` is selected. -/
def t1bcSuccessRequest : T1Request := ⟨2, [true, false, true]⟩

/-- The loop driver walks the cursor from slot `0` to slot `2` in exactly
`t1LoopSteps 2 = 90` genuine steps. -/
def t1bcDriveToSlotTwo :=
  t1CS_loop_reach_exact t1bcSuccessRequest 2 (by decide) (by decide)
    true true rfl rfl

/-- The success tail from `Σ(2)`. -/
def t1bcSuccessTail :=
  t1CS_loop_success_tail_exact t1bcSuccessRequest true (by decide)

/-- The exact `TM.runConfig` success case from the real initial
configuration. -/
def t1bcSuccessFromInitial :=
  t1CS_runConfig_decide_success_exact t1bcSuccessRequest true rfl

/-- The same case under the genuine public clock. -/
def t1bcSuccessPublicClock :=
  t1CS_run_encoded_decide_success t1bcSuccessRequest true rfl

/-! ## Out of bounds with nonempty data -/

/-- Two data cells but three index units: the driver falls off at slot `1`. -/
def t1bcOobRequest : T1Request := ⟨3, [true, false]⟩

def t1bcOobFromInitial :=
  t1CS_runConfig_decide_oob_exact t1bcOobRequest false rfl (by decide) rfl

def t1bcOobPublicClock :=
  t1CS_run_encoded_decide_oob_nonempty t1bcOobRequest false rfl (by decide) rfl

/-! ## Out of bounds with empty data -/

def t1bcEmptyRequest : T1Request := ⟨2, []⟩

def t1bcEmptyOobFromInitial :=
  t1CS_runConfig_decide_oob_empty_exact t1bcEmptyRequest rfl

def t1bcEmptyOobPublicClock :=
  t1CS_run_encoded_decide_oob_empty t1bcEmptyRequest rfl

/-! ## The clock estimate is usable at concrete requests -/

def t1bcSuccessFitsClock := t1CS_decideTotal_le_clock t1bcSuccessRequest
def t1bcOobFitsClock := t1CS_decideTotal_le_clock t1bcOobRequest
def t1bcEmptyFitsClock := t1CS_decideTotal_le_clock t1bcEmptyRequest

end Pnp3.Internal.PsubsetPpoly.TM
