import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriver

/-!
# Concrete T1b-C driver probes

These named proof values instantiate the loop driver, the success tail and
the three exact terminal cases at concrete requests, so that the driver
surface is demonstrably non-vacuous.  Two of them — `index = 0` and the exact
`index = data.length` boundary — are stated as `theorem`s with the whole
configuration spelled out, so a weakened conclusion fails here.  They are not
evaluator tests, and they make no acceptance, output or restoration claim.
There are no public-clock probes any more: T1c-1 activated `successStart` and
`oobStart`, so the `t1CS_run_encoded_decide_*` theorems they instantiated no
longer exist.
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

/-- Degenerate nonempty success: index zero selects the first data cell. -/
def t1bcIndexZeroRequest : T1Request := ⟨0, [true]⟩

theorem t1bcIndexZeroSuccessFromInitial :
    TM.runConfig (M := T1M)
        (T1M.initialConfig (t1Point (encodeT1 t1bcIndexZeroRequest)))
        (t1DecideTotal t1bcIndexZeroRequest) =
      t1AlignedConfig (encodeT1 t1bcIndexZeroRequest).length 0
        (t1_lt_tapeLength _ _ (Nat.zero_le _))
        (t1ListTape
          ((t1LoopFrames t1bcIndexZeroRequest t1bcIndexZeroRequest.index).flatMap
            T1Frame.bits))
        .successStart .p0 false false false true :=
  t1CS_runConfig_decide_success_exact t1bcIndexZeroRequest true rfl

/-! ## Out of bounds with nonempty data -/

/-- Two data cells but three index units: the driver falls off at slot `1`. -/
def t1bcOobRequest : T1Request := ⟨3, [true, false]⟩

def t1bcOobFromInitial :=
  t1CS_runConfig_decide_oob_exact t1bcOobRequest false rfl (by decide) rfl

/-- Exact boundary OOB: the first missing slot is `index = data.length`. -/
def t1bcOobBoundaryRequest : T1Request := ⟨2, [true, false]⟩

theorem t1bcOobBoundaryFromInitial :
    TM.runConfig (M := T1M)
        (T1M.initialConfig (t1Point (encodeT1 t1bcOobBoundaryRequest)))
        (t1DecideTotal t1bcOobBoundaryRequest) =
      t1AlignedConfig (encodeT1 t1bcOobBoundaryRequest).length
        (4 * (t1bcOobBoundaryRequest.index +
          (t1bcOobBoundaryRequest.data.length - 1) + 3) + 3)
        (t1dOobHead_safe t1bcOobBoundaryRequest)
        (t1ListTape
          ((t1LoopFramesRestored t1bcOobBoundaryRequest
            (t1bcOobBoundaryRequest.data.length - 1)).flatMap T1Frame.bits))
        .oobStart .p0 false false false false :=
  t1CS_runConfig_decide_oob_exact t1bcOobBoundaryRequest false rfl
    (by decide) rfl

/-! ## Out of bounds with empty data -/

def t1bcEmptyRequest : T1Request := ⟨2, []⟩

def t1bcEmptyOobFromInitial :=
  t1CS_runConfig_decide_oob_empty_exact t1bcEmptyRequest rfl

/-! ## The clock estimate is usable at concrete requests -/

def t1bcSuccessFitsClock := t1CS_decideTotal_le_clock t1bcSuccessRequest
def t1bcOobFitsClock := t1CS_decideTotal_le_clock t1bcOobRequest
def t1bcEmptyFitsClock := t1CS_decideTotal_le_clock t1bcEmptyRequest

end Pnp3.Internal.PsubsetPpoly.TM
