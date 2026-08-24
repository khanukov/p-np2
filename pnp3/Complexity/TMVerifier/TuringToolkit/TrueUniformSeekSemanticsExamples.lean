import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemantics

/-!
# Concrete T1c-3 canonical-semantics probes

Four named probes on the one fixed machine `t1CS`, each at a canonical
`encodeT1 r` input:

* **true bit** — the selected slot holds `true`: the machine accepts and the
  observable output cell reads `true`;
* **false bit** — the selected slot holds `false`: the machine still accepts
  (acceptance is *structural*, i.e. "the slot exists"), and the output cell
  reads `false`, so the payload is genuinely carried and not confused with the
  accept/reject decision;
* **nonempty out of bounds** — the index exceeds a nonempty data field: the
  machine rejects and the tape is restored to the input tape;
* **empty out of bounds** — no data field at all: the machine rejects and the
  tape was never written.

Nothing here is claimed for malformed or trailing-padded physical tapes; every
probe is a canonical `encodeT1` image (see the scope section of
`TrueUniformSeekSemantics`).
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## True-bit probe -/

/-- Slot `1` of `[false, true]` holds `true`. -/
def t1c3TrueRequest : T1Request := ⟨1, [false, true]⟩

def t1c3TrueRun :=
  t1CS_run_success_exact t1c3TrueRequest true rfl

/-- The output cell of the accepting run reads `true`. -/
def t1c3TrueOutput :=
  t1CS_run_output_at t1c3TrueRequest true rfl
    ⟨t1OutputPosition t1c3TrueRequest, by
      have := t1tOutputBase_safe t1c3TrueRequest
      simp only [t1OutputPosition_eq] at *
      omega⟩ rfl

theorem t1c3TrueAccepts :
    TM.accepts (M := T1M) (encodeT1 t1c3TrueRequest).length
      (t1Point (encodeT1 t1c3TrueRequest)) = true := by
  rw [t1CS_accepts_eq_isSome t1c3TrueRequest]
  rfl

/-! ## False-bit probe

The point of this probe: a `false` payload must **still accept**.  Acceptance
tracks slot existence, the output cell tracks the payload. -/

/-- Slot `0` of `[false, true]` holds `false`. -/
def t1c3FalseRequest : T1Request := ⟨0, [false, true]⟩

def t1c3FalseRun :=
  t1CS_run_success_exact t1c3FalseRequest false rfl

/-- The output cell of the accepting run reads `false`. -/
def t1c3FalseOutput :=
  t1CS_run_output_at t1c3FalseRequest false rfl
    ⟨t1OutputPosition t1c3FalseRequest, by
      have := t1tOutputBase_safe t1c3FalseRequest
      simp only [t1OutputPosition_eq] at *
      omega⟩ rfl

theorem t1c3FalseAccepts :
    TM.accepts (M := T1M) (encodeT1 t1c3FalseRequest).length
      (t1Point (encodeT1 t1c3FalseRequest)) = true := by
  rw [t1CS_accepts_eq_isSome t1c3FalseRequest]
  rfl

/-! ## Nonempty out-of-bounds probe -/

/-- Index `3` against two data cells. -/
def t1c3OobRequest : T1Request := ⟨3, [true, false]⟩

def t1c3OobRun :=
  t1CS_run_reject_exact t1c3OobRequest rfl

def t1c3OobTapePreserved :=
  t1CS_run_reject_tape_eq t1c3OobRequest rfl

theorem t1c3OobRejects :
    TM.accepts (M := T1M) (encodeT1 t1c3OobRequest).length
      (t1Point (encodeT1 t1c3OobRequest)) = false :=
  t1CS_run_reject_not_accepts t1c3OobRequest rfl

/-! ## Empty out-of-bounds probe -/

/-- Two index units and no data field at all. -/
def t1c3EmptyRequest : T1Request := ⟨2, []⟩

def t1c3EmptyRun :=
  t1CS_run_reject_exact t1c3EmptyRequest rfl

def t1c3EmptyTapePreserved :=
  t1CS_run_reject_tape_eq t1c3EmptyRequest rfl

theorem t1c3EmptyRejects :
    TM.accepts (M := T1M) (encodeT1 t1c3EmptyRequest).length
      (t1Point (encodeT1 t1c3EmptyRequest)) = false :=
  t1CS_run_reject_not_accepts t1c3EmptyRequest rfl

/-! ## Clock headroom on the probes -/

def t1c3TrueClockFits := t1CS_totalSteps_le_clock t1c3TrueRequest
def t1c3OobClockFits := t1CS_totalSteps_le_clock t1c3OobRequest
def t1c3EmptyClockFits := t1CS_totalSteps_le_clock t1c3EmptyRequest

end Pnp3.Internal.PsubsetPpoly.TM
