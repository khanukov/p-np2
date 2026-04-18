import Complexity.PsubsetPpolyInternal.TuringToolkit.CombineAtOffset

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM


/-! ## AndAtOffset: 2-input AND gate compound

Specialization of `CombineAtOffset.combineAtOffsetProgram` to the
boolean AND operation. -/

namespace AndAtOffset

open Pnp3.Internal.PsubsetPpoly.TM

/-- The AND-at-offset compound: reads bits at `head + Δ1` and `head + Δ2`,
writes their conjunction at `head + Δdst`, returns head to origin. -/
def andAtOffsetProgram (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) : PhasedProgram.{0} :=
  CombineAtOffset.combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d (· && ·)

@[simp] theorem andAtOffsetProgram_numPhases (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) :
    (andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).numPhases = 2 * Δdst + 4 := rfl

@[simp] theorem andAtOffsetProgram_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (n : Nat) :
    (andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).timeBound n = 2 * Δdst + 3 := rfl

/-- **Full correctness of `andAtOffsetProgram`**: after `2*Δdst + 3` steps,
head returns to its origin and the destination cell holds
`c.tape[head+Δ1] && c.tape[head+Δ2]`. -/
theorem andAtOffsetProgram_run_full (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) {n : Nat}
    (c : Configuration (M := (andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM) c
        (2 * Δdst + 3)
    ∃ (h_src1_bound : (c.head : ℕ) + Δ1 <
        (andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM.tapeLength n)
      (h_src2_bound : (c.head : ℕ) + Δ2 <
        (andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM.tapeLength n),
    cfinal.state.fst.val = 2 * Δdst + 3 ∧
    cfinal.state.snd = (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
                        c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩) ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
                    ((c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩) &&
                     (c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩)) :=
  CombineAtOffset.combineAtOffsetProgram_run_full Δ1 Δ2 Δdst hle12 hle2d (· && ·)
    c h_phase h_state_snd h_bound

end AndAtOffset

/-! ## OrAtOffset: 2-input OR gate compound

Specialization of `CombineAtOffset.combineAtOffsetProgram` to the
boolean OR operation. -/

namespace OrAtOffset

open Pnp3.Internal.PsubsetPpoly.TM

/-- The OR-at-offset compound: reads bits at `head + Δ1` and `head + Δ2`,
writes their disjunction at `head + Δdst`, returns head to origin. -/
def orAtOffsetProgram (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) : PhasedProgram.{0} :=
  CombineAtOffset.combineAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d (· || ·)

@[simp] theorem orAtOffsetProgram_numPhases (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) :
    (orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).numPhases = 2 * Δdst + 4 := rfl

@[simp] theorem orAtOffsetProgram_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (n : Nat) :
    (orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).timeBound n = 2 * Δdst + 3 := rfl

/-- **Full correctness of `orAtOffsetProgram`**: after `2*Δdst + 3` steps,
head returns to its origin and the destination cell holds
`c.tape[head+Δ1] || c.tape[head+Δ2]`. -/
theorem orAtOffsetProgram_run_full (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) {n : Nat}
    (c : Configuration (M := (orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM) c
        (2 * Δdst + 3)
    ∃ (h_src1_bound : (c.head : ℕ) + Δ1 <
        (orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM.tapeLength n)
      (h_src2_bound : (c.head : ℕ) + Δ2 <
        (orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d).toTM.tapeLength n),
    cfinal.state.fst.val = 2 * Δdst + 3 ∧
    cfinal.state.snd = (c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩,
                        c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩) ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
                    ((c.tape ⟨(c.head : ℕ) + Δ1, h_src1_bound⟩) ||
                     (c.tape ⟨(c.head : ℕ) + Δ2, h_src2_bound⟩)) :=
  CombineAtOffset.combineAtOffsetProgram_run_full Δ1 Δ2 Δdst hle12 hle2d (· || ·)
    c h_phase h_state_snd h_bound

end OrAtOffset

/-! ## NotSrcDstAtOffset: read-src, negate, write-dst compound

Specialization of `CombineAtOffset.combineAtOffsetProgram` with
`Δ1 = Δ2 = Δsrc` and `op a _ = !a`: reads the bit at `head + Δsrc`
(twice, inexpensively) and writes its negation at `head + Δdst`.

Used by the MCSP verifier for NOT-gates whose source and destination
slots differ. -/

namespace NotSrcDstAtOffset

open Pnp3.Internal.PsubsetPpoly.TM

/-- Read-src, negate, write-dst compound: reads bit at `head + Δsrc`
and writes its negation at `head + Δdst`. -/
def notSrcDstAtOffsetProgram (Δsrc Δdst : Nat) (hle : Δsrc ≤ Δdst) :
    PhasedProgram.{0} :=
  CombineAtOffset.combineAtOffsetProgram Δsrc Δsrc Δdst (le_refl Δsrc) hle
    (fun a _ => !a)

@[simp] theorem notSrcDstAtOffsetProgram_numPhases (Δsrc Δdst : Nat)
    (hle : Δsrc ≤ Δdst) :
    (notSrcDstAtOffsetProgram Δsrc Δdst hle).numPhases = 2 * Δdst + 4 := rfl

@[simp] theorem notSrcDstAtOffsetProgram_timeBound (Δsrc Δdst : Nat)
    (hle : Δsrc ≤ Δdst) (n : Nat) :
    (notSrcDstAtOffsetProgram Δsrc Δdst hle).timeBound n = 2 * Δdst + 3 := rfl

/-- **Full correctness**: after `2*Δdst + 3` steps head returns to origin and
the destination cell holds `!c.tape[head+Δsrc]`. -/
theorem notSrcDstAtOffsetProgram_run_full (Δsrc Δdst : Nat) (hle : Δsrc ≤ Δdst)
    {n : Nat}
    (c : Configuration (M := (notSrcDstAtOffsetProgram Δsrc Δdst hle).toTM) n)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (notSrcDstAtOffsetProgram Δsrc Δdst hle).toTM.tapeLength n) :
    let cfinal := TM.runConfig (M := (notSrcDstAtOffsetProgram Δsrc Δdst hle).toTM) c
        (2 * Δdst + 3)
    ∃ (h_src_bound : (c.head : ℕ) + Δsrc <
        (notSrcDstAtOffsetProgram Δsrc Δdst hle).toTM.tapeLength n),
    cfinal.state.fst.val = 2 * Δdst + 3 ∧
    cfinal.head = c.head ∧
    cfinal.tape = c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
                    (!(c.tape ⟨(c.head : ℕ) + Δsrc, h_src_bound⟩)) := by
  obtain ⟨h_src1_bound, _, h_phase_f, _, h_head_f, h_tape_f⟩ :=
    CombineAtOffset.combineAtOffsetProgram_run_full Δsrc Δsrc Δdst (le_refl Δsrc) hle
      (fun a _ => !a) c h_phase h_state_snd h_bound
  refine ⟨h_src1_bound, h_phase_f, h_head_f, ?_⟩
  exact h_tape_f

end NotSrcDstAtOffset

/-! ## GateEval: per-SLGate evaluator wrappers

Trivial specializations of the already-proven compound programs, indexed
by the SLGate constructors (input / const / notGate / andGate / orGate).
Each wrapper takes explicit tape-offsets describing where the source
and destination cells live.  The caller (circuit evaluator) is
responsible for picking offsets consistent with the tape layout
(input, scratch and row regions). -/

namespace GateEval

open Pnp3.Internal.PsubsetPpoly.TM

/-- Evaluator for `SLGate.input i`: copies `tape[head + Δrowbase + i]`
into `tape[head + Δdst]`.  Requires `Δrowbase + i ≤ Δdst`. -/
def gateInputProgram {n : Nat} (i : Fin n) (Δrowbase Δdst : Nat)
    (hle : Δrowbase + i.val ≤ Δdst) : PhasedProgram.{0} :=
  CopyAtOffset.copyAtOffsetProgram (Δrowbase + i.val) Δdst hle

@[simp] theorem gateInputProgram_timeBound {n : Nat} (i : Fin n)
    (Δrowbase Δdst : Nat) (hle : Δrowbase + i.val ≤ Δdst) (m : Nat) :
    (gateInputProgram i Δrowbase Δdst hle).timeBound m = 2 * Δdst + 2 := rfl

/-- Evaluator for `SLGate.const b`: writes `b` at `tape[head + Δdst]`. -/
def gateConstProgram (b : Bool) (Δdst : Nat) : PhasedProgram.{0} :=
  WriteAtOffset.writeAtOffsetProgram Δdst b

@[simp] theorem gateConstProgram_timeBound (b : Bool) (Δdst : Nat) (m : Nat) :
    (gateConstProgram b Δdst).timeBound m = 2 * Δdst + 1 := rfl

/-- Evaluator for `SLGate.notGate k`: reads `tape[head + Δsrc]`, writes its
negation at `tape[head + Δdst]`.  Requires `Δsrc ≤ Δdst`. -/
def gateNotProgram (Δsrc Δdst : Nat) (hle : Δsrc ≤ Δdst) : PhasedProgram.{0} :=
  NotSrcDstAtOffset.notSrcDstAtOffsetProgram Δsrc Δdst hle

@[simp] theorem gateNotProgram_timeBound (Δsrc Δdst : Nat)
    (hle : Δsrc ≤ Δdst) (m : Nat) :
    (gateNotProgram Δsrc Δdst hle).timeBound m = 2 * Δdst + 3 := rfl

/-- Evaluator for `SLGate.andGate k l`: reads `tape[head + Δ1]`,
`tape[head + Δ2]`, writes their conjunction at `tape[head + Δdst]`.
Requires `Δ1 ≤ Δ2 ≤ Δdst`. -/
def gateAndProgram (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) : PhasedProgram.{0} :=
  AndAtOffset.andAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d

@[simp] theorem gateAndProgram_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (m : Nat) :
    (gateAndProgram Δ1 Δ2 Δdst hle12 hle2d).timeBound m = 2 * Δdst + 3 := rfl

/-- Evaluator for `SLGate.orGate k l`: reads `tape[head + Δ1]`,
`tape[head + Δ2]`, writes their disjunction at `tape[head + Δdst]`.
Requires `Δ1 ≤ Δ2 ≤ Δdst`. -/
def gateOrProgram (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) : PhasedProgram.{0} :=
  OrAtOffset.orAtOffsetProgram Δ1 Δ2 Δdst hle12 hle2d

@[simp] theorem gateOrProgram_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (m : Nat) :
    (gateOrProgram Δ1 Δ2 Δdst hle12 hle2d).timeBound m = 2 * Δdst + 3 := rfl

/-- Uniform polynomial bound on the cost of evaluating a single gate:
`2*Δdst + 3` steps suffice regardless of constructor.  This is the
key lemma for the runtime bound of the circuit evaluator. -/
theorem gateAndProgram_timeBound_le_uniform (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (m : Nat) :
    (gateAndProgram Δ1 Δ2 Δdst hle12 hle2d).timeBound m ≤ 2 * Δdst + 3 := le_rfl

end GateEval

end TM

end PsubsetPpoly
end Internal
end Pnp3
