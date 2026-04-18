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

/-! ## `ConstStatePhasedProgram` variants of the gate evaluators

All concrete gate programs are definable as specializations of
`combineAtOffsetCS` with the appropriate boolean operator.  This gives
a single uniform `ConstStatePhasedProgram (Bool × Bool)` shape that
composes cleanly via `seq`.

- `.input i`     → read at `Δrowbase + i`, write at `Δdst`
                   (copy with op = fun a _ => a).
- `.const b`     → read-twice-write-b at `Δdst`
                   (op = fun _ _ => b).
- `.notGate`     → read at `Δsrc`, write `!` at `Δdst`
                   (op = fun a _ => !a).
- `.andGate`     → AND at `Δ1, Δ2 → Δdst`.
- `.orGate`      → OR at `Δ1, Δ2 → Δdst`.

Every wrapper has `numPhases = 2*Δdst + 4` and `timeBound = 2*Δdst + 3`,
independent of the op. -/

namespace GateEvalCS

open Pnp3.Internal.PsubsetPpoly.TM
open ConstStatePhasedProgram
open Encoding

/-- Evaluator for `SLGate.input i` (as ConstState): copies
`tape[head + Δrowbase + i]` into `tape[head + Δdst]`.  Built via
`combineAtOffsetCS` with `op = fun a _ => a` and a reflexive
Δsrc-chain. -/
def gateInputCS {n : Nat} (i : Fin n) (Δrowbase Δdst : Nat)
    (hle : Δrowbase + i.val ≤ Δdst) : ConstStatePhasedProgram (Bool × Bool) :=
  CombineAtOffset.combineAtOffsetCS (Δrowbase + i.val) (Δrowbase + i.val) Δdst
    (le_refl _) hle (fun a _ => a)

/-- Evaluator for `SLGate.const b` (as ConstState): writes `b` at
`tape[head + Δdst]`.  Built via `combineAtOffsetCS` with `op = fun _ _ => b`. -/
def gateConstCS (b : Bool) (Δdst : Nat) : ConstStatePhasedProgram (Bool × Bool) :=
  CombineAtOffset.combineAtOffsetCS Δdst Δdst Δdst (le_refl _) (le_refl _)
    (fun _ _ => b)

/-- Evaluator for `SLGate.notGate k` (as ConstState): reads
`tape[head + Δsrc]`, writes its negation at `tape[head + Δdst]`.
Built via `combineAtOffsetCS` with `op = fun a _ => !a`. -/
def gateNotCS (Δsrc Δdst : Nat) (hle : Δsrc ≤ Δdst) :
    ConstStatePhasedProgram (Bool × Bool) :=
  CombineAtOffset.combineAtOffsetCS Δsrc Δsrc Δdst (le_refl _) hle
    (fun a _ => !a)

/-- Evaluator for `SLGate.andGate k l` (as ConstState). -/
def gateAndCS (Δ1 Δ2 Δdst : Nat) (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) :
    ConstStatePhasedProgram (Bool × Bool) :=
  CombineAtOffset.combineAtOffsetCS Δ1 Δ2 Δdst hle12 hle2d (· && ·)

/-- Evaluator for `SLGate.orGate k l` (as ConstState). -/
def gateOrCS (Δ1 Δ2 Δdst : Nat) (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) :
    ConstStatePhasedProgram (Bool × Bool) :=
  CombineAtOffset.combineAtOffsetCS Δ1 Δ2 Δdst hle12 hle2d (· || ·)

/-! ### @[simp] timeBound / numPhases identities -/

@[simp] theorem gateInputCS_timeBound {n : Nat} (i : Fin n)
    (Δrowbase Δdst : Nat) (hle : Δrowbase + i.val ≤ Δdst) (m : Nat) :
    (gateInputCS i Δrowbase Δdst hle).timeBound m = 2 * Δdst + 3 := rfl

@[simp] theorem gateConstCS_timeBound (b : Bool) (Δdst : Nat) (m : Nat) :
    (gateConstCS b Δdst).timeBound m = 2 * Δdst + 3 := rfl

@[simp] theorem gateNotCS_timeBound (Δsrc Δdst : Nat) (hle : Δsrc ≤ Δdst)
    (m : Nat) :
    (gateNotCS Δsrc Δdst hle).timeBound m = 2 * Δdst + 3 := rfl

@[simp] theorem gateAndCS_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (m : Nat) :
    (gateAndCS Δ1 Δ2 Δdst hle12 hle2d).timeBound m = 2 * Δdst + 3 := rfl

@[simp] theorem gateOrCS_timeBound (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (m : Nat) :
    (gateOrCS Δ1 Δ2 Δdst hle12 hle2d).timeBound m = 2 * Δdst + 3 := rfl

/-- Uniform per-gate timeBound: every single-gate evaluator runs in
exactly `2*Δdst + 3` steps, regardless of gate type.  Used to bound
the total runtime of a circuit evaluator as `#gates * (2*Δdst + 3) + #boundaries`. -/
theorem gate_eval_uniform_timeBound_le (Δ1 Δ2 Δdst : Nat)
    (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst) (op : Bool → Bool → Bool) (m : Nat) :
    (CombineAtOffset.combineAtOffsetCS Δ1 Δ2 Δdst hle12 hle2d op).timeBound m ≤
      2 * Δdst + 3 := le_rfl

/-! ### Per-gate evaluator dispatcher

`evalOneGateCS g slot Δrowbase Δscratch hle` returns the
`ConstStatePhasedProgram (Bool × Bool)` that evaluates gate `g` whose
output is stored at scratch slot `slot`.  Invalid back-references
(out-of-range `.notGate`, `.andGate`, `.orGate` indices in a
malformed SL program) are clamped to `slot` so the result still type-
checks.  For well-formed SL programs, clamping is a no-op. -/


def evalOneGateCS {n : Nat} (g : SLGate n) (slot : Nat) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) :
    ConstStatePhasedProgram (Bool × Bool) :=
  match g with
  | .input i =>
    have hi : Δrowbase + i.val ≤ Δscratch + slot := by
      have := i.isLt; omega
    gateInputCS i Δrowbase (Δscratch + slot) hi
  | .const b => gateConstCS b (Δscratch + slot)
  | .notGate j =>
    let j' := min j slot
    have hj : Δscratch + j' ≤ Δscratch + slot := by
      have : j' ≤ slot := Nat.min_le_right _ _
      omega
    gateNotCS (Δscratch + j') (Δscratch + slot) hj
  | .andGate j l =>
    let a := min (min j l) slot
    let b := min (max j l) slot
    have h1 : Δscratch + a ≤ Δscratch + b := by
      show Δscratch + min (min j l) slot ≤ Δscratch + min (max j l) slot
      have hmm : min j l ≤ max j l := by
        rcases Nat.le_total j l with hjl | hjl
        · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
        · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
      omega
    have h2 : Δscratch + b ≤ Δscratch + slot := by
      show Δscratch + min (max j l) slot ≤ Δscratch + slot
      omega
    gateAndCS (Δscratch + a) (Δscratch + b) (Δscratch + slot) h1 h2
  | .orGate j l =>
    let a := min (min j l) slot
    let b := min (max j l) slot
    have h1 : Δscratch + a ≤ Δscratch + b := by
      show Δscratch + min (min j l) slot ≤ Δscratch + min (max j l) slot
      have hmm : min j l ≤ max j l := by
        rcases Nat.le_total j l with hjl | hjl
        · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
        · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
      omega
    have h2 : Δscratch + b ≤ Δscratch + slot := by
      show Δscratch + min (max j l) slot ≤ Δscratch + slot
      omega
    gateOrCS (Δscratch + a) (Δscratch + b) (Δscratch + slot) h1 h2

/-- Uniform timeBound: each gate evaluator runs in exactly
`2*(Δscratch + slot) + 3` steps. -/

theorem evalOneGateCS_timeBound {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) (m : Nat) :
    (evalOneGateCS g slot Δrowbase Δscratch hle).timeBound m =
      2 * (Δscratch + slot) + 3 := by
  cases g <;> rfl

/-! ### Whole-circuit evaluator

`circuitEvaluatorCS gates Δrowbase Δscratch hle` evaluates every gate
in `gates` in order, storing output of gate at index `i` into
`scratch[i]`.  Uses `seqList` over the per-gate evaluators. -/


def circuitEvaluatorCS {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    ConstStatePhasedProgram (Bool × Bool) :=
  ConstStatePhasedProgram.seqList
    ((gates.mapIdx (fun slot g => evalOneGateCS g slot Δrowbase Δscratch hle)))

/-- Generic seqList timeBound upper bound: if every program in `ps`
has `timeBound m ≤ B`, then the composed seqList's timeBound is at
most `ps.length * B + ps.length + 1 = ps.length * (B + 1) + 1`. -/
theorem seqList_timeBound_le_uniform {S : Type v}
    [Fintype S] [DecidableEq S] [Inhabited S]
    (ps : List (ConstStatePhasedProgram S)) (B : Nat) (m : Nat)
    (hB : ∀ p ∈ ps, p.timeBound m ≤ B) :
    (ConstStatePhasedProgram.seqList ps).timeBound m ≤
      ps.length * (B + 1) + 1 := by
  induction ps with
  | nil =>
    rw [ConstStatePhasedProgram.seqList_timeBound_nil]
    omega
  | cons p rest ih =>
    rw [ConstStatePhasedProgram.seqList_timeBound_cons]
    have hp : p.timeBound m ≤ B := hB p (by simp)
    have hrest : ∀ q ∈ rest, q.timeBound m ≤ B := fun q hq =>
      hB q (by simp [hq])
    have ih' := ih hrest
    have hlen : (p :: rest).length = rest.length + 1 := by rfl
    rw [hlen]
    have hexp : (rest.length + 1) * (B + 1) + 1 =
        rest.length * (B + 1) + (B + 1) + 1 := by
      simp [Nat.add_mul, Nat.one_mul]
    omega

end GateEvalCS

end TM

end PsubsetPpoly
end Internal
end Pnp3
