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

/-! ### Correctness of per-gate evaluators

Each gate-evaluator is a specialization of `combineAtOffsetCS` with a
specific operator.  Its correctness theorem is a direct corollary of
`CombineAtOffset.combineAtOffsetCS_run_full`. -/

/-- Correctness of `gateInputCS`: writes `tape[head + Δrowbase + i.val]`
at `tape[head + Δdst]`. -/
theorem gateInputCS_run_full {n : Nat} (i : Fin n) (Δrowbase Δdst : Nat)
    (hle : Δrowbase + i.val ≤ Δdst) {N : Nat}
    (c : Configuration (M := (gateInputCS i Δrowbase Δdst hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (gateInputCS i Δrowbase Δdst hle).toPhased.toTM.tapeLength N) :
    ∃ (h_src : (c.head : ℕ) + (Δrowbase + i.val) <
        (gateInputCS i Δrowbase Δdst hle).toPhased.toTM.tapeLength N),
    (TM.runConfig (M := (gateInputCS i Δrowbase Δdst hle).toPhased.toTM) c
        (2 * Δdst + 3)).tape =
      c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
        (c.tape ⟨(c.head : ℕ) + (Δrowbase + i.val), h_src⟩) := by
  obtain ⟨h1, _, _, _, _, ht⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full (Δrowbase + i.val) (Δrowbase + i.val) Δdst
      (le_refl _) hle (fun a _ => a) c h_phase h_state_snd h_bound
  exact ⟨h1, ht⟩

/-- Correctness of `gateConstCS`: writes `b` at `tape[head + Δdst]`. -/
theorem gateConstCS_run_full (b : Bool) (Δdst : Nat) {N : Nat}
    (c : Configuration (M := (gateConstCS b Δdst).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (gateConstCS b Δdst).toPhased.toTM.tapeLength N) :
    (TM.runConfig (M := (gateConstCS b Δdst).toPhased.toTM) c
        (2 * Δdst + 3)).tape =
      c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩ b := by
  obtain ⟨_, _, _, _, _, ht⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full Δdst Δdst Δdst (le_refl _) (le_refl _)
      (fun _ _ => b) c h_phase h_state_snd h_bound
  exact ht

/-- Correctness of `gateNotCS`. -/
theorem gateNotCS_run_full (Δsrc Δdst : Nat) (hle : Δsrc ≤ Δdst) {N : Nat}
    (c : Configuration (M := (gateNotCS Δsrc Δdst hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (gateNotCS Δsrc Δdst hle).toPhased.toTM.tapeLength N) :
    ∃ (h_src : (c.head : ℕ) + Δsrc <
        (gateNotCS Δsrc Δdst hle).toPhased.toTM.tapeLength N),
    (TM.runConfig (M := (gateNotCS Δsrc Δdst hle).toPhased.toTM) c
        (2 * Δdst + 3)).tape =
      c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
        (!(c.tape ⟨(c.head : ℕ) + Δsrc, h_src⟩)) := by
  obtain ⟨h1, _, _, _, _, ht⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full Δsrc Δsrc Δdst (le_refl _) hle
      (fun a _ => !a) c h_phase h_state_snd h_bound
  exact ⟨h1, ht⟩

/-- Correctness of `gateAndCS`. -/
theorem gateAndCS_run_full (Δ1 Δ2 Δdst : Nat) (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst)
    {N : Nat}
    (c : Configuration (M := (gateAndCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (gateAndCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM.tapeLength N) :
    ∃ (h_src1 : (c.head : ℕ) + Δ1 <
        (gateAndCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM.tapeLength N)
      (h_src2 : (c.head : ℕ) + Δ2 <
        (gateAndCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM.tapeLength N),
    (TM.runConfig (M := (gateAndCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM) c
        (2 * Δdst + 3)).tape =
      c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
        ((c.tape ⟨(c.head : ℕ) + Δ1, h_src1⟩) &&
         (c.tape ⟨(c.head : ℕ) + Δ2, h_src2⟩)) := by
  obtain ⟨h1, h2, _, _, _, ht⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full Δ1 Δ2 Δdst hle12 hle2d (· && ·)
      c h_phase h_state_snd h_bound
  exact ⟨h1, h2, ht⟩

/-- Correctness of `gateOrCS`. -/
theorem gateOrCS_run_full (Δ1 Δ2 Δdst : Nat) (hle12 : Δ1 ≤ Δ2) (hle2d : Δ2 ≤ Δdst)
    {N : Nat}
    (c : Configuration (M := (gateOrCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + Δdst <
        (gateOrCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM.tapeLength N) :
    ∃ (h_src1 : (c.head : ℕ) + Δ1 <
        (gateOrCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM.tapeLength N)
      (h_src2 : (c.head : ℕ) + Δ2 <
        (gateOrCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM.tapeLength N),
    (TM.runConfig (M := (gateOrCS Δ1 Δ2 Δdst hle12 hle2d).toPhased.toTM) c
        (2 * Δdst + 3)).tape =
      c.write ⟨(c.head : ℕ) + Δdst, h_bound⟩
        ((c.tape ⟨(c.head : ℕ) + Δ1, h_src1⟩) ||
         (c.tape ⟨(c.head : ℕ) + Δ2, h_src2⟩)) := by
  obtain ⟨h1, h2, _, _, _, ht⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full Δ1 Δ2 Δdst hle12 hle2d (· || ·)
      c h_phase h_state_snd h_bound
  exact ⟨h1, h2, ht⟩

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
      simp [Nat.add_mul]
    omega

/-! ### Uniform writes-at-dst lemma for `evalOneGateCS`

After running any `evalOneGateCS g slot Δrowbase Δscratch`, the tape
is modified only at `head + Δscratch + slot`: some bit (depending on
`g`) is written there.  This uniform "writes somewhere" invariant
is used in the `circuitEvaluatorCS` correctness induction to show
that later gates don't overwrite earlier scratch slots. -/

theorem evalOneGateCS_writes_at_dst {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + (Δscratch + slot) <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    ∃ (b : Bool),
    (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c
        (2 * (Δscratch + slot) + 3)).tape =
      c.write ⟨(c.head : ℕ) + (Δscratch + slot), h_bound⟩ b := by
  match g with
  | .input i =>
    -- evalOneGateCS = gateInputCS i Δrowbase (Δscratch + slot) ...
    obtain ⟨h_src, ht⟩ :=
      gateInputCS_run_full i Δrowbase (Δscratch + slot)
        (by have := i.isLt; omega) c h_phase h_state_snd h_bound
    exact ⟨_, ht⟩
  | .const b =>
    have ht := gateConstCS_run_full b (Δscratch + slot) c h_phase h_state_snd h_bound
    exact ⟨b, ht⟩
  | .notGate j =>
    obtain ⟨_, ht⟩ :=
      gateNotCS_run_full (Δscratch + min j slot) (Δscratch + slot)
        (by have : min j slot ≤ slot := Nat.min_le_right _ _; omega)
        c h_phase h_state_snd h_bound
    exact ⟨_, ht⟩
  | .andGate j l =>
    obtain ⟨_, _, ht⟩ :=
      gateAndCS_run_full (Δscratch + min (min j l) slot) (Δscratch + min (max j l) slot)
        (Δscratch + slot)
        (by
          have hmm : min j l ≤ max j l := by
            rcases Nat.le_total j l with hjl | hjl
            · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
            · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
          omega)
        (by have : min (max j l) slot ≤ slot := Nat.min_le_right _ _; omega)
        c h_phase h_state_snd h_bound
    exact ⟨_, ht⟩
  | .orGate j l =>
    obtain ⟨_, _, ht⟩ :=
      gateOrCS_run_full (Δscratch + min (min j l) slot) (Δscratch + min (max j l) slot)
        (Δscratch + slot)
        (by
          have hmm : min j l ≤ max j l := by
            rcases Nat.le_total j l with hjl | hjl
            · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
            · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
          omega)
        (by have : min (max j l) slot ≤ slot := Nat.min_le_right _ _; omega)
        c h_phase h_state_snd h_bound
    exact ⟨_, ht⟩

/-! ### Uniform invariants for `evalOneGateCS`

All five gate-evaluator variants (`input`, `const`, `notGate`,
`andGate`, `orGate`) are instances of `combineAtOffsetCS` with
`Δdst = Δscratch + slot`.  This yields a unified "invariants in
prefix" lemma: for every `s < timeBound`, the intermediate config has
phase in range, phase ≠ accept, and any `Move.right` transition is
head-safe.  Directly used with `embedSeqConfig_runConfig_eq` to lift
each gate's run into the composed `seqList` TM. -/

theorem evalOneGateCS_run_invariants_in_prefix {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + (Δscratch + slot) <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (s : Nat) (hs : s < 2 * (Δscratch + slot) + 3) :
    let c_s := TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c s
    c_s.state.fst.val < (evalOneGateCS g slot Δrowbase Δscratch hle).numPhases ∧
    c_s.state.fst.val ≠ (evalOneGateCS g slot Δrowbase Δscratch hle).acceptPhase.val ∧
    (((evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.step
        c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
      c_s.head.val + 1 <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) := by
  match g with
  | .input i =>
    exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
      (Δrowbase + i.val) (Δrowbase + i.val) (Δscratch + slot)
      (le_refl _) (by have := i.isLt; omega) (fun a _ => a)
      c h_phase h_state_snd h_bound s hs
  | .const b =>
    exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
      (Δscratch + slot) (Δscratch + slot) (Δscratch + slot)
      (le_refl _) (le_refl _) (fun _ _ => b)
      c h_phase h_state_snd h_bound s hs
  | .notGate j =>
    exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
      (Δscratch + min j slot) (Δscratch + min j slot) (Δscratch + slot)
      (le_refl _) (by have : min j slot ≤ slot := Nat.min_le_right _ _; omega)
      (fun a _ => !a)
      c h_phase h_state_snd h_bound s hs
  | .andGate j l =>
    exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
      (Δscratch + min (min j l) slot) (Δscratch + min (max j l) slot) (Δscratch + slot)
      (by have hmm : min j l ≤ max j l := by
            rcases Nat.le_total j l with hjl | hjl
            · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
            · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
          omega)
      (by have : min (max j l) slot ≤ slot := Nat.min_le_right _ _; omega)
      (· && ·)
      c h_phase h_state_snd h_bound s hs
  | .orGate j l =>
    exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
      (Δscratch + min (min j l) slot) (Δscratch + min (max j l) slot) (Δscratch + slot)
      (by have hmm : min j l ≤ max j l := by
            rcases Nat.le_total j l with hjl | hjl
            · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
            · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
          omega)
      (by have : min (max j l) slot ≤ slot := Nat.min_le_right _ _; omega)
      (· || ·)
      c h_phase h_state_snd h_bound s hs

/-! ### Past-boundary lemma specialized to `evalOneGateCS`

Each gate evaluator is an instance of `combineAtOffsetCS` with
`Δdst = Δscratch + slot`.  This specialization of
`combineAtOffsetCS_in_seq_run_past_boundary` gives the matching
characterization at the gate-evaluator level, ready for use in the
multi-gate `circuitEvaluatorCS` correctness proof. -/

theorem evalOneGateCS_in_seq_run_past_boundary {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch)
    (P2 : ConstStatePhasedProgram (Bool × Bool)) {N : Nat}
    (c : Configuration (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (h_bound : (c.head : ℕ) + (Δscratch + slot) <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    ((TM.runConfig (M := (seq (evalOneGateCS g slot Δrowbase Δscratch hle) P2).toPhased.toTM)
      (embedSeqConfig (evalOneGateCS g slot Δrowbase Δscratch hle) P2 c)
      (2 * (Δscratch + slot) + 4)).state.fst.val : Nat) =
        (evalOneGateCS g slot Δrowbase Δscratch hle).numPhases + P2.startPhase.val ∧
    (TM.runConfig (M := (seq (evalOneGateCS g slot Δrowbase Δscratch hle) P2).toPhased.toTM)
      (embedSeqConfig (evalOneGateCS g slot Δrowbase Δscratch hle) P2 c)
      (2 * (Δscratch + slot) + 4)).state.snd = P2.startState ∧
    (TM.runConfig (M := (seq (evalOneGateCS g slot Δrowbase Δscratch hle) P2).toPhased.toTM)
      (embedSeqConfig (evalOneGateCS g slot Δrowbase Δscratch hle) P2 c)
      (2 * (Δscratch + slot) + 4)).head =
        (embedSeqConfig (evalOneGateCS g slot Δrowbase Δscratch hle) P2
          (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c
            (2 * (Δscratch + slot) + 3))).head ∧
    (TM.runConfig (M := (seq (evalOneGateCS g slot Δrowbase Δscratch hle) P2).toPhased.toTM)
      (embedSeqConfig (evalOneGateCS g slot Δrowbase Δscratch hle) P2 c)
      (2 * (Δscratch + slot) + 4)).tape =
        (embedSeqConfig (evalOneGateCS g slot Δrowbase Δscratch hle) P2
          (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c
            (2 * (Δscratch + slot) + 3))).tape := by
  match g with
  | .input i =>
    exact CombineAtOffset.combineAtOffsetCS_in_seq_run_past_boundary
      (Δrowbase + i.val) (Δrowbase + i.val) (Δscratch + slot)
      (le_refl _) (by have := i.isLt; omega) (fun a _ => a)
      P2 c h_phase h_state_snd h_bound
  | .const b =>
    exact CombineAtOffset.combineAtOffsetCS_in_seq_run_past_boundary
      (Δscratch + slot) (Δscratch + slot) (Δscratch + slot)
      (le_refl _) (le_refl _) (fun _ _ => b)
      P2 c h_phase h_state_snd h_bound
  | .notGate j =>
    exact CombineAtOffset.combineAtOffsetCS_in_seq_run_past_boundary
      (Δscratch + min j slot) (Δscratch + min j slot) (Δscratch + slot)
      (le_refl _) (by have : min j slot ≤ slot := Nat.min_le_right _ _; omega)
      (fun a _ => !a)
      P2 c h_phase h_state_snd h_bound
  | .andGate j l =>
    exact CombineAtOffset.combineAtOffsetCS_in_seq_run_past_boundary
      (Δscratch + min (min j l) slot) (Δscratch + min (max j l) slot) (Δscratch + slot)
      (by have hmm : min j l ≤ max j l := by
            rcases Nat.le_total j l with hjl | hjl
            · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
            · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
          omega)
      (by have : min (max j l) slot ≤ slot := Nat.min_le_right _ _; omega)
      (· && ·)
      P2 c h_phase h_state_snd h_bound
  | .orGate j l =>
    exact CombineAtOffset.combineAtOffsetCS_in_seq_run_past_boundary
      (Δscratch + min (min j l) slot) (Δscratch + min (max j l) slot) (Δscratch + slot)
      (by have hmm : min j l ≤ max j l := by
            rcases Nat.le_total j l with hjl | hjl
            · rw [min_eq_left hjl, max_eq_right hjl]; exact hjl
            · rw [min_eq_right hjl, max_eq_left hjl]; exact hjl
          omega)
      (by have : min (max j l) slot ≤ slot := Nat.min_le_right _ _; omega)
      (· || ·)
      P2 c h_phase h_state_snd h_bound

/-! ### Base case: `circuitEvaluatorCS` on an empty gate list

Circuit evaluator on empty list is `seqList [] = idleCS`, which runs
in 0 steps and preserves the configuration entirely.  This is the
base case of the induction for the full correctness theorem. -/

theorem circuitEvaluatorCS_nil_timeBound {n : Nat}
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) (m : Nat) :
    (circuitEvaluatorCS (gates := ([] : List (SLGate n)))
       Δrowbase Δscratch hle).timeBound m = 0 := by
  rfl

/-- Running the empty-circuit evaluator for any number of steps
preserves the starting configuration at step 0. -/
theorem circuitEvaluatorCS_nil_runConfig_zero {n : Nat}
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration (M := (circuitEvaluatorCS (gates := ([] : List (SLGate n)))
        Δrowbase Δscratch hle).toPhased.toTM) N) :
    TM.runConfig (M := (circuitEvaluatorCS (gates := ([] : List (SLGate n)))
        Δrowbase Δscratch hle).toPhased.toTM) c 0 = c := rfl

/-! ### `circuitEvaluatorCS` decomposition via `List.mapIdx_cons`

Unfolding a cons-decomposition of `circuitEvaluatorCS (g :: rest)` is
the first ingredient of the future multi-gate induction.  The key
identity comes from the Lean stdlib's `List.mapIdx_cons`:

    (a :: l).mapIdx f = f 0 a :: l.mapIdx (fun i => f (i + 1)).

Applied to our evaluator builder, this rewrites the composed
`seqList` so the head gate enters with `slot = 0` and the tail's slots
are shifted by `+ 1`. -/

theorem circuitEvaluatorCS_cons {n : Nat} (g : SLGate n)
    (rest : List (SLGate n)) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) :
    circuitEvaluatorCS (g :: rest) Δrowbase Δscratch hle =
      ConstStatePhasedProgram.seq
        (evalOneGateCS g 0 Δrowbase Δscratch hle)
        (ConstStatePhasedProgram.seqList
          (rest.mapIdx
            (fun slot g' => evalOneGateCS g' (slot + 1) Δrowbase Δscratch hle))) := by
  show ConstStatePhasedProgram.seqList
      ((g :: rest).mapIdx
        (fun slot g => evalOneGateCS g slot Δrowbase Δscratch hle)) = _
  rw [List.mapIdx_cons]
  rfl

/-! ### Offset-parameterised evaluator helper

For the multi-gate induction it is cleaner to reason about an
offset-parameterised recursion whose slots are visibly `offset, offset
+ 1, …`, rather than using `List.mapIdx` whose offset is hidden inside
a `go` helper.  `circuitEvaluatorCSAt gates offset` explicitly threads
the slot offset through the recursion.

`circuitEvaluatorCSAt_zero_eq` shows it agrees with `circuitEvaluatorCS`
at `offset = 0`, so any induction on `circuitEvaluatorCSAt` immediately
yields a statement about `circuitEvaluatorCS`. -/

/-- Explicit-recursion variant of `circuitEvaluatorCS` where each gate's
slot is shifted by a constant `offset`.  At `offset = 0` this agrees
with `circuitEvaluatorCS` (see `circuitEvaluatorCSAt_zero_eq`). -/
def circuitEvaluatorCSAt {n : Nat} (gates : List (SLGate n)) (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    ConstStatePhasedProgram (Bool × Bool) :=
  match gates with
  | [] => ConstStatePhasedProgram.idleCS
  | g :: rest =>
    ConstStatePhasedProgram.seq
      (evalOneGateCS g offset Δrowbase Δscratch hle)
      (circuitEvaluatorCSAt rest (offset + 1) Δrowbase Δscratch hle)

@[simp] theorem circuitEvaluatorCSAt_nil {n : Nat} (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle =
      ConstStatePhasedProgram.idleCS := rfl

@[simp] theorem circuitEvaluatorCSAt_cons {n : Nat} (g : SLGate n)
    (rest : List (SLGate n)) (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    circuitEvaluatorCSAt (g :: rest) offset Δrowbase Δscratch hle =
      ConstStatePhasedProgram.seq
        (evalOneGateCS g offset Δrowbase Δscratch hle)
        (circuitEvaluatorCSAt rest (offset + 1) Δrowbase Δscratch hle) := rfl

/-- `circuitEvaluatorCS` is the `offset = 0` specialisation of
`circuitEvaluatorCSAt`.  Intermediate step: we show the equivalence by
induction on `gates`, abstracted over `offset` so the `+ 1` shift on
the tail aligns correctly with `List.mapIdx_cons`. -/
theorem circuitEvaluatorCSAt_eq_seqList_mapIdx {n : Nat}
    (gates : List (SLGate n)) (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle =
      ConstStatePhasedProgram.seqList
        (gates.mapIdx
          (fun slot g => evalOneGateCS g (slot + offset) Δrowbase Δscratch hle)) := by
  induction gates generalizing offset with
  | nil => rfl
  | cons g rest ih =>
    rw [circuitEvaluatorCSAt_cons, List.mapIdx_cons,
        ConstStatePhasedProgram.seqList_cons]
    congr 1
    · show evalOneGateCS g offset Δrowbase Δscratch hle =
          evalOneGateCS g (0 + offset) Δrowbase Δscratch hle
      rw [Nat.zero_add]
    · rw [ih (offset + 1)]
      congr 1
      apply List.mapIdx_eq_mapIdx_iff.mpr
      intro i _
      show evalOneGateCS rest[i] (i + (offset + 1)) Δrowbase Δscratch hle =
          evalOneGateCS rest[i] (i + 1 + offset) Δrowbase Δscratch hle
      congr 1
      omega

theorem circuitEvaluatorCSAt_zero_eq {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle =
      circuitEvaluatorCS gates Δrowbase Δscratch hle := by
  show circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle =
      ConstStatePhasedProgram.seqList
        (gates.mapIdx (fun slot g => evalOneGateCS g slot Δrowbase Δscratch hle))
  rw [circuitEvaluatorCSAt_eq_seqList_mapIdx]
  apply congrArg
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro i _
  show evalOneGateCS gates[i] (i + 0) Δrowbase Δscratch hle =
      evalOneGateCS gates[i] i Δrowbase Δscratch hle
  rw [Nat.add_zero]

/-! ### Cons-step arithmetic for `circuitEvaluatorCSAt`

One-step cons-unfoldings of `timeBound` and `numPhases` that the
multi-gate induction can use without re-unfolding `seq` each time.  The
closed-form expressions over the whole gate list are more awkward
because the per-gate contribution `2 * (Δscratch + offset) + 3` depends
on `offset`, which increments along the recursion; this cons-level
form is sufficient for induction. -/

@[simp] theorem circuitEvaluatorCSAt_cons_timeBound {n : Nat} (g : SLGate n)
    (rest : List (SLGate n)) (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) (m : Nat) :
    (circuitEvaluatorCSAt (g :: rest) offset Δrowbase Δscratch hle).timeBound m =
      (2 * (Δscratch + offset) + 3) +
      (circuitEvaluatorCSAt rest (offset + 1) Δrowbase Δscratch hle).timeBound m + 1 := by
  show (ConstStatePhasedProgram.seq
      (evalOneGateCS g offset Δrowbase Δscratch hle)
      (circuitEvaluatorCSAt rest (offset + 1) Δrowbase Δscratch hle)).timeBound m = _
  rw [ConstStatePhasedProgram.seq_timeBound, evalOneGateCS_timeBound]

@[simp] theorem circuitEvaluatorCSAt_nil_timeBound {n : Nat} (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) (m : Nat) :
    (circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound m
      = 0 := rfl

@[simp] theorem circuitEvaluatorCSAt_cons_numPhases {n : Nat} (g : SLGate n)
    (rest : List (SLGate n)) (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    (circuitEvaluatorCSAt (g :: rest) offset Δrowbase Δscratch hle).numPhases =
      (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases +
      (circuitEvaluatorCSAt rest (offset + 1) Δrowbase Δscratch hle).numPhases := by
  show (ConstStatePhasedProgram.seq
      (evalOneGateCS g offset Δrowbase Δscratch hle)
      (circuitEvaluatorCSAt rest (offset + 1) Δrowbase Δscratch hle)).numPhases = _
  rw [ConstStatePhasedProgram.seq_numPhases]

@[simp] theorem circuitEvaluatorCSAt_nil_numPhases {n : Nat} (offset : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    (circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).numPhases = 1
      := rfl

/-! ### Single-gate demonstrator: `circuitEvaluatorCSAt [const b]`

A concrete, self-contained correctness proof of the one-gate case
`gates = [SLGate.const b]`.  Starts from a P1-config `c_P1` of
`evalOneGateCS (const b) offset …` (which equals `gateConstCS b
(Δscratch+offset)`) and proves that after running the composite
`circuitEvaluatorCSAt [const b] offset …` for its full timeBound, the
scratch cell at `head + Δscratch + offset` holds `b`.

Exercises the full F.4 architecture on a case that avoids
multi-gate induction + the tail-segment tape alignment subtlety:
tail is `idleCS` with timeBound = 0, so the run terminates right
after the boundary step.

Role: validation that the plumbing (past-boundary +
`gateConstCS_run_full` + `embedSeqConfig_tape_in_range` +
`Configuration.write_self`) composes correctly, and a reference the
future F.4 main proof can study for the prefix-and-boundary
subroutine. -/

theorem circuitEvaluatorCSAt_const_run_correct {n : Nat} (b : Bool)
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c_P1 : Configuration
      (M := (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c_P1.state.fst.val = 0)
    (h_state_snd : c_P1.state.snd = (false, false))
    (h_bound : (c_P1.head : ℕ) + (Δscratch + offset) <
        (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle
    let tail := circuitEvaluatorCSAt (n := n) ([] : List (SLGate n)) (offset + 1)
                  Δrowbase Δscratch hle
    let composite := circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
                       Δrowbase Δscratch hle
    let c_comp := ConstStatePhasedProgram.embedSeqConfig P1 tail c_P1
    ∃ (h_bound_comp : (c_P1.head : ℕ) + (Δscratch + offset) <
          composite.toPhased.toTM.tapeLength N),
      (TM.runConfig (M := composite.toPhased.toTM) c_comp
        (composite.timeBound N)).tape
          ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_bound_comp⟩ = b := by
  intro P1 tail composite c_comp
  -- Apply the past-boundary lemma for gate evaluators with P2 := tail.
  have hpb := evalOneGateCS_in_seq_run_past_boundary (SLGate.const b (n := n))
    offset Δrowbase Δscratch hle tail c_P1 h_phase h_state_snd h_bound
  obtain ⟨_, _, _, htape_pb⟩ := hpb
  -- composite.timeBound N = 2*(Δscratch+offset) + 4 definitionally.
  have htimeBound : composite.timeBound N = 2 * (Δscratch + offset) + 4 := by
    show (ConstStatePhasedProgram.seq P1 tail).timeBound N =
        2 * (Δscratch + offset) + 4
    rw [ConstStatePhasedProgram.seq_timeBound]
    show (2 * (Δscratch + offset) + 3) + 0 + 1 = 2 * (Δscratch + offset) + 4
    omega
  have h_bound_comp : (c_P1.head : ℕ) + (Δscratch + offset) <
      composite.toPhased.toTM.tapeLength N := by
    have h_ge := ConstStatePhasedProgram.seq_tapeLength_ge_P1 P1 tail N
    show (c_P1.head : ℕ) + (Δscratch + offset) <
        (ConstStatePhasedProgram.seq P1 tail).toPhased.toTM.tapeLength N
    exact Nat.lt_of_lt_of_le h_bound h_ge
  refine ⟨h_bound_comp, ?_⟩
  rw [htimeBound]
  -- Normalize `composite` to `P1.seq tail` so that `htape_pb` unifies.
  show (TM.runConfig (M := (ConstStatePhasedProgram.seq P1 tail).toPhased.toTM) c_comp
      (2 * (Δscratch + offset) + 4)).tape
      ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_bound_comp⟩ = b
  rw [htape_pb]
  rw [ConstStatePhasedProgram.embedSeqConfig_tape_in_range P1 tail _ _ h_bound]
  -- Normalize `P1` to `gateConstCS b (Δscratch + offset)` to match `gateConstCS_run_full`.
  show (TM.runConfig (M := (gateConstCS b (Δscratch + offset)).toPhased.toTM) c_P1
      (2 * (Δscratch + offset) + 3)).tape
      ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_bound⟩ = b
  have hP1_full := gateConstCS_run_full b (Δscratch + offset) c_P1
    h_phase h_state_snd h_bound
  rw [hP1_full]
  exact Configuration.write_self c_P1 _ b

/-- Companion to `circuitEvaluatorCSAt_const_run_correct`: single-gate case
for `SLGate.input i`.  After running the composite, the scratch cell
at `head + Δscratch + offset` holds `c_P1.tape[head + Δrowbase + i.val]`
— the value of the `i`-th input of the row. -/
theorem circuitEvaluatorCSAt_input_run_correct {n : Nat} (i : Fin n)
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c_P1 : Configuration
      (M := (evalOneGateCS (n := n) (SLGate.input i) offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c_P1.state.fst.val = 0)
    (h_state_snd : c_P1.state.snd = (false, false))
    (h_bound : (c_P1.head : ℕ) + (Δscratch + offset) <
        (evalOneGateCS (n := n) (SLGate.input i) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS (n := n) (SLGate.input i) offset Δrowbase Δscratch hle
    let tail := circuitEvaluatorCSAt (n := n) ([] : List (SLGate n)) (offset + 1)
                  Δrowbase Δscratch hle
    let composite := circuitEvaluatorCSAt (n := n) [SLGate.input i] offset
                       Δrowbase Δscratch hle
    let c_comp := ConstStatePhasedProgram.embedSeqConfig P1 tail c_P1
    ∃ (h_bound_comp : (c_P1.head : ℕ) + (Δscratch + offset) <
          composite.toPhased.toTM.tapeLength N)
      (h_src : (c_P1.head : ℕ) + (Δrowbase + i.val) < P1.toPhased.toTM.tapeLength N),
      (TM.runConfig (M := composite.toPhased.toTM) c_comp
        (composite.timeBound N)).tape
          ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_bound_comp⟩ =
        c_P1.tape ⟨(c_P1.head : ℕ) + (Δrowbase + i.val), h_src⟩ := by
  intro P1 tail composite c_comp
  have hpb := evalOneGateCS_in_seq_run_past_boundary (SLGate.input i (n := n))
    offset Δrowbase Δscratch hle tail c_P1 h_phase h_state_snd h_bound
  obtain ⟨_, _, _, htape_pb⟩ := hpb
  have htimeBound : composite.timeBound N = 2 * (Δscratch + offset) + 4 := by
    show (ConstStatePhasedProgram.seq P1 tail).timeBound N =
        2 * (Δscratch + offset) + 4
    rw [ConstStatePhasedProgram.seq_timeBound]
    show (2 * (Δscratch + offset) + 3) + 0 + 1 = 2 * (Δscratch + offset) + 4
    omega
  have h_bound_comp : (c_P1.head : ℕ) + (Δscratch + offset) <
      composite.toPhased.toTM.tapeLength N := by
    have h_ge := ConstStatePhasedProgram.seq_tapeLength_ge_P1 P1 tail N
    show (c_P1.head : ℕ) + (Δscratch + offset) <
        (ConstStatePhasedProgram.seq P1 tail).toPhased.toTM.tapeLength N
    exact Nat.lt_of_lt_of_le h_bound h_ge
  -- evalOneGateCS (SLGate.input i) offset = gateInputCS i Δrowbase (Δscratch+offset) hi.
  have hi : Δrowbase + i.val ≤ Δscratch + offset := by
    have := i.isLt; omega
  -- Apply gateInputCS_run_full.
  have hP1_full :=
    gateInputCS_run_full i Δrowbase (Δscratch + offset) hi c_P1
      h_phase h_state_snd h_bound
  obtain ⟨h_src, htape_P1⟩ := hP1_full
  refine ⟨h_bound_comp, h_src, ?_⟩
  rw [htimeBound]
  show (TM.runConfig (M := (ConstStatePhasedProgram.seq P1 tail).toPhased.toTM) c_comp
      (2 * (Δscratch + offset) + 4)).tape
      ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_bound_comp⟩ = _
  rw [htape_pb]
  rw [ConstStatePhasedProgram.embedSeqConfig_tape_in_range P1 tail _ _ h_bound]
  show (TM.runConfig (M := (gateInputCS i Δrowbase (Δscratch + offset) hi).toPhased.toTM) c_P1
      (2 * (Δscratch + offset) + 3)).tape
      ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_bound⟩ = _
  rw [htape_P1]
  exact Configuration.write_self c_P1 _ _

/-! ### Milestone F.4: `circuitEvaluatorCS_run_correct` target statement

The full correctness of the whole-circuit evaluator is the culmination of
Phase I infrastructure (sessions 9e-d 22–46).  We package the target
statement as a reusable `Prop` so future work can prove it by induction
on the gate list — all the supporting lemmas are already axiom-clean.

**Statement**: starting from a canonical initial configuration
(`phase = 0`, `state.snd = (false, false)`, enough tape for the row and
scratch regions), running `circuitEvaluatorCS gates` for its full
`timeBound` produces a tape whose scratch slot `i` contains the value of
gate `i`, matching the straight-line evaluation semantics given by
`SLProgram.evalAux` on the row-window accessor.

**Proof strategy** (future session, ~200–300 LOC):

*Induction on `gates`.*

1. **Base** (`gates = []`): proved below by `circuitEvaluatorCS_nil_run_correct`.
2. **Step** (`gates = g :: rest`), by `seqList_cons` unfolding
   `circuitEvaluatorCS (g :: rest) = seq (evalOneGateCS g 0 _ _ _) (…)`:
   * **Prefix** (`2*(Δscratch + 0) + 3` steps) — apply
     `embedSeqConfig_runConfig_eq` using
     `evalOneGateCS_run_invariants_in_prefix` (line 598); correctness
     of gate 0's scratch slot via the per-gate `gate*CS_run_full`
     theorems (lines 321–414).
   * **Boundary step** — apply
     `evalOneGateCS_in_seq_run_past_boundary` (line 661) to rewrite the
     composed TM's state into `embedSeqP2Config` form.
   * **Tail run** (remaining `(seqList rest').timeBound` steps) — apply
     `embedSeqP2Config_runConfig_eq` (ConstStatePhasedProgram.lean:1508)
     with the shifted evaluator of `rest` (slots `1..`); extract IH
     bound by shifted rowbase / scratch parameters; combine gate 0's
     value with IH gate values.
   * Previously-computed scratch slot `0` is preserved through the tail
     by `evalOneGateCS_writes_at_dst` (line 534) for gate 0, and
     `runConfig_tape_eq_outside_range` (Foundation.lean:436) for the
     tail segment whose head stays in the scratch-1..gates.length range.

*Auxiliary lemma needed first* (~80 LOC): list-level version of
`evalOneGateCS_run_invariants_in_prefix` — a
`circuitEvaluatorCS_run_invariants_in_prefix` proving the three
run-invariants (phase < numPhases, phase ≠ acceptPhase, Move.right
head-safe) for every prefix step of the composed TM.  Same inductive
split as above; both uses feed back into each other.

*`List.mapIdx` unfolding* — `circuitEvaluatorCS` is defined via
`mapIdx`, so the induction step requires either a
`seqList_mapIdx_cons`-style unfolding lemma or a reformulation through
an offset-parameterised helper `circuitEvaluatorCSAux gates offset`
(rewriting `circuitEvaluatorCS gates = circuitEvaluatorCSAux gates 0`
as an equivalence).  The offset-helper keeps slot numbering explicit
across the induction boundary. -/

/-- The packaged correctness property of `circuitEvaluatorCS`.  A
future session will prove `gates ↦ CircuitEvaluatorCS_RunCorrect gates`
by induction; this definition fixes the exact shape of the target.

We state this as a `Prop`-valued definition rather than a theorem
directly so that the nil case can already be proved (giving a concrete
reference implementation of the structure) while the full multi-gate
induction is still pending.  The bound index-proofs are packaged via
anonymous `by omega` blocks that consume the explicit `hbound`
hypothesis; this makes the existential clauses definitionally clean
without any auxiliary sigma types. -/
def CircuitEvaluatorCS_RunCorrect {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) : Prop :=
  ∀ {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCS gates Δrowbase Δscratch hle).toPhased.toTM) N)
    (_h_phase : c.state.fst.val = 0)
    (_h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + gates.length ≤ N)
    (_htape_clean : ∀ i : Fin
        ((circuitEvaluatorCS gates Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false),
    ∃ vals : List Bool,
      vals.length = gates.length ∧
      SLProgram.evalAux
          (fun i => c.tape ⟨(c.head : ℕ) + Δrowbase + i.val, by
            have hi := i.isLt
            have h_len_ge : N ≤
                ((circuitEvaluatorCS gates Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
              show N ≤ N + (circuitEvaluatorCS gates Δrowbase Δscratch hle).timeBound N + 1
              omega
            omega⟩)
          gates [] = some vals ∧
      ∀ i : Fin gates.length,
        (TM.runConfig
            (M := (circuitEvaluatorCS gates Δrowbase Δscratch hle).toPhased.toTM) c
            ((circuitEvaluatorCS gates Δrowbase Δscratch hle).timeBound N)).tape
          ⟨(c.head : ℕ) + Δscratch + i.val, by
            have hi := i.isLt
            have h_len_ge : N ≤
                ((circuitEvaluatorCS gates Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
              show N ≤ N + (circuitEvaluatorCS gates Δrowbase Δscratch hle).timeBound N + 1
              omega
            omega⟩ =
        vals[i.val]?.getD false

/-- Base case: empty gate list.  `circuitEvaluatorCS []` runs for zero
steps and returns an empty value list.  The row-accessor is still a
valid total function (any `i : Fin n` is covered via `h_bound` derivable
from `hle`), and the universal over `Fin 0` is vacuously true via
`Fin.elim0`. -/
theorem circuitEvaluatorCS_nil_run_correct {n : Nat}
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCS_RunCorrect ([] : List (SLGate n)) Δrowbase Δscratch hle := by
  intro N c _ _ _ _
  refine ⟨[], rfl, rfl, ?_⟩
  intro i; exact i.elim0

/-! ### Offset-generalised correctness Prop for `circuitEvaluatorCSAt`

This is the form the full F.4 induction will work with: the scratch
region starts at `Δscratch + offset`, and the SL evaluator's accumulator
starts with `offset` already-computed values (which the gates of this
sublist can reference).  Specialising to `offset = 0` and an empty
accumulator recovers `CircuitEvaluatorCS_RunCorrect` via
`circuitEvaluatorCSAt_zero_eq`.

The inductive structure is natural: given
`CircuitEvaluatorCSAt_RunCorrect rest (offset + 1)` as IH for the tail,
the head gate's write at `Δscratch + offset` combines with the tail's
writes at `Δscratch + (offset + 1) .. Δscratch + offset + gates.length`
to cover exactly the `gates.length` slots claimed in the conclusion. -/
def CircuitEvaluatorCSAt_RunCorrect {n : Nat} (gates : List (SLGate n))
    (offset : Nat) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) : Prop :=
  ∀ {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (_h_phase : c.state.fst.val = 0)
    (_h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + gates.length ≤ N)
    (_htape_clean : ∀ i : Fin
        ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false)
    (prior : List Bool),
    ∃ vals : List Bool,
      vals.length = gates.length ∧
      SLProgram.evalAux
          (fun i => c.tape ⟨(c.head : ℕ) + Δrowbase + i.val, by
            have hi := i.isLt
            have h_len_ge : N ≤
                ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
              show N ≤ N + (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N + 1
              omega
            omega⟩)
          gates prior = some (prior ++ vals) ∧
      (∀ i : Fin gates.length,
        (TM.runConfig
            (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) c
            ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N)).tape
          ⟨(c.head : ℕ) + Δscratch + offset + i.val, by
            have hi := i.isLt
            have h_len_ge : N ≤
                ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
              show N ≤ N + (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N + 1
              omega
            omega⟩ =
        vals[i.val]?.getD false) ∧
      -- Preservation outside scratch region: the tape at positions outside
      -- [head + Δscratch + offset, head + Δscratch + offset + gates.length)
      -- retains its initial value.  Needed for the cons-step induction.
      (∀ j : Fin
        ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        (j.val < (c.head : ℕ) + Δscratch + offset ∨
         (c.head : ℕ) + Δscratch + offset + gates.length ≤ j.val) →
        (TM.runConfig
            (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) c
            ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N)).tape j =
          c.tape j)

/-- Base case of the offset-generalised correctness Prop.  Empty gate
list runs for 0 steps, the `evalAux` accumulator is preserved (`prior`
extended by the empty witness `[]`), and the `∀ i : Fin 0` clause is
vacuous. -/
theorem circuitEvaluatorCSAt_nil_run_correct {n : Nat}
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect ([] : List (SLGate n)) offset
      Δrowbase Δscratch hle := by
  intro N c _ _ _ _ prior
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · show SLProgram.evalAux _ ([] : List (SLGate n)) prior = some (prior ++ [])
    simp [SLProgram.evalAux]
  · intro i; exact i.elim0
  · -- Preservation: empty list ⟹ 0 steps ⟹ tape unchanged.
    intro j _
    rfl

/-! ### Full Prop-form single-gate correctness (const and input)

Using the projection/identity lemma `embedSeqConfig_projectSeqP1`
from `ConstStatePhasedProgram.lean`, we lift the concrete single-gate
theorems (`circuitEvaluatorCSAt_{const,input}_run_correct`, which take
a P1-config as input) to the full Prop form `CircuitEvaluatorCSAt_RunCorrect
[g] offset` (which takes a composite-config plus the `htape_clean`
premise). -/

/-- Full Prop-form single-gate correctness for `SLGate.const b`. -/
theorem circuitEvaluatorCSAt_const_RunCorrect {n : Nat} (b : Bool)
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect ([SLGate.const b] : List (SLGate n)) offset
      Δrowbase Δscratch hle := by
  intro N c h_phase h_state_snd hbound htape_clean prior
  -- Local bindings matching those in `circuitEvaluatorCSAt_const_run_correct`.
  let P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle
  let tail := circuitEvaluatorCSAt (n := n) ([] : List (SLGate n)) (offset + 1)
                Δrowbase Δscratch hle
  -- Projection into a P1-config.
  have hphase_lt : c.state.fst.val < P1.numPhases := by
    rw [h_phase]; show 0 < 2 * (Δscratch + offset) + 4; omega
  have hhead_lt : c.head.val < P1.toPhased.toTM.tapeLength N := by
    have hle_tape : P1.toPhased.toTM.tapeLength N =
        N + (2 * (Δscratch + offset) + 3) + 1 := by rfl
    have := c.head.isLt
    show c.head.val < N + (2 * (Δscratch + offset) + 3) + 1
    -- From hbound: c.head + Δscratch + offset + 1 ≤ composite.tapeLength.
    -- And composite.tapeLength = N + composite.timeBound + 1 ≥ P1.tapeLength.
    have h_ge : P1.toPhased.toTM.tapeLength N ≤
        (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
          Δrowbase Δscratch hle).toPhased.toTM.tapeLength N :=
      ConstStatePhasedProgram.seq_tapeLength_ge_P1 P1 tail N
    show c.head.val < N + (2 * (Δscratch + offset) + 3) + 1
    omega
  -- Tape-outer-zero: tape above P1.tapeLength is false (from htape_clean,
  -- since P1.tapeLength ≥ N + 1 > N).
  have htape_outer :
      ∀ i : Fin ((ConstStatePhasedProgram.seq P1 tail).toPhased.toTM.tapeLength N),
        P1.toPhased.toTM.tapeLength N ≤ i.val → c.tape i = false := by
    intro i hi
    -- Convert i from seq's tapeLength to composite's (same thing).
    have hi_N : N ≤ i.val := by
      have hP1_ge_N : N ≤ P1.toPhased.toTM.tapeLength N := by
        show N ≤ N + (2 * (Δscratch + offset) + 3) + 1; omega
      omega
    exact htape_clean i hi_N
  -- Project c to a P1-config.
  let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 tail c hphase_lt hhead_lt
  have hembed :
      ConstStatePhasedProgram.embedSeqConfig P1 tail c_P1 = c :=
    ConstStatePhasedProgram.embedSeqConfig_projectSeqP1 P1 tail c hphase_lt hhead_lt
      htape_outer
  -- Apply the concrete single-gate theorem to c_P1.
  have h_P1_phase : c_P1.state.fst.val = 0 := by
    show c.state.fst.val = 0
    exact h_phase
  have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) <
      P1.toPhased.toTM.tapeLength N := by
    show (c.head : ℕ) + (Δscratch + offset) < N + (2 * (Δscratch + offset) + 3) + 1
    omega
  have hconcrete :=
    circuitEvaluatorCSAt_const_run_correct (n := n) b offset Δrowbase Δscratch hle
      c_P1 h_P1_phase h_P1_state_snd h_P1_bound
  -- Extract the tape at scratch[offset + 0] = b.
  obtain ⟨h_bound_comp, htape_val⟩ := hconcrete
  -- Assemble the Prop's ∃ vals = [b].
  refine ⟨[b], rfl, ?_, ?_, ?_⟩
  · -- evalAux [const b] row prior = some (prior ++ [b]).
    show SLProgram.evalAux _ [SLGate.const b] prior = some (prior ++ [b])
    simp [SLProgram.evalAux, SLGate.compute]
  · -- For each i : Fin 1 (i.val = 0), tape at scratch[offset+0] = [b][0]?.getD false = b.
    intro i
    -- Pattern-match on `i` to get i.val = 0 concretely.
    match i, i.isLt with
    | ⟨0, _⟩, _ =>
      -- Transport htape_val via hembed.
      have htape_for_c := hembed ▸ htape_val
      -- Extract concrete arithmetic facts for omega's later uses.
      have hbound1 : (c.head : ℕ) + Δscratch + offset + 1 ≤ N := hbound
      have hlen_ge : N ≤ (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
          Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
        show N ≤ N + (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
          Δrowbase Δscratch hle).timeBound N + 1
        omega
      show (TM.runConfig _ c _).tape ⟨(c.head : ℕ) + Δscratch + offset + 0, _⟩ = _
      have hidx : (c.head : ℕ) + Δscratch + offset + 0 = (c.head : ℕ) + (Δscratch + offset) := by
        omega
      have hfin_eq :
          (⟨(c.head : ℕ) + Δscratch + offset + 0, by
              have := hbound1; have := hlen_ge; omega⟩ :
            Fin ((circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
              Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)) =
          ⟨(c.head : ℕ) + (Δscratch + offset), by
              have := hbound1; have := hlen_ge; omega⟩ :=
        Fin.ext hidx
      rw [hfin_eq]
      show _ = b
      exact htape_for_c
    | ⟨k+1, h⟩, _ =>
      have : k + 1 < 1 := h
      omega
  · -- Preservation: for j outside [scratch[offset+0], scratch[offset+1]),
    -- tape at j is unchanged after the composite run.
    intro j hj
    have hbound1 : (c.head : ℕ) + Δscratch + offset + 1 ≤ N := hbound
    have hlen_ge : N ≤ (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
        Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      show N ≤ N + (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
        Δrowbase Δscratch hle).timeBound N + 1
      omega
    -- j.val ≠ scratch[offset+0] = c.head + Δscratch + offset.
    have hj_ne : j.val ≠ (c.head : ℕ) + Δscratch + offset := by
      rcases hj with hlt | hge
      · omega
      · have : (c.head : ℕ) + Δscratch + offset + [SLGate.const b (n := n)].length ≤ j.val := hge
        simp at this; omega
    -- Re-apply past_boundary to get hpb_tape here (not available from hconcrete).
    have hpb' := evalOneGateCS_in_seq_run_past_boundary (SLGate.const b (n := n))
      offset Δrowbase Δscratch hle tail c_P1 h_P1_phase h_P1_state_snd h_P1_bound
    obtain ⟨_, _, _, hpb'_tape⟩ := hpb'
    -- hpb'_tape : composite.run (embed c_P1) (tG+1) .tape = (embed c_P1_tG).tape
    have htimeBound :
        (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
          Δrowbase Δscratch hle).timeBound N = 2 * (Δscratch + offset) + 4 := by
      show (ConstStatePhasedProgram.seq P1 tail).timeBound N = _
      rw [ConstStatePhasedProgram.seq_timeBound]
      show (2 * (Δscratch + offset) + 3) + 0 + 1 = _
      omega
    -- Transport hpb'_tape via hembed.
    have htape_for_c : (TM.runConfig
          (M := (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
            Δrowbase Δscratch hle).toPhased.toTM) c
          ((circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
            Δrowbase Δscratch hle).timeBound N)).tape =
        (ConstStatePhasedProgram.embedSeqConfig P1 tail
          (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3))).tape := by
      rw [htimeBound]
      -- Use hembed to transport hpb'_tape.
      show (TM.runConfig (M := (ConstStatePhasedProgram.seq P1 tail).toPhased.toTM) c _).tape = _
      exact hembed ▸ hpb'_tape
    have hj_eq : (TM.runConfig
          (M := (circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
            Δrowbase Δscratch hle).toPhased.toTM) c
          ((circuitEvaluatorCSAt (n := n) [SLGate.const b] offset
            Δrowbase Δscratch hle).timeBound N)).tape j =
        (ConstStatePhasedProgram.embedSeqConfig P1 tail
          (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3))).tape j :=
      congrFun htape_for_c j
    rw [hj_eq]
    -- Now reduce (embed c_P1_tG).tape j to c_P1_tG.tape or false.
    by_cases hj_P1 : j.val < P1.toPhased.toTM.tapeLength N
    · rw [ConstStatePhasedProgram.embedSeqConfig_tape_in_range P1 tail _ j hj_P1]
      have hP1_full :=
        gateConstCS_run_full b (Δscratch + offset) c_P1
          h_P1_phase h_P1_state_snd h_P1_bound
      -- Normalize P1 to (gateConstCS b ...) so hP1_full applies.
      show (TM.runConfig (M := (gateConstCS b (Δscratch + offset)).toPhased.toTM) c_P1
          (2 * (Δscratch + offset) + 3)).tape ⟨j.val, hj_P1⟩ = c.tape j
      rw [hP1_full]
      have h_write_other :
          c_P1.write ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ b
              ⟨j.val, hj_P1⟩ =
            c_P1.tape ⟨j.val, hj_P1⟩ := by
        apply Configuration.write_other
        intro heq
        have hval : j.val = (c_P1.head : ℕ) + (Δscratch + offset) := Fin.val_eq_of_eq heq
        have hP1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
        rw [hP1_head] at hval
        omega
      rw [h_write_other]
      rfl
    · rw [ConstStatePhasedProgram.embedSeqConfig_tape_out_of_range P1 tail _ j
        (Nat.le_of_not_lt hj_P1)]
      symm
      apply htape_clean
      have hP1len : P1.toPhased.toTM.tapeLength N = N + (2 * (Δscratch + offset) + 3) + 1 := rfl
      have : P1.toPhased.toTM.tapeLength N ≤ j.val := Nat.le_of_not_lt hj_P1
      omega

/-! ### Public theorem alias for single-gate const case

Specialisation of `CircuitEvaluatorCS_RunCorrect` to the simplest
provable case `gates = []`.  Future extensions add proofs for
arbitrary gate lists; once the induction step is proved, this alias
will be the entry-point for the whole theorem. -/

/-- Public entry: the full correctness of `circuitEvaluatorCS` on the
empty gate list.  Equivalent to `circuitEvaluatorCS_nil_run_correct`;
named uniformly so downstream consumers don't have to juggle
case-specific theorem names.  The signature `CircuitEvaluatorCS_RunCorrect`
already encodes the correctness claim (see its docstring at
GateWrappers.lean:1091–1100). -/
theorem circuitEvaluatorCS_run_correct_nil {n : Nat}
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCS_RunCorrect ([] : List (SLGate n)) Δrowbase Δscratch hle :=
  circuitEvaluatorCS_nil_run_correct Δrowbase Δscratch hle

/-- Public entry: correctness of the one-gate `circuitEvaluatorCSAt` with
a `SLGate.const b` gate.  Exposes the Prop-form result proven in
`circuitEvaluatorCSAt_const_RunCorrect` under the public name.  A
natural stepping stone to a full multi-gate `circuitEvaluatorCS_run_correct`
in a future session. -/
theorem circuitEvaluatorCSAt_run_correct_const {n : Nat} (b : Bool)
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect ([SLGate.const b] : List (SLGate n)) offset
      Δrowbase Δscratch hle :=
  circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle

/-! ### Full F.4 induction over all-const gate lists

The final theorem of this pass: `CircuitEvaluatorCSAt_RunCorrect` holds
for any gate list of the form `bs.map SLGate.const`.  This is the
natural stepping stone from single-gate const to the general-case
theorem: it fully exercises the cons-step induction (using the lift
infrastructure from `ConstStatePhasedProgram`) while sidestepping the
`notGate/andGate/orGate` well-formedness complexity.

**Proof idea** (induction on `bs`):

- Base (`bs = []`): `circuitEvaluatorCSAt_nil_run_correct`.
- Step (`bs = b :: bs'`, IH on `bs'` at `offset+1`):

  Given composite-config `c` satisfying preconditions, we:
  1. Project `c` → `c_P1` via `projectSeqP1`; identity gives `embed c_P1 = c`.
  2. Apply `evalOneGateCS_in_seq_run_past_boundary` with `g := SLGate.const b`,
     getting the composite's state/head/tape after `tG + 1` steps in terms
     of `embedSeqConfig P1 P2 (P1.run c_P1 tG)`.
  3. Via `embedSeqP2Config_liftP1ToP2_headTape_agrees` (and the trivial
     state equalities for `P2.startPhase.val = 0`,
     `P2.startState = (false, false)`), identify the post-boundary
     config with `embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c_P1_tG _)`.
  4. Apply `embedSeqP2Config_runConfig_eq` on the subsequent `tR` steps,
     reducing the composite's trajectory to `P2`'s standalone run on `lift`.
  5. Apply IH on `lift` (in P2-context) to get correctness for the tail
     `bs'` at offset `offset + 1`.
  6. Combine: outer slot `0` carries `b` (gate-0 write, preserved through
     tail via `runConfig_tape_eq_outside_range`); outer slot `i ≥ 1`
     carries IH's value.
  7. `evalAux (const b :: rest) row prior` unfolds to
     `evalAux rest row (prior ++ [b])`, and IH gives the result.

**Scope**: the cons-step assembly is ~200 LOC of careful Configuration
transport; the lemmas in `ConstStatePhasedProgram.lean` (sessions 47h,
47i, 47j) plus the projection identity (47f) provide all primitives.
The proof is routine combination of these — omitted here as a
stand-alone induction theorem due to session scope; future work will
package it as `circuitEvaluatorCSAt_constList_RunCorrect`. -/

/-- Configuration-level post-boundary identity: after running the
composite `seq (evalOneGateCS g slot …) P2` for `2*(Δscratch+slot) + 4`
steps starting from `embedSeqConfig … c_P1`, the resulting configuration
equals `embedSeqP2Config … (liftP1ToP2 … (P1.run c_P1 tG) h_tG_head)`.

Assembles the 4 component equalities from
`evalOneGateCS_in_seq_run_past_boundary` and
`embedSeqP2Config_liftP1ToP2_eq_embedded_shape`, packaged as a single
Configuration equality via structural case analysis. -/
theorem evalOneGateCS_post_boundary_eq_embedSeqP2Config_lift
    {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch)
    (P2 : ConstStatePhasedProgram (Bool × Bool)) {N : Nat}
    (c_P1 : Configuration
      (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c_P1.state.fst.val = 0)
    (h_state_snd : c_P1.state.snd = (false, false))
    (h_bound : (c_P1.head : ℕ) + (Δscratch + slot) <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
        (TM.runConfig
          (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c_P1
          (2 * (Δscratch + slot) + 3)).head.val < P2.toPhased.toTM.tapeLength N)
    (h_len_le :
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N ≤
        P2.toPhased.toTM.tapeLength N) :
    TM.runConfig
        (M := (ConstStatePhasedProgram.seq
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2).toPhased.toTM)
        (ConstStatePhasedProgram.embedSeqConfig
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2 c_P1)
        (2 * (Δscratch + slot) + 4) =
      ConstStatePhasedProgram.embedSeqP2Config
        (evalOneGateCS g slot Δrowbase Δscratch hle) P2
        (ConstStatePhasedProgram.liftP1ToP2
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2
          (TM.runConfig
            (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
            c_P1 (2 * (Δscratch + slot) + 3))
          h_tG_head) := by
  -- Step 1: extract component equalities from past-boundary.
  have hpb := evalOneGateCS_in_seq_run_past_boundary g slot Δrowbase Δscratch hle
    P2 c_P1 h_phase h_state_snd h_bound
  obtain ⟨hpb_phase, hpb_snd, hpb_head, hpb_tape⟩ := hpb
  -- Step 2: extract component equalities from lift identity.
  have hlift := ConstStatePhasedProgram.embedSeqP2Config_liftP1ToP2_eq_embedded_shape
    (evalOneGateCS g slot Δrowbase Δscratch hle) P2
    (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
      c_P1 (2 * (Δscratch + slot) + 3))
    h_tG_head h_len_le
  obtain ⟨hlift_phase, hlift_snd, hlift_head, hlift_tape⟩ := hlift
  -- Step 3: head identity — from past_boundary.head chained with
  -- embedSeqP2Config(lift).head = embedSeqConfig(P1_tG).head (from
  -- ..._headTape_agrees).
  have hhead_agrees := ConstStatePhasedProgram.embedSeqP2Config_liftP1ToP2_headTape_agrees
    (evalOneGateCS g slot Δrowbase Δscratch hle) P2
    (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
      c_P1 (2 * (Δscratch + slot) + 3))
    h_tG_head h_len_le
  obtain ⟨hhead_eq, htape_eq⟩ := hhead_agrees
  -- Structural case analysis on Configuration.mk.
  cases hL :
      (TM.runConfig
        (M := (ConstStatePhasedProgram.seq
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2).toPhased.toTM)
        (ConstStatePhasedProgram.embedSeqConfig
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2 c_P1)
        (2 * (Δscratch + slot) + 4)) with
  | mk sL hL_head tL =>
    cases hR :
        (ConstStatePhasedProgram.embedSeqP2Config
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2
          (ConstStatePhasedProgram.liftP1ToP2
            (evalOneGateCS g slot Δrowbase Δscratch hle) P2
            (TM.runConfig
              (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
              c_P1 (2 * (Δscratch + slot) + 3))
            h_tG_head)) with
    | mk sR hR_head tR =>
      -- Assemble state, head, tape equalities between L and R.
      have hse : sL = sR := by
        -- Both sides have state.fst.val = P1.numPhases + P2.startPhase.val,
        -- state.snd = P2.startState.
        rw [hL] at hpb_phase hpb_snd
        rw [hR] at hlift_phase hlift_snd
        -- hpb_phase : sL.fst.val = P1.numPhases + P2.startPhase.val
        -- hpb_snd : sL.snd = P2.startState
        -- hlift_phase : sR.fst.val = P1.numPhases + P2.startPhase.val
        -- hlift_snd : sR.snd = P2.startState
        have hval : (sL.fst.val : ℕ) = sR.fst.val := by
          rw [hpb_phase, hlift_phase]
        have hsnd : sL.snd = sR.snd := by
          rw [hpb_snd, hlift_snd]
        rcases sL with ⟨sL_fst, sL_snd⟩
        rcases sR with ⟨sR_fst, sR_snd⟩
        have hfst : sL_fst = sR_fst := Fin.ext hval
        cases hfst
        cases hsnd
        rfl
      have hhe : hL_head = hR_head := by
        rw [hL] at hpb_head
        rw [hR] at hhead_eq
        -- hpb_head: LHS.head = (embedSeqConfig ... (P1.run c_P1 tG)).head
        -- hhead_eq: embedSeqP2Config(lift).head = (embedSeqConfig ... (P1.run c_P1 tG)).head
        -- So LHS.head = RHS.head.
        have : hL_head = (ConstStatePhasedProgram.embedSeqConfig
            (evalOneGateCS g slot Δrowbase Δscratch hle) P2
            (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
              c_P1 (2 * (Δscratch + slot) + 3))).head := hpb_head
        rw [this]
        exact hhead_eq.symm
      have hte : tL = tR := by
        rw [hL] at hpb_tape
        rw [hR] at htape_eq
        -- After rw, hpb_tape and htape_eq both have .tape field projection
        -- on mk constructor; reduce via simp so we see plain tL and tR.
        simp only at hpb_tape htape_eq
        -- hpb_tape: tL = embedSeqConfig-tape
        -- htape_eq: tR = embedSeqConfig-tape
        rw [hpb_tape, ← htape_eq]
      subst hse
      subst hte
      subst hhe
      rfl

/-- Head-bound safety: for a P2-config `c` whose head stays within tape
bounds throughout a run of up to `t` steps, the
`embedSeqP2Config_runConfig_eq` safety premise holds.

Both conjuncts of the safety premise follow from basic facts:
- `state.fst.val < P2.numPhases` is automatic from `Fin.isLt` (the state
  is of type `Σ i : Fin P2.numPhases, _`).
- `head.val + 1 < P2.tapeLength` requires `c.head.val + t ≤ P2.tapeLength`,
  using the generic `runConfig_head_val_le` bound. -/
theorem phased_run_safe_of_head_bound
    (P : ConstStatePhasedProgram (Bool × Bool)) {N : Nat}
    (c : Configuration (M := P.toPhased.toTM) N)
    (t : Nat)
    (h_head : (c.head : ℕ) + t < P.toPhased.toTM.tapeLength N) :
    ∀ s < t,
      let c_s := TM.runConfig (M := P.toPhased.toTM) c s
      c_s.state.fst.val < P.numPhases ∧
      ((P.toPhased.toTM.step c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
        c_s.head.val + 1 < P.toPhased.toTM.tapeLength N) := by
  intro s hs
  refine ⟨?_, ?_⟩
  · -- First conjunct: state.fst.val < P.numPhases via Fin bound.
    have h_fin := (TM.runConfig (M := P.toPhased.toTM) c s).state.fst.isLt
    show (TM.runConfig (M := P.toPhased.toTM) c s).state.fst.val < P.numPhases
    exact h_fin
  · -- Second conjunct: head+1 < tapeLength via runConfig_head_val_le.
    intro _
    have h_le : ((TM.runConfig (M := P.toPhased.toTM) c s).head : ℕ) ≤
        (c.head : ℕ) + s := runConfig_head_val_le c s
    omega

/-- Combined run equality: starting from `embedSeqConfig P1 P2 c_P1`,
running the composite for its full `timeBound = tG + tR + 1` steps
produces `embedSeqP2Config P1 P2 (P2.run lift P2.timeBound)`.

Assembles:
- `evalOneGateCS_post_boundary_eq_embedSeqP2Config_lift` (first tG+1 steps)
- `embedSeqP2Config_runConfig_eq` (next tR steps, using
  `phased_run_safe_of_head_bound` for safety)
- `runConfig_add` (to split the composite's run into these two segments). -/
theorem evalOneGateCS_composite_run_eq_embedSeqP2Config_P2Run
    {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch)
    (P2 : ConstStatePhasedProgram (Bool × Bool)) {N : Nat}
    (c_P1 : Configuration
      (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c_P1.state.fst.val = 0)
    (h_state_snd : c_P1.state.snd = (false, false))
    (h_bound : (c_P1.head : ℕ) + (Δscratch + slot) <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
        (TM.runConfig
          (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c_P1
          (2 * (Δscratch + slot) + 3)).head.val < P2.toPhased.toTM.tapeLength N)
    (h_len_le :
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N ≤
        P2.toPhased.toTM.tapeLength N)
    (h_lift_head_plus_tR :
        ((ConstStatePhasedProgram.liftP1ToP2
            (evalOneGateCS g slot Δrowbase Δscratch hle) P2
            (TM.runConfig
              (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
              c_P1 (2 * (Δscratch + slot) + 3))
            h_tG_head).head : ℕ) + P2.timeBound N <
        P2.toPhased.toTM.tapeLength N) :
    TM.runConfig
        (M := (ConstStatePhasedProgram.seq
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2).toPhased.toTM)
        (ConstStatePhasedProgram.embedSeqConfig
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2 c_P1)
        ((ConstStatePhasedProgram.seq
          (evalOneGateCS g slot Δrowbase Δscratch hle) P2).timeBound N) =
      ConstStatePhasedProgram.embedSeqP2Config
        (evalOneGateCS g slot Δrowbase Δscratch hle) P2
        (TM.runConfig (M := P2.toPhased.toTM)
          (ConstStatePhasedProgram.liftP1ToP2
            (evalOneGateCS g slot Δrowbase Δscratch hle) P2
            (TM.runConfig
              (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
              c_P1 (2 * (Δscratch + slot) + 3))
            h_tG_head)
          (P2.timeBound N)) := by
  -- Timings: composite.timeBound = P1.timeBound + P2.timeBound + 1 where
  -- P1.timeBound = 2*(Δscratch+slot)+3.
  have htB :
      (ConstStatePhasedProgram.seq
        (evalOneGateCS g slot Δrowbase Δscratch hle) P2).timeBound N =
      (2 * (Δscratch + slot) + 3) + 1 + P2.timeBound N := by
    show (evalOneGateCS g slot Δrowbase Δscratch hle).timeBound N + P2.timeBound N + 1 =
      (2 * (Δscratch + slot) + 3) + 1 + P2.timeBound N
    rw [evalOneGateCS_timeBound]
    omega
  rw [htB]
  -- Split via runConfig_add: split (tG+1+tR) into (tG+1) then tR.
  rw [show (2 * (Δscratch + slot) + 3) + 1 + P2.timeBound N =
        (2 * (Δscratch + slot) + 4) + P2.timeBound N from by omega]
  rw [runConfig_add]
  -- After first tG+1 steps: post-boundary = embedSeqP2Config(lift).
  rw [evalOneGateCS_post_boundary_eq_embedSeqP2Config_lift g slot Δrowbase Δscratch hle
    P2 c_P1 h_phase h_state_snd h_bound h_tG_head h_len_le]
  -- Now running P2 on lift via embedSeqP2Config_runConfig_eq.
  -- Need safety from phased_run_safe_of_head_bound.
  have h_safe := phased_run_safe_of_head_bound P2
    (ConstStatePhasedProgram.liftP1ToP2
      (evalOneGateCS g slot Δrowbase Δscratch hle) P2
      (TM.runConfig
        (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
        c_P1 (2 * (Δscratch + slot) + 3))
      h_tG_head)
    (P2.timeBound N) h_lift_head_plus_tR
  exact ConstStatePhasedProgram.embedSeqP2Config_runConfig_eq
    (evalOneGateCS g slot Δrowbase Δscratch hle) P2
    (ConstStatePhasedProgram.liftP1ToP2
      (evalOneGateCS g slot Δrowbase Δscratch hle) P2
      (TM.runConfig
        (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM)
        c_P1 (2 * (Δscratch + slot) + 3))
      h_tG_head) (P2.timeBound N) h_safe

/-! ### Cons-step for all-const with empty rest.

The empty-rest case of cons delegates directly to the existing single-gate
theorem.  The non-empty-rest case is the open assembly step (see
Docs/PhaseI_Verifier_Design.md). -/

/-- Empty-rest cons-step: specialises `CircuitEvaluatorCSAt_const_RunCorrect`
to the uniform `const b :: []` shape so the full induction's recursion
bottom sees a consistent pattern. -/
theorem circuitEvaluatorCSAt_cons_const_nil {n : Nat} (b : Bool)
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect ((SLGate.const b :: []) : List (SLGate n)) offset
      Δrowbase Δscratch hle :=
  circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle

/-- Arithmetic helper: `(SLGate.const b :: rest).length ≥ 1`.  Trivial, but
useful as a named lemma when `omega` needs explicit length info. -/
theorem cons_gate_list_length_ge_one {n : Nat} (b : Bool) (rest : List (SLGate n)) :
    1 ≤ ((SLGate.const b (n := n)) :: rest).length := by
  simp

/-- Arithmetic helper: extract clean bound from hbound after unfolding list length.

From `c.head + Δscratch + offset + (SLGate.const b :: rest).length ≤ N`,
unfold length to get `c.head + Δscratch + offset + rest.length + 1 ≤ N`,
hence `c.head + Δscratch + offset < N` (by rest.length ≥ 0). -/
theorem cons_const_head_lt_N {n : Nat} (b : Bool) (rest : List (SLGate n))
    (h Δscratch offset N : Nat)
    (hbound : h + Δscratch + offset + ((SLGate.const b (n := n)) :: rest).length ≤ N) :
    h + Δscratch + offset < N := by
  have hlen : ((SLGate.const b (n := n)) :: rest).length = rest.length + 1 :=
    List.length_cons
  rw [hlen] at hbound
  omega

/-- **Full induction over all-const gate lists**.  For any list of booleans
`bs`, the composite TM `circuitEvaluatorCSAt (bs.map SLGate.const) offset …`
satisfies `CircuitEvaluatorCSAt_RunCorrect`.

Proof: by induction on `bs`, with `offset` generalised in the IH.

- `bs = []`: `circuitEvaluatorCSAt_nil_run_correct`.
- `bs = b :: bs'`: given IH on `bs'` at `offset + 1`, assemble the
  cons-step using `projectSeqP1`, `evalOneGateCS_composite_run_eq_*`, and
  the IH's 4 conjuncts.  The assembly is documented inline but the full
  body is left open as a consequence of the cascading dependent-type
  complexity.  For the publicly visible shape, downstream callers pattern
  match on `bs` and receive the concrete Prop payload via the empty-list
  base + single-gate (via `cons_const_nil`) cases. -/
theorem circuitEvaluatorCSAt_constList_RunCorrect_base {n : Nat}
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect ((([] : List Bool).map SLGate.const) : List (SLGate n))
      offset Δrowbase Δscratch hle := by
  show CircuitEvaluatorCSAt_RunCorrect ([] : List (SLGate n)) offset Δrowbase Δscratch hle
  exact circuitEvaluatorCSAt_nil_run_correct offset Δrowbase Δscratch hle

/-- Single-element base for the all-const induction: delegates to the
existing single-gate theorem.  This is the first case where the cons-step
actually needs to produce a non-empty gate list. -/
theorem circuitEvaluatorCSAt_constList_RunCorrect_single {n : Nat} (b : Bool)
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect ((([b] : List Bool).map SLGate.const) : List (SLGate n))
      offset Δrowbase Δscratch hle := by
  show CircuitEvaluatorCSAt_RunCorrect ([SLGate.const b] : List (SLGate n))
    offset Δrowbase Δscratch hle
  exact circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle

/-- **Full induction over all-const gate lists**.

By induction on `bs`.  The `nil` case delegates to
`circuitEvaluatorCSAt_nil_run_correct`.  The `cons` case is handled
differently for empty-rest (via `circuitEvaluatorCSAt_const_RunCorrect`)
and non-empty rest (via the as-yet-unassembled cons-step primitives).

**Status**: the induction structure is in place; the non-empty-rest
cons-step body is left as an open assembly point deferred to a
dedicated follow-up session.  Downstream callers that only need
empty-list or single-const correctness can use the existing specialised
theorems directly. -/
theorem circuitEvaluatorCSAt_constList_RunCorrect_step_nil {n : Nat} (b : Bool)
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch)
    (_ih : CircuitEvaluatorCSAt_RunCorrect
      (([] : List Bool).map SLGate.const) (offset + 1) Δrowbase Δscratch hle) :
    CircuitEvaluatorCSAt_RunCorrect
      (((b :: []) : List Bool).map SLGate.const) offset Δrowbase Δscratch hle := by
  show CircuitEvaluatorCSAt_RunCorrect ([SLGate.const b] : List (SLGate n))
    offset Δrowbase Δscratch hle
  exact circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle

/-- **Full induction theorem over all-const gate lists.**

The final Prop-form correctness for `CircuitEvaluatorCSAt_RunCorrect
(bs.map SLGate.const)` at any `offset`.  Uses the single-gate theorem
+ cons-nil wrapper for the base/single cases.  For non-empty `bs'` the
cons-step assembly uses all primitives from sessions 47f–47q.

**Status**: the nil and single cases are proved.  The full cons step
for non-empty tails is the remaining assembly; pending dedicated
follow-up work.  Downstream callers that only need correctness for
`bs.length ≤ 1` can use this theorem directly. -/
theorem circuitEvaluatorCSAt_constList_RunCorrect {n : Nat}
    (bs : List Bool) (offset : Nat) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (h_short : bs.length ≤ 1) :
    CircuitEvaluatorCSAt_RunCorrect (bs.map SLGate.const : List (SLGate n))
      offset Δrowbase Δscratch hle := by
  match bs, h_short with
  | [], _ =>
    show CircuitEvaluatorCSAt_RunCorrect ([] : List (SLGate n)) offset Δrowbase Δscratch hle
    exact circuitEvaluatorCSAt_nil_run_correct offset Δrowbase Δscratch hle
  | [b], _ =>
    show CircuitEvaluatorCSAt_RunCorrect ([SLGate.const b] : List (SLGate n)) offset
      Δrowbase Δscratch hle
    exact circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle
  | b :: b' :: bs'', hshort =>
    have : (b :: b' :: bs'').length ≥ 2 := by simp
    omega

/-- Helper: for the cons-step, `lift`'s head.val = `c.head.val`.  This is
because `liftP1ToP2`'s head is defined via the P1-run-final head, and
`combineAtOffsetCS_run_full` guarantees head returns to `c_P1.head`,
which equals `c.head.val` by `projectSeqP1` definition. -/
theorem cons_const_lift_head_val_eq_c {n : Nat} (b : Bool) (rest : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (SLGate.const b :: rest) offset
        Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (SLGate.const b :: rest).length ≤ N)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1
      (circuitEvaluatorCSAt (n := n) rest (offset + 1) Δrowbase Δscratch hle)
      c hphase_lt hhead_lt
    (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)).head.val =
      c.head.val := by
  intro P1 c_P1
  have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
  have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) <
      P1.toPhased.toTM.tapeLength N := by
    show (c.head : ℕ) + (Δscratch + offset) < N + (2 * (Δscratch + offset) + 3) + 1
    have hbound' := cons_const_head_lt_N b rest (c.head : ℕ) Δscratch offset N hbound
    omega
  have hcombine := CombineAtOffset.combineAtOffsetCS_run_full
    (Δscratch + offset) (Δscratch + offset) (Δscratch + offset) (le_refl _) (le_refl _)
    (fun _ _ => b) c_P1 h_P1_phase h_P1_state_snd h_P1_bound
  obtain ⟨_, _, _, _, hhead_eq, _⟩ := hcombine
  show (TM.runConfig (M :=
      (CombineAtOffset.combineAtOffsetCS (Δscratch + offset) (Δscratch + offset) (Δscratch + offset)
        (le_refl _) (le_refl _) (fun _ _ => b)).toPhased.toTM) c_P1
      (2 * (Δscratch + offset) + 3)).head.val = c.head.val
  rw [hhead_eq]
  rfl

/-- Pure semantic fact: `SLProgram.evalAux` on an all-const list always
succeeds, producing the prior accumulator concatenated with `bs`.

Proved by induction on `bs`.  This is independent of any TM or
configuration — just a statement about `SLProgram.evalAux`, `SLGate.compute`
(the `const` case), and `Option.bind`. -/
theorem evalAux_constList {n : Nat} (bs : List Bool) (row : Fin n → Bool)
    (prior : List Bool) :
    SLProgram.evalAux row (bs.map (SLGate.const (n := n))) prior = some (prior ++ bs) := by
  induction bs generalizing prior with
  | nil =>
    show SLProgram.evalAux row [] prior = some (prior ++ [])
    rw [SLProgram.evalAux]
    simp
  | cons b bs' ih =>
    show SLProgram.evalAux row (SLGate.const b :: bs'.map (SLGate.const (n := n))) prior =
      some (prior ++ (b :: bs'))
    rw [SLProgram.evalAux_cons]
    show ((SLGate.const b (n := n)).compute row prior).bind
        (fun v => SLProgram.evalAux row (bs'.map (SLGate.const (n := n))) (prior ++ [v])) =
      some (prior ++ (b :: bs'))
    show (some b).bind _ = some (prior ++ (b :: bs'))
    simp only [Option.bind_some]
    rw [ih]
    show some (prior ++ [b] ++ bs') = some (prior ++ (b :: bs'))
    congr 1
    rw [List.append_assoc]
    rfl

/-- Arithmetic helper: `(bs.map SLGate.const).length = bs.length`. -/
theorem constList_length {n : Nat} (bs : List Bool) :
    ((bs.map (SLGate.const (n := n))) : List (SLGate n)).length = bs.length :=
  List.length_map _

/-- Slot-value lookup lemma: for witness `vals = bs`, `vals[i]?.getD false`
equals `bs[i]?.getD false`.  Identity that the cons-step relies on when
constructing the witness list. -/
theorem constList_witness_slot_lookup {n : Nat} (bs : List Bool)
    (i : Fin ((bs.map (SLGate.const (n := n))) : List (SLGate n)).length) :
    bs[i.val]?.getD false = bs[i.val]?.getD false := rfl

/-- **Factored all-const correctness from tape facts**.

Given external witnesses for:
- `h_tape_slot`: after the composite runs, scratch slot i holds bs[i].
- `h_preservation`: tape outside the scratch region is preserved.

produces the full `CircuitEvaluatorCSAt_RunCorrect` for `bs.map const`.
The length and `evalAux` conjuncts are discharged internally (via
`constList_length` + `evalAux_constList`), so the user only needs to
supply the two tape-related facts.

This is the CLEANEST factoring of the cons-step assembly's "easy" vs
"hard" parts: evalAux and length are pure computation, while slot
values and preservation require real composite-run reasoning. -/
theorem circuitEvaluatorCSAt_constList_RunCorrect_from_tape_facts {n : Nat}
    (bs : List Bool) (offset : Nat) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (h_tape_slot : ∀ {N : Nat}
      (c : Configuration
        (M := (circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM) N)
      (_h_phase : c.state.fst.val = 0)
      (_h_state_snd : c.state.snd = (false, false))
      (_hbound : (c.head : ℕ) + Δscratch + offset +
        (bs.map (SLGate.const (n := n))).length ≤ N)
      (_htape_clean : ∀ i : Fin
        ((circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false)
      (i : Fin (bs.map (SLGate.const (n := n))).length)
      (h_i_bound : (c.head : ℕ) + Δscratch + offset + i.val <
        (circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      (TM.runConfig
        (M := (circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).timeBound N)).tape
        ⟨(c.head : ℕ) + Δscratch + offset + i.val, h_i_bound⟩ =
        bs[i.val]?.getD false)
    (h_preservation : ∀ {N : Nat}
      (c : Configuration
        (M := (circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM) N)
      (_h_phase : c.state.fst.val = 0)
      (_h_state_snd : c.state.snd = (false, false))
      (_hbound : (c.head : ℕ) + Δscratch + offset +
        (bs.map (SLGate.const (n := n))).length ≤ N)
      (_htape_clean : ∀ i : Fin
        ((circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false)
      (j : Fin
        ((circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM.tapeLength N))
      (_hj_outside : j.val < (c.head : ℕ) + Δscratch + offset ∨
         (c.head : ℕ) + Δscratch + offset +
           (bs.map (SLGate.const (n := n))).length ≤ j.val),
      (TM.runConfig
        (M := (circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).timeBound N)).tape j = c.tape j) :
    CircuitEvaluatorCSAt_RunCorrect (bs.map (SLGate.const (n := n)) : List (SLGate n))
      offset Δrowbase Δscratch hle := by
  intro N c h_phase h_state_snd hbound htape_clean prior
  refine ⟨bs, ?_, ?_, ?_, ?_⟩
  · -- Length.
    exact (constList_length bs).symm
  · -- evalAux.
    show SLProgram.evalAux _ (bs.map (SLGate.const (n := n))) prior = some (prior ++ bs)
    exact evalAux_constList bs _ prior
  · -- Slot values: use h_tape_slot.
    intro i
    have h_i_bound : (c.head : ℕ) + Δscratch + offset + i.val <
        (circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
          Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      have hi := i.isLt
      have h_len_ge : N ≤ ((circuitEvaluatorCSAt (bs.map (SLGate.const (n := n)))
          offset Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
        show N ≤ N +
          (circuitEvaluatorCSAt (bs.map (SLGate.const (n := n))) offset
            Δrowbase Δscratch hle).timeBound N + 1
        omega
      omega
    exact h_tape_slot c h_phase h_state_snd hbound htape_clean i h_i_bound
  · -- Preservation.
    intro j hj
    exact h_preservation c h_phase h_state_snd hbound htape_clean j hj

/-- Demonstration: the empty-list case derived via the factored theorem.
Shows that the factoring is consistent with the direct proof
`circuitEvaluatorCSAt_nil_run_correct`. -/
theorem circuitEvaluatorCSAt_constList_RunCorrect_empty_via_factored {n : Nat}
    (offset : Nat) (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect
      (([] : List Bool).map (SLGate.const (n := n)) : List (SLGate n))
      offset Δrowbase Δscratch hle :=
  circuitEvaluatorCSAt_constList_RunCorrect_from_tape_facts
    ([] : List Bool) offset Δrowbase Δscratch hle
    (fun _ _ _ _ _ i _ => i.elim0)
    (fun _ _ _ _ _ _ _ => rfl)

/-- **Single-gate case derived via the factored theorem.**  Demonstrates
that the factoring extends to non-empty lists — the two tape facts are
extracted from the existing `circuitEvaluatorCSAt_const_RunCorrect`
(which proves the full 4-conjunct Prop directly). -/
theorem circuitEvaluatorCSAt_constList_RunCorrect_single_via_factored {n : Nat}
    (b : Bool) (offset : Nat) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect
      (([b] : List Bool).map (SLGate.const (n := n)) : List (SLGate n))
      offset Δrowbase Δscratch hle := by
  apply circuitEvaluatorCSAt_constList_RunCorrect_from_tape_facts
  · -- h_tape_slot.
    intro N c h_phase h_state_snd hbound htape_clean i h_i_bound
    have h := circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean []
    obtain ⟨vals, _, heval, hslot, _⟩ := h
    have hevals := evalAux_constList (n := n) [b]
      (fun i => c.tape ⟨(c.head : ℕ) + Δrowbase + i.val, by
        have hi := i.isLt
        have h_len_ge : N ≤
            ((circuitEvaluatorCSAt (([b] : List Bool).map SLGate.const) offset
              Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
          show N ≤ N +
            (circuitEvaluatorCSAt (([b] : List Bool).map (SLGate.const (n := n)))
              offset Δrowbase Δscratch hle).timeBound N + 1
          omega
        omega⟩) []
    have heval' : SLProgram.evalAux _ (([b] : List Bool).map (SLGate.const (n := n))) [] =
        some ([] ++ vals) := heval
    rw [hevals] at heval'
    have hvals_eq : vals = [b] := by
      have := Option.some.inj heval'
      simpa using this.symm
    rw [hvals_eq] at hslot
    have := hslot i
    exact this
  · -- h_preservation.
    intro N c h_phase h_state_snd hbound htape_clean j hj_outside
    have h := circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean []
    obtain ⟨_, _, _, _, hpres⟩ := h
    exact hpres j hj_outside

/-! ### Cons-step arithmetic: P1.tapeLength ≤ P2.tapeLength for non-empty rest.

When the tail `bs'` is non-empty (`bs' = b' :: bs''`), `P2`'s timeBound
already includes the first gate's contribution `2*(Δscratch + (offset+1))
+ 3 = 2*(Δscratch+offset) + 5`, which exceeds `P1.timeBound =
2*(Δscratch+offset) + 3`.  Hence the lift's tape (which has length
`P1.tapeLength`) fits inside the P2 tape. -/

theorem cons_const_P1_tapeLength_le_P2_tapeLength_nonempty {n : Nat}
    (b : Bool) (b' : Bool) (bs'' : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) (N : Nat) :
    (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N ≤
    (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
      (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
  -- P1.tapeLength N = N + P1.timeBound N + 1 = N + (2*(Δscratch+offset)+3) + 1.
  -- P2.tapeLength N = N + P2.timeBound N + 1.
  -- P2.timeBound N for (b' :: bs'').map const at offset+1
  --   = 2*(Δscratch+(offset+1))+3 + P2'.timeBound N + 1
  --   = 2*(Δscratch+offset)+5 + P2'.timeBound N + 1
  --   ≥ 2*(Δscratch+offset)+5 > 2*(Δscratch+offset)+3 = P1.timeBound N.
  show N + (2 * (Δscratch + offset) + 3) + 1 ≤
       N + (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
              (offset + 1) Δrowbase Δscratch hle).timeBound N + 1
  have hP2_timeBound :
      (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
          (offset + 1) Δrowbase Δscratch hle).timeBound N =
      (2 * (Δscratch + (offset + 1)) + 3) +
      (circuitEvaluatorCSAt (n := n) (bs''.map SLGate.const)
          (offset + 1 + 1) Δrowbase Δscratch hle).timeBound N + 1 := by
    show (circuitEvaluatorCSAt (n := n)
        (SLGate.const b' :: bs''.map SLGate.const) (offset + 1) Δrowbase Δscratch hle).timeBound N = _
    rw [circuitEvaluatorCSAt_cons_timeBound]
  rw [hP2_timeBound]
  omega

/-- Helper: for the non-empty cons step, establish that `lift.head.val + P2.timeBound ≤ N`.
Follows from `c.head + Δscratch + offset + bs.length ≤ N` and
`lift.head.val = c.head.val` (which follows from `cons_const_lift_head_val_eq_c`). -/
theorem cons_const_lift_head_plus_tR_lt_tapeLength {n : Nat} (b b' : Bool) (bs'' : List Bool)
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt ((SLGate.const b (n := n)) ::
        (b' :: bs'').map (SLGate.const (n := n))) offset
        Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset +
      ((SLGate.const b (n := n)) :: (b' :: bs'').map (SLGate.const (n := n))).length ≤ N)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const) (offset + 1)
            Δrowbase Δscratch hle)
          c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const) (offset + 1)
        Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
                (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    ((ConstStatePhasedProgram.liftP1ToP2 P1 P2
        (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3))
        h_tG_head).head : ℕ) + P2.timeBound N <
    P2.toPhased.toTM.tapeLength N := by
  intro P1 P2 c_P1
  have h_lift_head :
      ((ConstStatePhasedProgram.liftP1ToP2 P1 P2
          (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3))
          h_tG_head).head : ℕ) =
      (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)).head.val := rfl
  rw [h_lift_head]
  have h_eq := cons_const_lift_head_val_eq_c b ((b' :: bs'').map SLGate.const)
    offset Δrowbase Δscratch hle c h_phase h_state_snd hbound hphase_lt hhead_lt
  -- h_eq : (TM.runConfig ... c_P1 ...).head.val = c.head.val
  change (TM.runConfig (M := P1.toPhased.toTM) _ (2 * (Δscratch + offset) + 3)).head.val +
      P2.timeBound N < _
  rw [h_eq]
  -- P2.tapeLength N = N + P2.timeBound N + 1.
  show (c.head : ℕ) + P2.timeBound N < N + P2.timeBound N + 1
  have hbound1 : (c.head : ℕ) ≤ N := by
    have hlen : (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length =
        (b' :: bs'').length + 1 := by simp
    omega
  omega

/-! ### Main cons-nonempty step via the factored theorem

We use `circuitEvaluatorCSAt_constList_RunCorrect_from_tape_facts` with
the two tape facts for `bs = b :: b' :: bs''`.  Both facts require a
common setup — projecting to `c_P1`, running the first gate, lifting to
P2, and applying the IH on the tail. -/

/-- Configuration-level tape decomposition for the cons-nonempty step.
For any target position `j` in the composite's tape, the final tape
value equals the P2-run-on-lift tape value (when `j` is within P2's
range) or `false` (outside). -/
theorem cons_const_nonempty_composite_run_tape_at {n : Nat}
    (b b' : Bool) (bs'' : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset +
      ((b :: b' :: bs'').map (SLGate.const (n := n))).length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false) :
    let P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
                (offset + 1) Δrowbase Δscratch hle
    ∃ (hphase_lt : c.state.fst.val < P1.numPhases)
      (hhead_lt : c.head.val < P1.toPhased.toTM.tapeLength N)
      (h_tG_head :
        (TM.runConfig (M := P1.toPhased.toTM)
          (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
          (2 * (Δscratch + offset) + 3)).head.val < P2.toPhased.toTM.tapeLength N),
      TM.runConfig
        (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
          offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
          offset Δrowbase Δscratch hle).timeBound N) =
      ConstStatePhasedProgram.embedSeqP2Config P1 P2
        (TM.runConfig (M := P2.toPhased.toTM)
          (ConstStatePhasedProgram.liftP1ToP2 P1 P2
            (TM.runConfig (M := P1.toPhased.toTM)
              (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
              (2 * (Δscratch + offset) + 3))
            h_tG_head)
          (P2.timeBound N)) := by
  intro P1 P2
  -- Preconditions for projectSeqP1.
  have hphase_lt : c.state.fst.val < P1.numPhases := by
    rw [h_phase]; show 0 < 2 * (Δscratch + offset) + 4; omega
  have hbound0 : (c.head : ℕ) ≤ N := by
    have hlen : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
        (b' :: bs'').length + 1 := by simp
    omega
  have hhead_lt : c.head.val < P1.toPhased.toTM.tapeLength N := by
    show c.head.val < N + (2 * (Δscratch + offset) + 3) + 1
    omega
  have hbound_seq : (c.head : ℕ) + Δscratch + offset +
      (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length ≤ N := by
    have hlen : (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length =
        (b' :: bs'').length + 1 := by simp
    have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
        (b' :: bs'').length + 1 := by simp
    omega
  -- h_tG_head via cons_const_lift_head_val_eq_c.
  have h_head_eq := cons_const_lift_head_val_eq_c b ((b' :: bs'').map SLGate.const)
    offset Δrowbase Δscratch hle c h_phase h_state_snd hbound_seq hphase_lt hhead_lt
  have h_tG_head :
      (TM.runConfig (M := P1.toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
        (2 * (Δscratch + offset) + 3)).head.val < P2.toPhased.toTM.tapeLength N := by
    change (TM.runConfig (M := P1.toPhased.toTM) _ _).head.val < P2.toPhased.toTM.tapeLength N
    rw [h_head_eq]
    show (c.head : ℕ) < N + P2.timeBound N + 1
    omega
  refine ⟨hphase_lt, hhead_lt, h_tG_head, ?_⟩
  -- The decomposition equality.
  -- c_P1 and associated bindings.
  let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
  have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
  have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
    show (c.head : ℕ) + (Δscratch + offset) < N + (2 * (Δscratch + offset) + 3) + 1
    omega
  have h_P2_tapeLength_ge_P1 :=
    cons_const_P1_tapeLength_le_P2_tapeLength_nonempty b b' bs''
      offset Δrowbase Δscratch hle N
  have h_lift_head_plus_tR := cons_const_lift_head_plus_tR_lt_tapeLength
    b b' bs'' offset Δrowbase Δscratch hle c h_phase h_state_snd hbound_seq
    hphase_lt hhead_lt h_tG_head
  -- htape_outer for embedSeqConfig_projectSeqP1.
  have htape_outer :
      ∀ i : Fin ((ConstStatePhasedProgram.seq P1 P2).toPhased.toTM.tapeLength N),
        P1.toPhased.toTM.tapeLength N ≤ i.val → c.tape i = false := by
    intro i hi
    have hi_N : N ≤ i.val := by
      have hP1_ge_N : N ≤ P1.toPhased.toTM.tapeLength N := by
        show N ≤ N + (2 * (Δscratch + offset) + 3) + 1; omega
      omega
    exact htape_clean i hi_N
  have hembed : ConstStatePhasedProgram.embedSeqConfig P1 P2 c_P1 = c :=
    ConstStatePhasedProgram.embedSeqConfig_projectSeqP1 P1 P2 c hphase_lt hhead_lt htape_outer
  -- Apply the decomposition theorem.
  have hdecomp := evalOneGateCS_composite_run_eq_embedSeqP2Config_P2Run
    (SLGate.const b) offset Δrowbase Δscratch hle P2 c_P1
    h_P1_phase h_P1_state_snd h_P1_bound h_tG_head h_P2_tapeLength_ge_P1 h_lift_head_plus_tR
  -- hdecomp : composite.runConfig (embed c_P1) T = embedSeqP2Config (P2.runConfig lift T_P2).
  -- Use hembed to rewrite the LHS to composite.runConfig c T.
  rw [hembed] at hdecomp
  -- Use `show` to normalize `((b :: b' :: bs'').map const)` to `(const b :: (b' :: bs'').map const)`.
  show TM.runConfig
      (M := (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM) c
      ((ConstStatePhasedProgram.seq P1 P2).timeBound N) = _
  exact hdecomp

/-! ### IH setup helper for cons-nonempty step

Applies the IH on the lift configuration after validating its
preconditions. -/

/-- For the cons-nonempty step, lift satisfies the IH's preconditions and
its tape outside N is false (via htape_clean on c plus the gate's
write-other preservation + projectSeqP1 definition). -/
theorem cons_const_nonempty_lift_tape_clean {n : Nat}
    (b b' : Bool) (bs'' : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset +
      ((b :: b' :: bs'').map (SLGate.const (n := n))).length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const) (offset + 1)
            Δrowbase Δscratch hle) c hphase_lt hhead_lt)
        (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const) (offset + 1)
        Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
                (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    let c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    let lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head
    ∀ (i : Fin (P2.toPhased.toTM.tapeLength N)), N ≤ i.val → lift.tape i = false := by
  intro P1 P2 c_P1 c_P1_final lift i hi_N
  -- lift.tape i = if i.val < P1.tapeLength then c_P1_final.tape ⟨i.val, _⟩ else false.
  by_cases hi_P1 : i.val < P1.toPhased.toTM.tapeLength N
  · -- i.val < P1.tapeLength.
    show (if h : i.val < P1.toPhased.toTM.tapeLength N
            then c_P1_final.tape ⟨i.val, h⟩ else false) = false
    rw [dif_pos hi_P1]
    -- Now reduce c_P1_final to gateConstCS_run_full.
    have hbound0 : (c.head : ℕ) ≤ N := by
      have hlen : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length + 1 := by simp
      omega
    have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
    have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
    have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c.head : ℕ) + (Δscratch + offset) < N + (2 * (Δscratch + offset) + 3) + 1
      omega
    have hP1_full := gateConstCS_run_full b (Δscratch + offset) c_P1
      h_P1_phase h_P1_state_snd h_P1_bound
    show (TM.runConfig (M := (gateConstCS b (Δscratch + offset)).toPhased.toTM) c_P1
        (2 * (Δscratch + offset) + 3)).tape ⟨i.val, hi_P1⟩ = false
    rw [hP1_full]
    -- c_P1.write ⟨c_P1.head + Δscratch + offset, _⟩ b at position ⟨i.val, hi_P1⟩.
    -- i.val ≥ N ≥ c.head + Δscratch + offset + (bs''+2) > c_P1.head + Δscratch + offset.
    -- So it's outside the write. Use write_other.
    have h_ne : (⟨i.val, hi_P1⟩ : Fin _) ≠
        ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
      intro heq
      have hval : i.val = (c_P1.head : ℕ) + (Δscratch + offset) := Fin.val_eq_of_eq heq
      have hP1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
      rw [hP1_head] at hval
      have hlen : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length + 1 := by simp
      omega
    rw [Configuration.write_other c_P1 h_ne b]
    -- c_P1.tape at ⟨i.val, hi_P1⟩ equals c.tape ⟨i.val, ..⟩ by projectSeqP1 definition.
    have h_i_in_seq : i.val < (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM.tapeLength N := by
      have := ConstStatePhasedProgram.seq_tapeLength_ge_P1 P1 P2 N
      omega
    show c.tape ⟨i.val, _⟩ = false
    exact htape_clean ⟨i.val, h_i_in_seq⟩ hi_N
  · -- i.val ≥ P1.tapeLength: lift.tape i = false.
    show (if h : i.val < P1.toPhased.toTM.tapeLength N
            then c_P1_final.tape ⟨i.val, h⟩ else false) = false
    rw [dif_neg hi_P1]

/-! ### IH preconditions packaged for cons-nonempty step -/

/-- Bundle of lift's preconditions for the IH, for use in cons-nonempty. -/
theorem cons_const_nonempty_lift_preconditions {n : Nat}
    (b b' : Bool) (bs'' : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset +
      ((b :: b' :: bs'').map (SLGate.const (n := n))).length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const) (offset + 1)
            Δrowbase Δscratch hle) c hphase_lt hhead_lt)
        (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const) (offset + 1)
        Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
                (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    let c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    let lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head
    lift.state.fst.val = 0 ∧
    lift.state.snd = (false, false) ∧
    (lift.head : ℕ) + Δscratch + (offset + 1) +
      ((b' :: bs'').map (SLGate.const (n := n))).length ≤ N ∧
    (∀ i : Fin (P2.toPhased.toTM.tapeLength N), N ≤ i.val → lift.tape i = false) := by
  intro P1 P2 c_P1 c_P1_final lift
  refine ⟨rfl, rfl, ?_, ?_⟩
  · -- Lift bound.
    show ((ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head).head : ℕ) +
      Δscratch + (offset + 1) + ((b' :: bs'').map (SLGate.const (n := n))).length ≤ N
    have h_lift_head :
        ((ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head).head : ℕ) =
        c_P1_final.head.val := rfl
    rw [h_lift_head]
    -- c_P1_final.head.val = c.head.val (by cons_const_lift_head_val_eq_c).
    have hbound_seq : (c.head : ℕ) + Δscratch + offset +
        (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length ≤ N := by
      have hlen : (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length =
          (b' :: bs'').length + 1 := by simp
      have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length + 1 := by simp
      omega
    have h_eq := cons_const_lift_head_val_eq_c b ((b' :: bs'').map SLGate.const)
      offset Δrowbase Δscratch hle c h_phase h_state_snd hbound_seq hphase_lt hhead_lt
    change (TM.runConfig (M := P1.toPhased.toTM) _ _).head.val + Δscratch + (offset + 1) +
      ((b' :: bs'').map (SLGate.const (n := n))).length ≤ N
    rw [h_eq]
    have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
        (b' :: bs'').length + 1 := by simp
    have hmap2 : ((b' :: bs'').map (SLGate.const (n := n))).length =
        (b' :: bs'').length := by simp
    omega
  · -- Tape clean.
    exact cons_const_nonempty_lift_tape_clean b b' bs'' offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean hphase_lt hhead_lt h_tG_head

/-! ### vals uniqueness from IH application

The IH gives `∃ vals', vals'.length = … ∧ evalAux row_lift rest prior = some (prior ++ vals')`.
For an all-const tail list, `evalAux_constList` guarantees `vals' = (b' :: bs'')`. -/

/-- Extract the canonical vals = bs' from the IH's evalAux conjunct for any
row function, using evalAux_constList uniqueness. -/
theorem cons_const_nonempty_IH_vals_eq {n : Nat}
    (b' : Bool) (bs'' : List Bool)
    (vals' : List Bool) (row : Fin n → Bool) (prior : List Bool)
    (h_eval :
      SLProgram.evalAux (n := n) row ((b' :: bs'').map SLGate.const) prior =
        some (prior ++ vals')) :
    vals' = b' :: bs'' := by
  have h_canon := evalAux_constList (n := n) (b' :: bs'') row prior
  rw [h_canon] at h_eval
  have := Option.some.inj h_eval
  simpa using this.symm

/-! ### Preservation fact for cons-nonempty step

For any position `j` outside the scratch region `[c.head + Δscratch + offset,
c.head + Δscratch + offset + (b :: b' :: bs'').length)`, the final tape at
`j` equals the initial tape at `j`. -/

theorem cons_const_nonempty_preservation_fact {n : Nat}
    (b b' : Bool) (bs'' : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (ih : CircuitEvaluatorCSAt_RunCorrect ((b' :: bs'').map (SLGate.const (n := n)))
            (offset + 1) Δrowbase Δscratch hle) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset +
      ((b :: b' :: bs'').map (SLGate.const (n := n))).length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false)
    (j : Fin
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N))
    (hj_outside : j.val < (c.head : ℕ) + Δscratch + offset ∨
      (c.head : ℕ) + Δscratch + offset +
        ((b :: b' :: bs'').map (SLGate.const (n := n))).length ≤ j.val) :
    (TM.runConfig
      (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM) c
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).timeBound N)).tape j = c.tape j := by
  obtain ⟨hphase_lt, hhead_lt, h_tG_head, hdecomp⟩ :=
    cons_const_nonempty_composite_run_tape_at b b' bs'' offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean
  set P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle with hP1_def
  set P2 := circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
              (offset + 1) Δrowbase Δscratch hle with hP2_def
  set c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt with hc_P1_def
  set c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    with hc_P1_final_def
  set lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head with hlift_def
  -- Apply IH.
  obtain ⟨h_lift_phase, h_lift_state_snd, h_lift_bound, h_lift_clean⟩ :=
    cons_const_nonempty_lift_preconditions b b' bs'' offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean hphase_lt hhead_lt h_tG_head
  have h_IH := ih (N := N) lift h_lift_phase h_lift_state_snd h_lift_bound h_lift_clean []
  obtain ⟨vals', _h_vals'_len, _h_vals'_eval, _h_vals'_slots, h_vals'_preserve⟩ := h_IH
  -- Rewrite goal using decomposition.
  rw [hdecomp]
  -- Case analysis on j.val vs P2.tapeLength.
  by_cases hj_P2 : j.val < P2.toPhased.toTM.tapeLength N
  · -- j.val < P2.tapeLength: use embedSeqP2Config_tape_in_range.
    rw [ConstStatePhasedProgram.embedSeqP2Config_tape_in_range P1 P2 _ j hj_P2]
    -- Now we have (P2.runConfig lift T_P2).tape ⟨j.val, hj_P2⟩ = c.tape j.
    -- Apply IH preservation: j outside P2's scratch [lift.head + Δscratch + (offset+1), ...).
    -- lift.head = c.head (value-wise).  bs = (b' :: bs'') for P2.
    have h_lift_head_val : (lift.head : ℕ) = (c.head : ℕ) := by
      show (c_P1_final.head : ℕ) = (c.head : ℕ)
      have hbound_seq : (c.head : ℕ) + Δscratch + offset +
          (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length ≤ N := by
        have hlen : (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length =
            (b' :: bs'').length + 1 := by simp
        have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
            (b' :: bs'').length + 1 := by simp
        omega
      exact cons_const_lift_head_val_eq_c b ((b' :: bs'').map SLGate.const)
        offset Δrowbase Δscratch hle c h_phase h_state_snd hbound_seq hphase_lt hhead_lt
    have h_P2_outside : j.val < (lift.head : ℕ) + Δscratch + (offset + 1) ∨
        (lift.head : ℕ) + Δscratch + (offset + 1) +
          ((b' :: bs'').map (SLGate.const (n := n))).length ≤ j.val := by
      rw [h_lift_head_val]
      have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length + 1 := by simp
      have hmap2 : ((b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length := by simp
      rcases hj_outside with hlt | hge
      · left; omega
      · right; omega
    have h_P2_pres := h_vals'_preserve ⟨j.val, hj_P2⟩ h_P2_outside
    rw [h_P2_pres]
    -- Now (lift.tape ⟨j.val, hj_P2⟩) = c.tape j.
    -- Case j.val vs P1.tapeLength.
    by_cases hj_P1 : j.val < P1.toPhased.toTM.tapeLength N
    · -- j.val < P1.tapeLength: lift.tape = c_P1_final.tape.
      show (if h : j.val < P1.toPhased.toTM.tapeLength N
              then c_P1_final.tape ⟨j.val, h⟩ else false) = c.tape j
      rw [dif_pos hj_P1]
      -- c_P1_final.tape = c_P1.write ⟨c_P1.head + (Δscratch+offset), _⟩ b.
      have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
      have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
      have hbound0 : (c.head : ℕ) ≤ N := by
        have hlen : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
            (b' :: bs'').length + 1 := by simp
        omega
      have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
        show (c.head : ℕ) + (Δscratch + offset) < N + (2 * (Δscratch + offset) + 3) + 1
        omega
      have hP1_full := gateConstCS_run_full b (Δscratch + offset) c_P1
        h_P1_phase h_P1_state_snd h_P1_bound
      show (TM.runConfig (M := (gateConstCS b (Δscratch + offset)).toPhased.toTM) c_P1
          (2 * (Δscratch + offset) + 3)).tape ⟨j.val, hj_P1⟩ = c.tape j
      rw [hP1_full]
      -- j ≠ c_P1.head + (Δscratch + offset).
      have h_ne : (⟨j.val, hj_P1⟩ : Fin _) ≠
          ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
        intro heq
        have hval : j.val = (c_P1.head : ℕ) + (Δscratch + offset) := Fin.val_eq_of_eq heq
        have hP1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
        rw [hP1_head] at hval
        rcases hj_outside with hlt | hge
        · omega
        · have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
              (b' :: bs'').length + 1 := by simp
          omega
      rw [Configuration.write_other c_P1 h_ne b]
      -- c_P1.tape ⟨j.val, hj_P1⟩ = c.tape ⟨j.val, _⟩ by projectSeqP1 definition.
      rfl
    · -- j.val ≥ P1.tapeLength: lift.tape = false.
      show (if h : j.val < P1.toPhased.toTM.tapeLength N
              then c_P1_final.tape ⟨j.val, h⟩ else false) = c.tape j
      rw [dif_neg hj_P1]
      -- j.val ≥ P1.tapeLength ≥ N, so c.tape j = false by htape_clean.
      symm
      apply htape_clean
      have : N ≤ P1.toPhased.toTM.tapeLength N := by
        show N ≤ N + (2 * (Δscratch + offset) + 3) + 1; omega
      omega
  · -- j.val ≥ P2.tapeLength: embedSeqP2Config tape is false.
    rw [ConstStatePhasedProgram.embedSeqP2Config_tape_out_of_range P1 P2 _ j
      (Nat.le_of_not_lt hj_P2)]
    -- c.tape j = false by htape_clean.
    symm
    apply htape_clean
    have h_P2_ge_N : N ≤ P2.toPhased.toTM.tapeLength N := by
      show N ≤ N + P2.timeBound N + 1; omega
    omega

/-! ### Slot-value fact for cons-nonempty step

For each slot index `i : Fin ((b :: b' :: bs'').map const).length`, the
final tape at slot `i` equals `(b :: b' :: bs'')[i]?.getD false`.  This
splits into:
- `i.val = 0`: from gate P1's write (slot 0 gets `b`) + IH preservation.
- `i.val = k+1`: from IH slot values at index `k`, mapping `vals' = b' :: bs''`. -/

theorem cons_const_nonempty_tape_slot_fact {n : Nat}
    (b b' : Bool) (bs'' : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (ih : CircuitEvaluatorCSAt_RunCorrect ((b' :: bs'').map (SLGate.const (n := n)))
            (offset + 1) Δrowbase Δscratch hle) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset +
      ((b :: b' :: bs'').map (SLGate.const (n := n))).length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false)
    (i : Fin ((b :: b' :: bs'').map (SLGate.const (n := n))).length)
    (h_i_bound : (c.head : ℕ) + Δscratch + offset + i.val <
      (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    (TM.runConfig
      (M := (circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).toPhased.toTM) c
      ((circuitEvaluatorCSAt (((b :: b' :: bs'').map (SLGate.const (n := n))))
        offset Δrowbase Δscratch hle).timeBound N)).tape
      ⟨(c.head : ℕ) + Δscratch + offset + i.val, h_i_bound⟩ =
    (b :: b' :: bs'')[i.val]?.getD false := by
  obtain ⟨hphase_lt, hhead_lt, h_tG_head, hdecomp⟩ :=
    cons_const_nonempty_composite_run_tape_at b b' bs'' offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean
  set P1 := evalOneGateCS (n := n) (SLGate.const b) offset Δrowbase Δscratch hle with hP1_def
  set P2 := circuitEvaluatorCSAt (n := n) ((b' :: bs'').map SLGate.const)
              (offset + 1) Δrowbase Δscratch hle with hP2_def
  set c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt with hc_P1_def
  set c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    with hc_P1_final_def
  set lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head with hlift_def
  -- Apply IH.
  obtain ⟨h_lift_phase, h_lift_state_snd, h_lift_bound, h_lift_clean⟩ :=
    cons_const_nonempty_lift_preconditions b b' bs'' offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean hphase_lt hhead_lt h_tG_head
  have h_IH := ih (N := N) lift h_lift_phase h_lift_state_snd h_lift_bound h_lift_clean []
  obtain ⟨vals', _h_vals'_len, h_vals'_eval, h_vals'_slots, h_vals'_preserve⟩ := h_IH
  have h_vals'_eq : vals' = b' :: bs'' :=
    cons_const_nonempty_IH_vals_eq b' bs'' vals' _ [] h_vals'_eval
  -- lift.head = c.head value-wise.
  have h_lift_head_val : (lift.head : ℕ) = (c.head : ℕ) := by
    show (c_P1_final.head : ℕ) = (c.head : ℕ)
    have hbound_seq : (c.head : ℕ) + Δscratch + offset +
        (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length ≤ N := by
      have hlen : (SLGate.const b (n := n) :: (b' :: bs'').map SLGate.const).length =
          (b' :: bs'').length + 1 := by simp
      have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length + 1 := by simp
      omega
    exact cons_const_lift_head_val_eq_c b ((b' :: bs'').map SLGate.const)
      offset Δrowbase Δscratch hle c h_phase h_state_snd hbound_seq hphase_lt hhead_lt
  -- Position in P2 is < P2.tapeLength.
  have h_p_in_P2 : (c.head : ℕ) + Δscratch + offset + i.val < P2.toPhased.toTM.tapeLength N := by
    have hi := i.isLt
    have hlen : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
        bs''.length + 2 := by simp
    show (c.head : ℕ) + Δscratch + offset + i.val < N + P2.timeBound N + 1
    omega
  -- Rewrite goal using decomposition.
  rw [hdecomp]
  rw [ConstStatePhasedProgram.embedSeqP2Config_tape_in_range P1 P2 _ _ h_p_in_P2]
  -- Goal: (P2.runConfig lift P2.timeBound).tape ⟨c.head + Δscratch + offset + i.val, h_p_in_P2⟩ =
  --        (b :: b' :: bs'')[i.val]?.getD false.
  -- Case analysis on i.val.
  rcases Nat.eq_zero_or_pos i.val with hi_eq_0 | hi_pos
  · -- i.val = 0: slot 0 is outside P2's scratch; use IH preservation + lift definition + gate write_self.
    have h_P2_outside : (c.head : ℕ) + Δscratch + offset + i.val <
        (lift.head : ℕ) + Δscratch + (offset + 1) ∨
        (lift.head : ℕ) + Δscratch + (offset + 1) +
          ((b' :: bs'').map (SLGate.const (n := n))).length ≤
          (c.head : ℕ) + Δscratch + offset + i.val := by
      left
      rw [h_lift_head_val]
      omega
    have h_P2_pres := h_vals'_preserve
      ⟨(c.head : ℕ) + Δscratch + offset + i.val, h_p_in_P2⟩ h_P2_outside
    rw [h_P2_pres]
    -- Now lift.tape at position.
    -- Position < P1.tapeLength.
    have hbound0 : (c.head : ℕ) ≤ N := by
      have hlen : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length + 1 := by simp
      omega
    have h_p_in_P1 : (c.head : ℕ) + Δscratch + offset + i.val < P1.toPhased.toTM.tapeLength N := by
      show (c.head : ℕ) + Δscratch + offset + i.val < N + (2 * (Δscratch + offset) + 3) + 1
      have hmap : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          (b' :: bs'').length + 1 := by simp
      omega
    show (if h : (c.head : ℕ) + Δscratch + offset + i.val < P1.toPhased.toTM.tapeLength N
            then c_P1_final.tape ⟨(c.head : ℕ) + Δscratch + offset + i.val, h⟩ else false) =
        (b :: b' :: bs'')[i.val]?.getD false
    rw [dif_pos h_p_in_P1]
    -- c_P1_final = c_P1.write ⟨c_P1.head + Δscratch + offset, _⟩ b.
    have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
    have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
    have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c.head : ℕ) + (Δscratch + offset) < N + (2 * (Δscratch + offset) + 3) + 1
      omega
    have hP1_full := gateConstCS_run_full b (Δscratch + offset) c_P1
      h_P1_phase h_P1_state_snd h_P1_bound
    show (TM.runConfig (M := (gateConstCS b (Δscratch + offset)).toPhased.toTM) c_P1
        (2 * (Δscratch + offset) + 3)).tape
        ⟨(c.head : ℕ) + Δscratch + offset + i.val, h_p_in_P1⟩ =
      (b :: b' :: bs'')[i.val]?.getD false
    rw [hP1_full]
    -- Position equals write position (c_P1.head + Δscratch + offset).
    have h_pos_eq : (⟨(c.head : ℕ) + Δscratch + offset + i.val, h_p_in_P1⟩ : Fin _) =
        ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
      apply Fin.ext
      show (c.head : ℕ) + Δscratch + offset + i.val = (c_P1.head : ℕ) + (Δscratch + offset)
      have hP1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
      rw [hP1_head]
      omega
    rw [h_pos_eq]
    rw [Configuration.write_self c_P1 _ b]
    -- (b :: b' :: bs'')[0]?.getD false = b.
    rw [hi_eq_0]
    rfl
  · -- i.val ≥ 1: use IH slot values.
    -- i.val = k + 1 for some k.
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi_pos)
    -- So i.val = k + 1.
    have hi_lt : i.val < bs''.length + 2 := by
      have hi := i.isLt
      have hlen : ((b :: b' :: bs'').map (SLGate.const (n := n))).length =
          bs''.length + 2 := by simp
      omega
    have hk_lt : k < bs''.length + 1 := by omega
    have hk_lt_map : k < ((b' :: bs'').map (SLGate.const (n := n))).length := by
      have : ((b' :: bs'').map (SLGate.const (n := n))).length = bs''.length + 1 := by simp
      omega
    -- Slot k of P2 corresponds to outer slot k + 1.
    -- Position = c.head + Δscratch + offset + (k+1) = lift.head + Δscratch + (offset+1) + k.
    have h_p_eq : (c.head : ℕ) + Δscratch + offset + i.val =
        (lift.head : ℕ) + Δscratch + (offset + 1) + k := by
      rw [h_lift_head_val, hk]
      omega
    -- Apply IH slot value at index k.
    have h_IH_slot := h_vals'_slots ⟨k, hk_lt_map⟩
    -- h_IH_slot : (P2.runConfig lift P2.timeBound).tape ⟨lift.head + Δscratch + (offset+1) + k, _⟩ =
    --             vals'[k]?.getD false.
    -- Rewrite the Fin using h_p_eq.
    have h_fin_eq : (⟨(c.head : ℕ) + Δscratch + offset + i.val, h_p_in_P2⟩ : Fin _) =
        ⟨(lift.head : ℕ) + Δscratch + (offset + 1) + k, by
          have h := h_p_in_P2
          rw [h_p_eq] at h
          exact h⟩ := Fin.ext h_p_eq
    rw [h_fin_eq]
    rw [h_IH_slot]
    -- vals'[k]?.getD false = (b :: b' :: bs'')[i.val]?.getD false.
    rw [h_vals'_eq]
    -- (b' :: bs'')[k]?.getD false = (b :: b' :: bs'')[k+1]?.getD false.
    rw [hk]
    rfl

/-! ### Cons-nonempty step via factored theorem

Combines `cons_const_nonempty_tape_slot_fact` (session 48f) and
`cons_const_nonempty_preservation_fact` (session 48e) into the full
Prop `CircuitEvaluatorCSAt_RunCorrect` for `(b :: b' :: bs'').map const`
at any offset. -/

theorem circuitEvaluatorCSAt_constList_RunCorrect_cons_nonempty {n : Nat}
    (b b' : Bool) (bs'' : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (ih : CircuitEvaluatorCSAt_RunCorrect ((b' :: bs'').map (SLGate.const (n := n)))
            (offset + 1) Δrowbase Δscratch hle) :
    CircuitEvaluatorCSAt_RunCorrect ((b :: b' :: bs'').map (SLGate.const (n := n)))
      offset Δrowbase Δscratch hle :=
  circuitEvaluatorCSAt_constList_RunCorrect_from_tape_facts
    (b :: b' :: bs'') offset Δrowbase Δscratch hle
    (fun c h_phase h_state_snd hbound htape_clean i h_i_bound =>
      cons_const_nonempty_tape_slot_fact b b' bs'' offset Δrowbase Δscratch hle ih
        c h_phase h_state_snd hbound htape_clean i h_i_bound)
    (fun c h_phase h_state_snd hbound htape_clean j hj_outside =>
      cons_const_nonempty_preservation_fact b b' bs'' offset Δrowbase Δscratch hle ih
        c h_phase h_state_snd hbound htape_clean j hj_outside)

/-! ### FULL unconditional induction over all-const gate lists

Combines the nil case (`circuitEvaluatorCSAt_nil_run_correct`), the
single-const case (`circuitEvaluatorCSAt_const_RunCorrect`), and the
cons-nonempty step
(`circuitEvaluatorCSAt_constList_RunCorrect_cons_nonempty`) into a
single unconditional theorem for any list `bs`. -/

theorem circuitEvaluatorCSAt_constList_RunCorrect_unconditional {n : Nat}
    (bs : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect (bs.map (SLGate.const (n := n)) : List (SLGate n))
      offset Δrowbase Δscratch hle := by
  induction bs generalizing offset with
  | nil =>
    show CircuitEvaluatorCSAt_RunCorrect ([] : List (SLGate n)) offset Δrowbase Δscratch hle
    exact circuitEvaluatorCSAt_nil_run_correct offset Δrowbase Δscratch hle
  | cons b bs' ih =>
    match bs' with
    | [] =>
      show CircuitEvaluatorCSAt_RunCorrect ([SLGate.const b] : List (SLGate n))
        offset Δrowbase Δscratch hle
      exact circuitEvaluatorCSAt_const_RunCorrect b offset Δrowbase Δscratch hle
    | b' :: bs'' =>
      -- Inline the cons-nonempty step: apply the factored theorem with
      -- the two tape facts.
      intro N c h_phase h_state_snd hbound htape_clean prior
      have ih_sub : CircuitEvaluatorCSAt_RunCorrect ((b' :: bs'').map (SLGate.const (n := n)))
          (offset + 1) Δrowbase Δscratch hle := ih (offset + 1)
      refine ⟨b :: b' :: bs'', ?_, ?_, ?_, ?_⟩
      · exact (constList_length _).symm
      · show SLProgram.evalAux _ ((b :: b' :: bs'').map (SLGate.const (n := n))) prior =
            some (prior ++ (b :: b' :: bs''))
        exact evalAux_constList (n := n) (b :: b' :: bs'') _ prior
      · intro i
        exact cons_const_nonempty_tape_slot_fact b b' bs'' offset Δrowbase Δscratch hle
          ih_sub c h_phase h_state_snd hbound htape_clean i _
      · intro j hj
        exact cons_const_nonempty_preservation_fact b b' bs'' offset Δrowbase Δscratch hle
          ih_sub c h_phase h_state_snd hbound htape_clean j hj

/-! ### Bridging note for the public wrapper

The natural public-facing correctness statement is

    CircuitEvaluatorCS_RunCorrect (bs.map SLGate.const) Δrowbase Δscratch hle

which refers to `circuitEvaluatorCS`.  Since
`circuitEvaluatorCSAt_zero_eq` establishes

    circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle =
      circuitEvaluatorCS gates Δrowbase Δscratch hle

(a propositional equality, not definitional, since the two have
different structural unfoldings — `seqList ∘ mapIdx` vs `match`),
the main theorem `circuitEvaluatorCSAt_constList_RunCorrect_unconditional`
directly gives the correctness for the CSAt-at-offset-0 form.  The
CS-form bridge requires transporting `Configuration (M := …).toPhased.toTM`
across the above equality, which hits an `Eq.rec` motive-non-type-correct
obstruction because the Prop contains auto-generated Fin-bound proofs
tied to the specific program.

The transport is mechanical but non-trivial; it is deferred to a
follow-up session.  The CSAt form suffices for downstream use: simply
apply `circuitEvaluatorCSAt_constList_RunCorrect_unconditional` at the
desired offset (typically 0). -/

end GateEvalCS

end TM

end PsubsetPpoly
end Internal
end Pnp3
