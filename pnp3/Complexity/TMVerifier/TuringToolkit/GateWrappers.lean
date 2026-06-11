import Complexity.TMVerifier.TuringToolkit.CombineAtOffset

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

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

/-! ### Offset-parameterised evaluator (`circuitEvaluatorCSAt`)

For the multi-gate induction it is cleaner to reason about an
offset-parameterised recursion whose slots are visibly `offset, offset
+ 1, …`, rather than using `List.mapIdx` whose offset is hidden inside
a `go` helper.  `circuitEvaluatorCSAt gates offset` explicitly threads
the slot offset through the recursion.

The offset-free `circuitEvaluatorCS gates` is then defined as the
`offset = 0` specialisation of this primitive (below). -/

/-- Explicit-recursion circuit evaluator where each gate's scratch slot
is shifted by a constant `offset`.  At `offset = 0` this IS the public
`circuitEvaluatorCS` (by definitional equality — see the definition of
`circuitEvaluatorCS` below). -/
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

/-! ### Whole-circuit evaluator

`circuitEvaluatorCS gates Δrowbase Δscratch hle` evaluates every gate
in `gates` in order, storing output of gate at index `i` into
`scratch[i]`.  Defined as the `offset = 0` specialisation of
`circuitEvaluatorCSAt`, so the two forms are DEFINITIONALLY equal —
this is the session 52 integration-edge closure that lets downstream
consumers use the offset-parameterised induction machinery directly on
literal `circuitEvaluatorCS gates` without any `rw` transport or
`castConfig` gymnastics.

(An equivalent `seqList ∘ mapIdx` spelling existed historically; the
direct recursion is the canonical form consumed by the induction.) -/

def circuitEvaluatorCS {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    ConstStatePhasedProgram (Bool × Bool) :=
  circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle

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

/-! ### Generic per-gate semantic write

For any gate `g`, after running its single-gate TM program, the scratch
slot at `Δscratch + slot` holds the value of `g.compute` on the row and
the tape-resident prior.  This unifies the five gate types via
`evalOneGateCS_writes_at_dst` with the semantic condition. -/

theorem evalOneGateCS_writes_compute_result {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c_P1 : Configuration (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c_P1.state.fst.val = 0)
    (h_state_snd : c_P1.state.snd = (false, false))
    (h_bound : (c_P1.head : ℕ) + (Δscratch + slot) <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (prior : List Bool)
    (h_prior_len : prior.length = slot)
    (h_prior_match : ∀ (k : Nat) (_hk : k < prior.length)
        (hpos : (c_P1.head : ℕ) + Δscratch + k <
          (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        prior[k]? = some (c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k, hpos⟩))
    (v : Bool)
    (h_compute : g.compute
      (fun i => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
        have hi := i.isLt
        -- Δrowbase + i.val ≤ Δrowbase + n - 1 ≤ Δscratch - 1 ≤ Δscratch + slot.
        have h1 : Δrowbase + i.val ≤ Δscratch + slot := by omega
        omega⟩) prior = some v) :
    (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c_P1
        (2 * (Δscratch + slot) + 3)).tape =
      c_P1.write ⟨(c_P1.head : ℕ) + (Δscratch + slot), h_bound⟩ v := by
  match g with
  | .const b =>
    -- const compute = some b, TM writes b.
    simp only [SLGate.compute] at h_compute
    have hvb : v = b := (Option.some.inj h_compute).symm
    rw [hvb]
    exact gateConstCS_run_full b (Δscratch + slot) c_P1 h_phase h_state_snd h_bound
  | .input i =>
    -- input compute = some (row i), TM writes (row i).
    simp only [SLGate.compute] at h_compute
    have hvi : v = c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
      have hi := i.isLt
      have h1 : Δrowbase + i.val ≤ Δscratch + slot := by omega
      omega⟩ := (Option.some.inj h_compute).symm
    rw [hvi]
    obtain ⟨h_src, ht⟩ := gateInputCS_run_full i Δrowbase (Δscratch + slot)
      (by have := i.isLt; omega) c_P1 h_phase h_state_snd h_bound
    show (TM.runConfig (M := (gateInputCS i Δrowbase (Δscratch + slot) _).toPhased.toTM) c_P1
        (2 * (Δscratch + slot) + 3)).tape = _
    rw [ht]
    have h_fin_eq : (⟨(c_P1.head : ℕ) + (Δrowbase + i.val), h_src⟩ : Fin
        ((evalOneGateCS (SLGate.input i) slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)) =
        ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
          have h := h_src; omega⟩ := by
      apply Fin.ext
      show (c_P1.head : ℕ) + (Δrowbase + i.val) = (c_P1.head : ℕ) + Δrowbase + i.val
      omega
    rw [h_fin_eq]
  | .notGate k =>
    -- notGate compute = prior[k]?.map(!·).  We need compute = some v.
    -- So prior[k]? = some w with v = !w.
    simp only [SLGate.compute] at h_compute
    -- h_compute : prior[k]?.map (!·) = some v
    obtain ⟨w, hw_eq, hwv⟩ : ∃ w, prior[k]? = some w ∧ v = !w := by
      cases hp : prior[k]? with
      | none => rw [hp] at h_compute; exact Option.noConfusion h_compute
      | some w =>
        refine ⟨w, rfl, ?_⟩
        rw [hp] at h_compute
        -- h_compute : some (!w) = some v
        exact (Option.some.inj h_compute).symm
    have hk_lt : k < prior.length := by
      by_contra hge
      push_neg at hge
      have : prior[k]? = none := List.getElem?_eq_none hge
      rw [this] at hw_eq
      exact Option.noConfusion hw_eq
    have hk_lt_slot : k < slot := by
      rw [← h_prior_len]; exact hk_lt
    have hmin : min k slot = k := Nat.min_eq_left (Nat.le_of_lt hk_lt_slot)
    have h_pos_ok : (c_P1.head : ℕ) + Δscratch + k <
        (evalOneGateCS (SLGate.notGate k) slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      omega
    have h_match := h_prior_match k hk_lt h_pos_ok
    rw [hw_eq] at h_match
    have h_w_eq : w = c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_ok⟩ := Option.some.inj h_match
    obtain ⟨h_src, ht⟩ := gateNotCS_run_full (Δscratch + min k slot) (Δscratch + slot)
      (by have : min k slot ≤ slot := Nat.min_le_right _ _; omega)
      c_P1 h_phase h_state_snd h_bound
    show (TM.runConfig
      (M := (gateNotCS (Δscratch + min k slot) (Δscratch + slot) _).toPhased.toTM) c_P1
        (2 * (Δscratch + slot) + 3)).tape = _
    rw [ht]
    -- Goal: c_P1.write ⟨slot pos, _⟩ (!c_P1.tape ⟨... min k slot ..., h_src⟩) = c_P1.write ⟨...⟩ v
    rw [hwv, h_w_eq]
    -- Goal: write _ (!(tape @ min k slot)) = write _ (!(tape @ k))
    -- Identify the Fin positions.
    have h_fin_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min k slot), h_src⟩ : Fin
        ((evalOneGateCS (SLGate.notGate k) slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)) =
        ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_ok⟩ := by
      apply Fin.ext
      show (c_P1.head : ℕ) + (Δscratch + min k slot) = (c_P1.head : ℕ) + Δscratch + k
      rw [hmin]; omega
    rw [h_fin_eq]
  | .andGate k l =>
    simp only [SLGate.compute] at h_compute
    have ⟨ak, al, hpk, hpl, hvv⟩ : ∃ ak al, prior[k]? = some ak ∧ prior[l]? = some al ∧ v = (ak && al) := by
      rcases hpk : prior[k]? with _ | ak
      · rw [hpk] at h_compute; exact Option.noConfusion h_compute
      · rcases hpl : prior[l]? with _ | al
        · rw [hpk, hpl] at h_compute; exact Option.noConfusion h_compute
        · refine ⟨ak, al, rfl, rfl, ?_⟩
          rw [hpk, hpl] at h_compute
          exact (Option.some.inj h_compute).symm
    have hk_lt : k < prior.length := by
      by_contra hge
      push_neg at hge
      have : prior[k]? = none := List.getElem?_eq_none hge
      rw [this] at hpk
      exact Option.noConfusion hpk
    have hl_lt : l < prior.length := by
      by_contra hge
      push_neg at hge
      have : prior[l]? = none := List.getElem?_eq_none hge
      rw [this] at hpl
      exact Option.noConfusion hpl
    have hk_lt_slot : k < slot := by rw [← h_prior_len]; exact hk_lt
    have hl_lt_slot : l < slot := by rw [← h_prior_len]; exact hl_lt
    obtain ⟨h_src1, h_src2, ht⟩ := gateAndCS_run_full
      (Δscratch + min (min k l) slot) (Δscratch + min (max k l) slot) (Δscratch + slot)
      (by
        have hmm : min k l ≤ max k l := by
          rcases Nat.le_total k l with hkl | hkl
          · rw [min_eq_left hkl, max_eq_right hkl]; exact hkl
          · rw [min_eq_right hkl, max_eq_left hkl]; exact hkl
        omega)
      (by have : min (max k l) slot ≤ slot := Nat.min_le_right _ _; omega)
      c_P1 h_phase h_state_snd h_bound
    show (TM.runConfig (M := (gateAndCS _ _ _ _ _).toPhased.toTM) c_P1 _).tape = _
    rw [ht]
    have h_pos_k : (c_P1.head : ℕ) + Δscratch + k <
        (evalOneGateCS (SLGate.andGate k l) slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N :=
      by omega
    have h_pos_l : (c_P1.head : ℕ) + Δscratch + l <
        (evalOneGateCS (SLGate.andGate k l) slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N :=
      by omega
    have h_match_k := h_prior_match k hk_lt h_pos_k
    have h_match_l := h_prior_match l hl_lt h_pos_l
    rw [hpk] at h_match_k
    rw [hpl] at h_match_l
    have h_ak_eq : ak = c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_k⟩ :=
      Option.some.inj h_match_k
    have h_al_eq : al = c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + l, h_pos_l⟩ :=
      Option.some.inj h_match_l
    -- The TM writes (tape @ pos1) && (tape @ pos2) where
    -- pos1 = c.head + Δscratch + min(min k l) slot, pos2 = c.head + Δscratch + min(max k l) slot.
    -- We want write v = ak && al = tape @ k && tape @ l.
    rw [hvv, h_ak_eq, h_al_eq]
    rcases Nat.le_total k l with h_kl | h_kl
    · -- k ≤ l: pos1 corresponds to k, pos2 to l.
      have h_fin1_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (min k l) slot), h_src1⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_k⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (min k l) slot) = (c_P1.head : ℕ) + Δscratch + k
        have : min (min k l) slot = k := by
          rw [Nat.min_eq_left h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hk_lt_slot)
        rw [this]; omega
      have h_fin2_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (max k l) slot), h_src2⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + l, h_pos_l⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (max k l) slot) = (c_P1.head : ℕ) + Δscratch + l
        have : min (max k l) slot = l := by
          rw [Nat.max_eq_right h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hl_lt_slot)
        rw [this]; omega
      rw [h_fin1_eq, h_fin2_eq]
    · -- l ≤ k: pos1 corresponds to l, pos2 to k.  AND is commutative.
      have h_fin1_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (min k l) slot), h_src1⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + l, h_pos_l⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (min k l) slot) = (c_P1.head : ℕ) + Δscratch + l
        have : min (min k l) slot = l := by
          rw [Nat.min_eq_right h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hl_lt_slot)
        rw [this]; omega
      have h_fin2_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (max k l) slot), h_src2⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_k⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (max k l) slot) = (c_P1.head : ℕ) + Δscratch + k
        have : min (max k l) slot = k := by
          rw [Nat.max_eq_left h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hk_lt_slot)
        rw [this]; omega
      rw [h_fin1_eq, h_fin2_eq]
      rw [Bool.and_comm]
  | .orGate k l =>
    simp only [SLGate.compute] at h_compute
    have ⟨ak, al, hpk, hpl, hvv⟩ : ∃ ak al, prior[k]? = some ak ∧ prior[l]? = some al ∧ v = (ak || al) := by
      rcases hpk : prior[k]? with _ | ak
      · rw [hpk] at h_compute; exact Option.noConfusion h_compute
      · rcases hpl : prior[l]? with _ | al
        · rw [hpk, hpl] at h_compute; exact Option.noConfusion h_compute
        · refine ⟨ak, al, rfl, rfl, ?_⟩
          rw [hpk, hpl] at h_compute
          exact (Option.some.inj h_compute).symm
    have hk_lt : k < prior.length := by
      by_contra hge
      push_neg at hge
      have : prior[k]? = none := List.getElem?_eq_none hge
      rw [this] at hpk
      exact Option.noConfusion hpk
    have hl_lt : l < prior.length := by
      by_contra hge
      push_neg at hge
      have : prior[l]? = none := List.getElem?_eq_none hge
      rw [this] at hpl
      exact Option.noConfusion hpl
    have hk_lt_slot : k < slot := by rw [← h_prior_len]; exact hk_lt
    have hl_lt_slot : l < slot := by rw [← h_prior_len]; exact hl_lt
    obtain ⟨h_src1, h_src2, ht⟩ := gateOrCS_run_full
      (Δscratch + min (min k l) slot) (Δscratch + min (max k l) slot) (Δscratch + slot)
      (by
        have hmm : min k l ≤ max k l := by
          rcases Nat.le_total k l with hkl | hkl
          · rw [min_eq_left hkl, max_eq_right hkl]; exact hkl
          · rw [min_eq_right hkl, max_eq_left hkl]; exact hkl
        omega)
      (by have : min (max k l) slot ≤ slot := Nat.min_le_right _ _; omega)
      c_P1 h_phase h_state_snd h_bound
    show (TM.runConfig (M := (gateOrCS _ _ _ _ _).toPhased.toTM) c_P1 _).tape = _
    rw [ht]
    have h_pos_k : (c_P1.head : ℕ) + Δscratch + k <
        (evalOneGateCS (SLGate.orGate k l) slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N :=
      by omega
    have h_pos_l : (c_P1.head : ℕ) + Δscratch + l <
        (evalOneGateCS (SLGate.orGate k l) slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N :=
      by omega
    have h_match_k := h_prior_match k hk_lt h_pos_k
    have h_match_l := h_prior_match l hl_lt h_pos_l
    rw [hpk] at h_match_k
    rw [hpl] at h_match_l
    have h_ak_eq : ak = c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_k⟩ :=
      Option.some.inj h_match_k
    have h_al_eq : al = c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + l, h_pos_l⟩ :=
      Option.some.inj h_match_l
    rw [hvv, h_ak_eq, h_al_eq]
    rcases Nat.le_total k l with h_kl | h_kl
    · have h_fin1_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (min k l) slot), h_src1⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_k⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (min k l) slot) = (c_P1.head : ℕ) + Δscratch + k
        have : min (min k l) slot = k := by
          rw [Nat.min_eq_left h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hk_lt_slot)
        rw [this]; omega
      have h_fin2_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (max k l) slot), h_src2⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + l, h_pos_l⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (max k l) slot) = (c_P1.head : ℕ) + Δscratch + l
        have : min (max k l) slot = l := by
          rw [Nat.max_eq_right h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hl_lt_slot)
        rw [this]; omega
      rw [h_fin1_eq, h_fin2_eq]
    · have h_fin1_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (min k l) slot), h_src1⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + l, h_pos_l⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (min k l) slot) = (c_P1.head : ℕ) + Δscratch + l
        have : min (min k l) slot = l := by
          rw [Nat.min_eq_right h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hl_lt_slot)
        rw [this]; omega
      have h_fin2_eq : (⟨(c_P1.head : ℕ) + (Δscratch + min (max k l) slot), h_src2⟩ : Fin _) =
          ⟨(c_P1.head : ℕ) + Δscratch + k, h_pos_k⟩ := by
        apply Fin.ext
        show (c_P1.head : ℕ) + (Δscratch + min (max k l) slot) = (c_P1.head : ℕ) + Δscratch + k
        have : min (max k l) slot = k := by
          rw [Nat.max_eq_left h_kl]; exact Nat.min_eq_left (Nat.le_of_lt hk_lt_slot)
        rw [this]; omega
      rw [h_fin1_eq, h_fin2_eq]
      rw [Bool.or_comm]

/-! ### Generic cons-any helpers for arbitrary gates

We generalize the const-specific cons helpers from session 48 to
arbitrary gates `g : SLGate n`, using `match g with ...` to dispatch
to the corresponding `combineAtOffsetCS_run_full` instance. -/

/-- Generic head-preservation: after running evalOneGateCS g's single-gate
TM, the head returns to its initial value.  Dispatches on gate type. -/
theorem evalOneGateCS_run_preserves_head {n : Nat} (g : SLGate n) (slot : Nat)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c_P1 : Configuration (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c_P1.state.fst.val = 0)
    (h_state_snd : c_P1.state.snd = (false, false))
    (h_bound : (c_P1.head : ℕ) + (Δscratch + slot) <
        (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    (TM.runConfig (M := (evalOneGateCS g slot Δrowbase Δscratch hle).toPhased.toTM) c_P1
        (2 * (Δscratch + slot) + 3)).head.val = c_P1.head.val := by
  match g with
  | .input i =>
    obtain ⟨_, _, _, _, hhead_eq, _⟩ :=
      CombineAtOffset.combineAtOffsetCS_run_full
        (Δrowbase + i.val) (Δrowbase + i.val) (Δscratch + slot)
        (le_refl _) (by have := i.isLt; omega) (fun a _ => a)
        c_P1 h_phase h_state_snd h_bound
    exact congrArg Fin.val hhead_eq
  | .const b =>
    obtain ⟨_, _, _, _, hhead_eq, _⟩ :=
      CombineAtOffset.combineAtOffsetCS_run_full
        (Δscratch + slot) (Δscratch + slot) (Δscratch + slot)
        (le_refl _) (le_refl _) (fun _ _ => b)
        c_P1 h_phase h_state_snd h_bound
    exact congrArg Fin.val hhead_eq
  | .notGate k =>
    obtain ⟨_, _, _, _, hhead_eq, _⟩ :=
      CombineAtOffset.combineAtOffsetCS_run_full
        (Δscratch + min k slot) (Δscratch + min k slot) (Δscratch + slot)
        (le_refl _) (by have : min k slot ≤ slot := Nat.min_le_right _ _; omega)
        (fun a _ => !a) c_P1 h_phase h_state_snd h_bound
    exact congrArg Fin.val hhead_eq
  | .andGate k l =>
    obtain ⟨_, _, _, _, hhead_eq, _⟩ :=
      CombineAtOffset.combineAtOffsetCS_run_full
        (Δscratch + min (min k l) slot) (Δscratch + min (max k l) slot) (Δscratch + slot)
        (by
          have hmm : min k l ≤ max k l := by
            rcases Nat.le_total k l with hkl | hkl
            · rw [min_eq_left hkl, max_eq_right hkl]; exact hkl
            · rw [min_eq_right hkl, max_eq_left hkl]; exact hkl
          omega)
        (by have : min (max k l) slot ≤ slot := Nat.min_le_right _ _; omega)
        (· && ·) c_P1 h_phase h_state_snd h_bound
    exact congrArg Fin.val hhead_eq
  | .orGate k l =>
    obtain ⟨_, _, _, _, hhead_eq, _⟩ :=
      CombineAtOffset.combineAtOffsetCS_run_full
        (Δscratch + min (min k l) slot) (Δscratch + min (max k l) slot) (Δscratch + slot)
        (by
          have hmm : min k l ≤ max k l := by
            rcases Nat.le_total k l with hkl | hkl
            · rw [min_eq_left hkl, max_eq_right hkl]; exact hkl
            · rw [min_eq_right hkl, max_eq_left hkl]; exact hkl
          omega)
        (by have : min (max k l) slot ≤ slot := Nat.min_le_right _ _; omega)
        (· || ·) c_P1 h_phase h_state_snd h_bound
    exact congrArg Fin.val hhead_eq

/-! ### Generic arithmetic helpers for cons-any-nonempty step -/

theorem cons_any_P1_tapeLength_le_P2_tapeLength_nonempty {n : Nat}
    (g : SLGate n) (g' : SLGate n) (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) (N : Nat) :
    (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N ≤
    (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
  show N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1 ≤
       N + (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).timeBound N + 1
  rw [evalOneGateCS_timeBound]
  have hP2 :
      (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).timeBound N =
      (2 * (Δscratch + (offset + 1)) + 3) +
      (circuitEvaluatorCSAt rest' (offset + 1 + 1) Δrowbase Δscratch hle).timeBound N + 1 := by
    rw [circuitEvaluatorCSAt_cons_timeBound]
  rw [hP2]
  omega

/-- Generic lift-head-plus-tR-safety for cons-any-nonempty step. -/
theorem cons_any_lift_head_plus_tR_lt_tapeLength {n : Nat}
    (g : SLGate n) (g' : SLGate n) (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset
        Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (g :: g' :: rest').length ≤ N)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS g offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
          c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle
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
  have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
    show (c_P1.head : ℕ) + (Δscratch + offset) <
      N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound, h_c_P1_head]
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    omega
  have h_head_eq := evalOneGateCS_run_preserves_head g offset Δrowbase Δscratch hle c_P1
    h_phase h_state_snd h_P1_bound
  rw [h_head_eq, h_c_P1_head]
  show (c.head : ℕ) + P2.timeBound N < N + P2.timeBound N + 1
  have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
  omega

/-- Generic decomposition: composite.runConfig c T = embedSeqP2Config (P2.runConfig lift P2.timeBound)
for any gate g with non-empty tail g' :: rest'.  Dispatches to the unified
head-preservation helper. -/
theorem cons_any_nonempty_composite_run_tape_at {n : Nat}
    (g : SLGate n) (g' : SLGate n) (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset
        Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (g :: g' :: rest').length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false) :
    let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle
    ∃ (hphase_lt : c.state.fst.val < P1.numPhases)
      (hhead_lt : c.head.val < P1.toPhased.toTM.tapeLength N)
      (h_tG_head :
        (TM.runConfig (M := P1.toPhased.toTM)
          (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
          (2 * (Δscratch + offset) + 3)).head.val < P2.toPhased.toTM.tapeLength N),
      TM.runConfig
        (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).timeBound N) =
      ConstStatePhasedProgram.embedSeqP2Config P1 P2
        (TM.runConfig (M := P2.toPhased.toTM)
          (ConstStatePhasedProgram.liftP1ToP2 P1 P2
            (TM.runConfig (M := P1.toPhased.toTM)
              (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
              (2 * (Δscratch + offset) + 3))
            h_tG_head)
          (P2.timeBound N)) := by
  intro P1 P2
  have hphase_lt : c.state.fst.val < P1.numPhases := by
    rw [h_phase]
    show 0 < (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases
    -- numPhases ≥ 1 always (timeBound + 2 or similar).
    -- Actually, the combineAtOffsetCS has numPhases = 2*Δdst + 4. Always > 0.
    have h_tb := evalOneGateCS_timeBound g offset Δrowbase Δscratch hle 0
    -- The numPhases is always positive because combineAtOffsetCS's numPhases = 2*Δdst + 4.
    -- We can assert numPhases ≥ 1 directly from the CombineAtOffset definition.
    -- Actually, simpler: evalOneGateCS is ConstStatePhasedProgram which extends PhasedProgram
    -- which has startPhase : Fin numPhases, so numPhases ≥ 1.
    exact (evalOneGateCS g offset Δrowbase Δscratch hle).startPhase.isLt.trans_le (le_refl _) |>.trans_le (le_refl _)
    |> fun h => by
      have := (evalOneGateCS g offset Δrowbase Δscratch hle).startPhase.isLt
      omega
  have hbound0 : (c.head : ℕ) ≤ N := by
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    omega
  have hhead_lt : c.head.val < P1.toPhased.toTM.tapeLength N := by
    show c.head.val < N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    omega
  have h_head_eq :
      (TM.runConfig (M := P1.toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
        (2 * (Δscratch + offset) + 3)).head.val = c.head.val := by
    have h_P1_bound : ((ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt).head : ℕ) +
        (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c.head : ℕ) + (Δscratch + offset) <
        N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
      rw [evalOneGateCS_timeBound]
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have h := evalOneGateCS_run_preserves_head g offset Δrowbase Δscratch hle
      (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
      h_phase h_state_snd h_P1_bound
    exact h
  have h_tG_head :
      (TM.runConfig (M := P1.toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt)
        (2 * (Δscratch + offset) + 3)).head.val < P2.toPhased.toTM.tapeLength N := by
    rw [h_head_eq]
    show (c.head : ℕ) < N + P2.timeBound N + 1
    omega
  refine ⟨hphase_lt, hhead_lt, h_tG_head, ?_⟩
  -- The decomposition.
  let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
  have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
  have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
    show (c.head : ℕ) + (Δscratch + offset) <
      N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    omega
  have h_P2_tapeLength_ge_P1 :=
    cons_any_P1_tapeLength_le_P2_tapeLength_nonempty g g' rest' offset Δrowbase Δscratch hle N
  have h_lift_head_plus_tR := cons_any_lift_head_plus_tR_lt_tapeLength
    g g' rest' offset Δrowbase Δscratch hle c h_phase h_state_snd hbound
    hphase_lt hhead_lt h_tG_head
  have htape_outer :
      ∀ i : Fin ((ConstStatePhasedProgram.seq P1 P2).toPhased.toTM.tapeLength N),
        P1.toPhased.toTM.tapeLength N ≤ i.val → c.tape i = false := by
    intro i hi
    have hi_N : N ≤ i.val := by
      have hP1_ge_N : N ≤ P1.toPhased.toTM.tapeLength N := by
        show N ≤ N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
        rw [evalOneGateCS_timeBound]; omega
      omega
    exact htape_clean i hi_N
  have hembed : ConstStatePhasedProgram.embedSeqConfig P1 P2 c_P1 = c :=
    ConstStatePhasedProgram.embedSeqConfig_projectSeqP1 P1 P2 c hphase_lt hhead_lt htape_outer
  have hdecomp := evalOneGateCS_composite_run_eq_embedSeqP2Config_P2Run
    g offset Δrowbase Δscratch hle P2 c_P1
    h_P1_phase h_P1_state_snd h_P1_bound h_tG_head h_P2_tapeLength_ge_P1 h_lift_head_plus_tR
  rw [hembed] at hdecomp
  show TM.runConfig
      (M := (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM) c
      ((ConstStatePhasedProgram.seq P1 P2).timeBound N) = _
  exact hdecomp

/-- Generic lift tape-clean: lift's tape is false outside N for any gate. -/
theorem cons_any_nonempty_lift_tape_clean {n : Nat}
    (g : SLGate n) (g' : SLGate n) (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (g :: g' :: rest').length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS g offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
          c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    let c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    let lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head
    ∀ (i : Fin (P2.toPhased.toTM.tapeLength N)), N ≤ i.val → lift.tape i = false := by
  intro P1 P2 c_P1 c_P1_final lift i hi_N
  by_cases hi_P1 : i.val < P1.toPhased.toTM.tapeLength N
  · show (if h : i.val < P1.toPhased.toTM.tapeLength N
            then c_P1_final.tape ⟨i.val, h⟩ else false) = false
    rw [dif_pos hi_P1]
    have hbound0 : (c.head : ℕ) ≤ N := by
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
    have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
    have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c.head : ℕ) + (Δscratch + offset) <
        N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
      rw [evalOneGateCS_timeBound]
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    -- Use evalOneGateCS_writes_at_dst to get existence of a written bool.
    obtain ⟨b, ht⟩ := evalOneGateCS_writes_at_dst g offset Δrowbase Δscratch hle
      c_P1 h_P1_phase h_P1_state_snd h_P1_bound
    show (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)).tape
      ⟨i.val, hi_P1⟩ = false
    rw [ht]
    -- c_P1.write ⟨c_P1.head + Δscratch + offset, _⟩ b at position ⟨i.val, hi_P1⟩.
    have h_ne : (⟨i.val, hi_P1⟩ : Fin _) ≠
        ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
      intro heq
      have hval : i.val = (c_P1.head : ℕ) + (Δscratch + offset) := Fin.val_eq_of_eq heq
      have hP1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
      rw [hP1_head] at hval
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    rw [Configuration.write_other c_P1 h_ne b]
    have h_i_in_seq : i.val < (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM.tapeLength N := by
      have := ConstStatePhasedProgram.seq_tapeLength_ge_P1 P1 P2 N
      omega
    show c.tape ⟨i.val, _⟩ = false
    exact htape_clean ⟨i.val, h_i_in_seq⟩ hi_N
  · show (if h : i.val < P1.toPhased.toTM.tapeLength N
            then c_P1_final.tape ⟨i.val, h⟩ else false) = false
    rw [dif_neg hi_P1]

/-- Generic lift preconditions bundle for cons-any-nonempty. -/
theorem cons_any_nonempty_lift_preconditions {n : Nat}
    (g : SLGate n) (g' : SLGate n) (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (g :: g' :: rest').length ≤ N)
    (htape_clean : ∀ i : Fin
      ((circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      N ≤ i.val → c.tape i = false)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS g offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
          c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N) :
    let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    let c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    let lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head
    lift.state.fst.val = 0 ∧
    lift.state.snd = (false, false) ∧
    (lift.head : ℕ) + Δscratch + (offset + 1) + (g' :: rest').length ≤ N ∧
    (∀ i : Fin (P2.toPhased.toTM.tapeLength N), N ≤ i.val → lift.tape i = false) := by
  intro P1 P2 c_P1 c_P1_final lift
  -- First establish the two rfl-like facts about lift's state, dispatching on g'.
  have h_lift_phase : (ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head).state.fst.val = 0 := by
    -- lift.state.fst.val = P2.startPhase.val = 0.
    show (P2.startPhase.val : ℕ) = 0
    cases g' <;> rfl
  have h_lift_state_snd : (ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head).state.snd =
      (false, false) := by
    -- Similar reasoning: lift.state.snd = P2.startState = P1'.startState = (false, false).
    show P2.startState = (false, false)
    -- P2 = circuitEvaluatorCSAt (g' :: rest') (offset+1) = seq (evalOneGateCS g' ...) (...)
    -- seq.startState = P1'.startState = combineAtOffsetCS.startState = (false, false)
    cases g' <;> rfl
  have h_lift_bound : ((ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head).head : ℕ) +
      Δscratch + (offset + 1) + (g' :: rest').length ≤ N := by
    have h_lift_head :
        ((ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head).head : ℕ) =
        c_P1_final.head.val := rfl
    rw [h_lift_head]
    have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
    have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c_P1.head : ℕ) + (Δscratch + offset) <
        N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
      rw [evalOneGateCS_timeBound, h_c_P1_head]
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have h_head_eq := evalOneGateCS_run_preserves_head g offset Δrowbase Δscratch hle c_P1
      h_phase h_state_snd h_P1_bound
    change (TM.runConfig (M := P1.toPhased.toTM) _ _).head.val + _ + _ + _ ≤ _
    rw [h_head_eq, h_c_P1_head]
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    have hlen2 : (g' :: rest').length = rest'.length + 1 := by simp
    omega
  have h_lift_clean := cons_any_nonempty_lift_tape_clean g g' rest' offset Δrowbase Δscratch hle
    c h_phase h_state_snd hbound htape_clean hphase_lt hhead_lt h_tG_head
  exact ⟨h_lift_phase, h_lift_state_snd, h_lift_bound, h_lift_clean⟩

/-! ### Conditional correctness Prop for arbitrary gates

Parameterized by explicit `prior + vals + h_eval + h_prior_match`. -/

/-- Row function derived from a config c, at c.head + Δrowbase + i.val. -/
def rowFromConfig {n N : Nat} {M : TM}
    (c : Configuration (M := M) N) (Δrowbase : Nat)
    (h_row_bounds : ∀ (i : Fin n), (c.head : ℕ) + Δrowbase + i.val < M.tapeLength N) :
    Fin n → Bool :=
  fun i => c.tape ⟨(c.head : ℕ) + Δrowbase + i.val, h_row_bounds i⟩

/-- Helper: under the standard tapeLength bound, row function is well-defined. -/
theorem rowFromConfig_bounds {n : Nat} (gates : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (hbound : (c.head : ℕ) + Δscratch + offset + gates.length ≤ N) :
    ∀ (i : Fin n), (c.head : ℕ) + Δrowbase + i.val <
      (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
  intro i
  have hi := i.isLt
  have hlen : N ≤
      (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
    show N ≤ N + (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N + 1
    omega
  omega

/-- Nil case of the conditional correctness: empty gate list.
`circuitEvaluatorCSAt []` has timeBound=0, so the tape is unchanged. -/
theorem circuitEvaluatorCSAt_run_correct_cond_nil {n : Nat}
    (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM) N) :
    (∀ i : Fin ([] : List (SLGate n)).length,
      (TM.runConfig (M := (circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound N)).tape
        ⟨(c.head : ℕ) + Δscratch + offset + i.val, by
          exact i.elim0⟩ = ([] : List Bool)[i.val]?.getD false) ∧
    (∀ j : Fin
        ((circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      (j.val < (c.head : ℕ) + Δscratch + offset ∨
       (c.head : ℕ) + Δscratch + offset + ([] : List (SLGate n)).length ≤ j.val) →
      (TM.runConfig (M := (circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt ([] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound N)).tape j =
        c.tape j) := by
  refine ⟨?_, ?_⟩
  · intro i; exact i.elim0
  · intro j _; rfl

/-! ### Single-gate case of the conditional theorem

For a single gate g, the TM writes `v = g.compute row prior` at slot offset
and preserves all other positions. -/

/-- Conditional correctness for a single-gate list `[g]`. -/
theorem circuitEvaluatorCSAt_run_correct_cond_single {n : Nat}
    (g : SLGate n) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + ([g] : List (SLGate n)).length ≤ N)
    (htape_clean : ∀ i : Fin
        ((circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false)
    (prior : List Bool) (v : Bool)
    (h_prior_len : prior.length = offset)
    (h_prior_match : ∀ (k : Nat) (_hk : k < prior.length)
        (hpos : (c.head : ℕ) + Δscratch + k <
          (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        prior[k]? = some (c.tape ⟨(c.head : ℕ) + Δscratch + k, hpos⟩))
    (h_compute : g.compute
      (rowFromConfig c Δrowbase
        (rowFromConfig_bounds ([g] : List (SLGate n)) offset Δrowbase Δscratch hle c hbound)) prior = some v) :
    (TM.runConfig (M := (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM) c
      ((circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound N)).tape
      ⟨(c.head : ℕ) + Δscratch + offset, by
        have : (c.head : ℕ) + Δscratch + offset + 1 ≤ N := hbound
        have hlen_ge : N ≤
            (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
          show N ≤ N + (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound N + 1
          omega
        omega⟩ = v ∧
    (∀ j : Fin
        ((circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      (j.val < (c.head : ℕ) + Δscratch + offset ∨
       (c.head : ℕ) + Δscratch + offset + 1 ≤ j.val) →
      (TM.runConfig (M := (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound N)).tape j =
        c.tape j) := by
  -- Set up P1 = evalOneGateCS g, tail = idleCS (= circuitEvaluatorCSAt []).
  let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
  let tail := circuitEvaluatorCSAt (n := n) ([] : List (SLGate n)) (offset + 1) Δrowbase Δscratch hle
  -- Project c to c_P1.
  have hbound1 : (c.head : ℕ) + Δscratch + offset + 1 ≤ N := hbound
  have hphase_lt : c.state.fst.val < P1.numPhases := by
    rw [h_phase]
    show 0 < P1.numPhases
    have h_sp := P1.startPhase.isLt
    omega
  have hhead_lt : c.head.val < P1.toPhased.toTM.tapeLength N := by
    show c.head.val < N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    omega
  let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 tail c hphase_lt hhead_lt
  have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
  have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
    show (c.head : ℕ) + (Δscratch + offset) <
      N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    omega
  -- htape_outer for embedSeqConfig_projectSeqP1.
  have htape_outer :
      ∀ i : Fin ((ConstStatePhasedProgram.seq P1 tail).toPhased.toTM.tapeLength N),
        P1.toPhased.toTM.tapeLength N ≤ i.val → c.tape i = false := by
    intro i hi
    have hi_N : N ≤ i.val := by
      have hP1_ge_N : N ≤ P1.toPhased.toTM.tapeLength N := by
        show N ≤ N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
        rw [evalOneGateCS_timeBound]; omega
      omega
    exact htape_clean i hi_N
  have hembed : ConstStatePhasedProgram.embedSeqConfig P1 tail c_P1 = c :=
    ConstStatePhasedProgram.embedSeqConfig_projectSeqP1 P1 tail c hphase_lt hhead_lt htape_outer
  -- Apply past-boundary.
  have hpb := evalOneGateCS_in_seq_run_past_boundary g offset Δrowbase Δscratch hle tail
    c_P1 h_P1_phase h_P1_state_snd h_P1_bound
  obtain ⟨_, _, _, hpb_tape⟩ := hpb
  -- composite.timeBound = P1.timeBound + 1 (idleCS.timeBound = 0).
  have htimeBound :
      (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound N =
      2 * (Δscratch + offset) + 4 := by
    show (ConstStatePhasedProgram.seq P1 tail).timeBound N = _
    rw [ConstStatePhasedProgram.seq_timeBound]
    show (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 0 + 1 = _
    rw [evalOneGateCS_timeBound]
  -- Transport hpb_tape via hembed.
  have h_run_eq : (TM.runConfig (M := (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM) c
      ((circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).timeBound N)).tape =
      (ConstStatePhasedProgram.embedSeqConfig P1 tail
        (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3))).tape := by
    rw [htimeBound]
    show (TM.runConfig (M := (ConstStatePhasedProgram.seq P1 tail).toPhased.toTM) c _).tape = _
    exact hembed ▸ hpb_tape
  -- Apply evalOneGateCS_writes_compute_result to get slot 0 value.
  have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
  -- We need h_prior_match on c_P1.  Since c_P1.tape = c.tape at positions < P1.tapeLength,
  -- and all positions in [c_P1.head + Δscratch, c_P1.head + Δscratch + offset) are <
  -- P1.tapeLength, the match carries over.
  have h_prior_match_P1 : ∀ (k : Nat) (hk : k < prior.length)
      (hpos : (c_P1.head : ℕ) + Δscratch + k < P1.toPhased.toTM.tapeLength N),
      prior[k]? = some (c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k, hpos⟩) := by
    intro k hk hpos
    have hk_lt_offset : k < offset := by rw [h_prior_len] at hk; exact hk
    have hpos_composite : (c.head : ℕ) + Δscratch + k <
        (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      have : (c.head : ℕ) + Δscratch + k < (c.head : ℕ) + Δscratch + offset := by omega
      have hlen_ge : (c.head : ℕ) + Δscratch + offset ≤
          (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
        have : (c.head : ℕ) + Δscratch + offset + 1 ≤ N := hbound
        have hlen : N ≤
            (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
          show N ≤ N + _ + 1; omega
        omega
      omega
    have := h_prior_match k hk hpos_composite
    -- c_P1.tape ⟨c_P1.head + Δscratch + k, hpos⟩ = c.tape ⟨c.head + Δscratch + k, hpos_composite⟩
    -- by projectSeqP1 definition.
    rw [this]
    rfl
  -- Apply evalOneGateCS_writes_compute_result.
  have h_write := evalOneGateCS_writes_compute_result g offset Δrowbase Δscratch hle
    c_P1 h_P1_phase h_P1_state_snd h_P1_bound prior h_prior_len h_prior_match_P1 v
    (by
      -- h_compute is about rowFromConfig c.  We need the same for c_P1.
      -- rowFromConfig c_P1 Δrowbase = rowFromConfig c Δrowbase (same values for same positions).
      have h_row_eq : (rowFromConfig c Δrowbase
          (rowFromConfig_bounds ([g] : List (SLGate n)) offset Δrowbase Δscratch hle c hbound)) =
          fun (i : Fin n) => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
            have hi := i.isLt
            show _ < P1.toPhased.toTM.tapeLength N
            have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
            rw [h_c_P1_head]
            have : (c.head : ℕ) + Δrowbase + i.val < P1.toPhased.toTM.tapeLength N := by
              show (c.head : ℕ) + Δrowbase + i.val <
                N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
              rw [evalOneGateCS_timeBound]
              omega
            exact this⟩ := by
        funext i
        -- Values are the same since c_P1.tape = c.tape at those positions.
        show c.tape _ = c_P1.tape _
        rfl
      rw [h_row_eq] at h_compute
      exact h_compute)
  -- Combine: tape at slot 0 = v.
  refine ⟨?_, ?_⟩
  · -- Slot value.
    have h_tape_at_slot : (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)).tape
        ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ = v := by
      rw [h_write]
      exact Configuration.write_self c_P1 _ v
    -- Now use h_run_eq to push to composite.
    have h_composite_tape := congrFun h_run_eq ⟨(c.head : ℕ) + Δscratch + offset, by
      have hlen_ge : N ≤
          (circuitEvaluatorCSAt ([g] : List (SLGate n)) offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
        show N ≤ N + _ + 1; omega
      omega⟩
    rw [h_composite_tape]
    -- embedSeqConfig.tape at c.head + Δscratch + offset = c_P1_final.tape at same position.
    have h_pos_in_P1 : (c.head : ℕ) + Δscratch + offset < P1.toPhased.toTM.tapeLength N := by
      show (c.head : ℕ) + Δscratch + offset <
        N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
      rw [evalOneGateCS_timeBound]
      omega
    rw [ConstStatePhasedProgram.embedSeqConfig_tape_in_range P1 tail _ _ h_pos_in_P1]
    show (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)).tape
      ⟨(c.head : ℕ) + Δscratch + offset, h_pos_in_P1⟩ = v
    have h_fin_eq : (⟨(c.head : ℕ) + Δscratch + offset, h_pos_in_P1⟩ : Fin _) =
        ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
      apply Fin.ext
      show (c.head : ℕ) + Δscratch + offset = (c_P1.head : ℕ) + (Δscratch + offset)
      rw [h_c_P1_head]; omega
    rw [h_fin_eq]
    exact h_tape_at_slot
  · -- Preservation.
    intro j hj
    have h_composite_tape := congrFun h_run_eq j
    rw [h_composite_tape]
    by_cases hj_P1 : j.val < P1.toPhased.toTM.tapeLength N
    · rw [ConstStatePhasedProgram.embedSeqConfig_tape_in_range P1 tail _ j hj_P1]
      -- c_P1_final.tape at j = c_P1.write (at slot offset) v at j.
      rw [h_write]
      -- j ≠ c_P1.head + (Δscratch + offset).
      have h_ne : (⟨j.val, hj_P1⟩ : Fin _) ≠
          ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
        intro heq
        have hval : j.val = (c_P1.head : ℕ) + (Δscratch + offset) := Fin.val_eq_of_eq heq
        rw [h_c_P1_head] at hval
        rcases hj with hlt | hge
        · omega
        · omega
      rw [Configuration.write_other c_P1 h_ne v]
      rfl
    · rw [ConstStatePhasedProgram.embedSeqConfig_tape_out_of_range P1 tail _ j
        (Nat.le_of_not_lt hj_P1)]
      symm
      apply htape_clean
      have hP1_ge_N : N ≤ P1.toPhased.toTM.tapeLength N := by
        show N ≤ N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
        omega
      omega

/-! ### evalAux prior-prefix preservation

Proves the key structural fact: `evalAux row gates prior = some r` implies
`r = prior ++ values` for some `values` with `values.length = gates.length`. -/

theorem SLProgram_evalAux_prior_prefix {n : Nat} :
    ∀ (gates : List (SLGate n)) (row : Fin n → Bool) (prior r : List Bool),
      SLProgram.evalAux row gates prior = some r →
      ∃ values, r = prior ++ values ∧ values.length = gates.length := by
  intro gates
  induction gates with
  | nil =>
    intro row prior r h
    refine ⟨[], ?_, rfl⟩
    show r = prior ++ []
    simp [SLProgram.evalAux] at h
    rw [← h]
    simp
  | cons g rest ih =>
    intro row prior r h
    show ∃ values, r = prior ++ values ∧ values.length = rest.length + 1
    rw [SLProgram.evalAux] at h
    rcases hc : g.compute row prior with _ | v
    · rw [hc] at h; exact absurd h (by simp)
    · rw [hc] at h
      -- h : evalAux row rest (prior ++ [v]) = some r
      obtain ⟨values_rest, hr, hvr_len⟩ := ih row (prior ++ [v]) r h
      refine ⟨v :: values_rest, ?_, ?_⟩
      · show r = prior ++ (v :: values_rest)
        rw [hr]; simp
      · show (v :: values_rest).length = rest.length + 1
        simp [hvr_len]

/-- Extract the cons-step structure from evalAux on `g :: rest`. -/
theorem SLProgram_evalAux_cons_split {n : Nat} (row : Fin n → Bool)
    (g : SLGate n) (rest : List (SLGate n)) (prior vals : List Bool)
    (h_eval : SLProgram.evalAux row (g :: rest) prior = some (prior ++ vals)) :
    ∃ (v : Bool) (vals_rest : List Bool),
      g.compute row prior = some v ∧
      vals = v :: vals_rest ∧
      vals_rest.length = rest.length ∧
      SLProgram.evalAux row rest (prior ++ [v]) = some ((prior ++ [v]) ++ vals_rest) := by
  rw [SLProgram.evalAux] at h_eval
  rcases hc : g.compute row prior with _ | v
  · rw [hc] at h_eval; exact absurd h_eval (by simp)
  · rw [hc] at h_eval
    -- h_eval : evalAux row rest (prior ++ [v]) = some (prior ++ vals)
    obtain ⟨values_rest, hr_eq, hvr_len⟩ := SLProgram_evalAux_prior_prefix rest row
      (prior ++ [v]) (prior ++ vals) h_eval
    -- hr_eq : prior ++ vals = (prior ++ [v]) ++ values_rest.
    -- Cancel prior on the left to get vals = [v] ++ values_rest = v :: values_rest.
    have h_vals_eq : vals = v :: values_rest := by
      have h2 : prior ++ vals = prior ++ (v :: values_rest) := by
        rw [hr_eq]; simp
      exact List.append_cancel_left h2
    refine ⟨v, values_rest, rfl, h_vals_eq, hvr_len, ?_⟩
    rw [hr_eq] at h_eval
    exact h_eval

/-! ### Row-function consistency for lift

For any gate g, the lift configuration (after running g on c_P1) has
the same tape values at row positions as the original c.  This is because
gates only write to scratch slot (not row region), and the lift carries
c_P1_final's tape which equals c's tape at row positions. -/

theorem cons_any_row_lift_eq_c {n : Nat} (g : SLGate n) (g' : SLGate n)
    (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (g :: g' :: rest').length ≤ N)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS g offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
          c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (prior : List Bool) (v : Bool)
    (h_prior_len : prior.length = offset)
    (h_prior_match : ∀ (k : Nat) (_hk : k < prior.length)
        (hpos : (c.head : ℕ) + Δscratch + k <
          (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        prior[k]? = some (c.tape ⟨(c.head : ℕ) + Δscratch + k, hpos⟩))
    (h_compute : g.compute
      (rowFromConfig c Δrowbase
        (rowFromConfig_bounds (g :: g' :: rest') offset Δrowbase Δscratch hle c hbound))
      prior = some v) :
    let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    let c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    let lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head
    ∀ (i : Fin n)
      (h_row : (lift.head : ℕ) + Δrowbase + i.val < P2.toPhased.toTM.tapeLength N),
      lift.tape ⟨(lift.head : ℕ) + Δrowbase + i.val, h_row⟩ =
        c.tape ⟨(c.head : ℕ) + Δrowbase + i.val, by
          have h_len_ge : N ≤
              (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
            show N ≤ N + _ + 1; omega
          omega⟩ := by
  intro P1 P2 c_P1 c_P1_final lift
  intro i h_row
  have h_lift_head : (lift.head : ℕ) = (c.head : ℕ) := by
    show (c_P1_final.head : ℕ) = (c.head : ℕ)
    have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
    have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c_P1.head : ℕ) + (Δscratch + offset) <
        N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
      rw [evalOneGateCS_timeBound, h_c_P1_head]
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have := evalOneGateCS_run_preserves_head g offset Δrowbase Δscratch hle c_P1
      h_phase h_state_snd h_P1_bound
    rw [this, h_c_P1_head]
  have hi := i.isLt
  have h_pos_in_P1 : (c.head : ℕ) + Δrowbase + i.val < P1.toPhased.toTM.tapeLength N := by
    show (c.head : ℕ) + Δrowbase + i.val <
      N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    omega
  -- lift.tape = if < P1.tapeLength then c_P1_final.tape else false.
  -- Use Fin.ext to change the Fin to use c.head instead of lift.head.
  have h_fin_eq : (⟨(lift.head : ℕ) + Δrowbase + i.val, h_row⟩ :
      Fin (P2.toPhased.toTM.tapeLength N)) =
      ⟨(c.head : ℕ) + Δrowbase + i.val, by rw [← h_lift_head]; exact h_row⟩ := by
    apply Fin.ext
    show (lift.head : ℕ) + Δrowbase + i.val = (c.head : ℕ) + Δrowbase + i.val
    rw [h_lift_head]
  rw [h_fin_eq]
  -- Now lift.tape ⟨c.head + Δrowbase + i, _⟩ with position < P1.tapeLength.
  show (if h : _ < P1.toPhased.toTM.tapeLength N
        then c_P1_final.tape ⟨_, h⟩ else false) = _
  rw [dif_pos h_pos_in_P1]
  -- Now c_P1_final.tape = c_P1.write ⟨slot offset, _⟩ v.
  have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
  have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
    show (c_P1.head : ℕ) + (Δscratch + offset) <
      N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
    rw [h_c_P1_head]
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    omega
  have h_prior_match_P1 : ∀ (k' : Nat) (hk' : k' < prior.length)
      (hpos' : (c_P1.head : ℕ) + Δscratch + k' < P1.toPhased.toTM.tapeLength N),
      prior[k']? = some (c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k', hpos'⟩) := by
    intro k' hk' hpos'
    have hk'_lt_offset : k' < offset := by rw [h_prior_len] at hk'; exact hk'
    have hpos_composite : (c.head : ℕ) + Δscratch + k' <
        (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      have hlen_ge : N ≤
          (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
        show N ≤ N + _ + 1; omega
      have hlen2 : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have := h_prior_match k' hk' hpos_composite
    rw [this]
    rfl
  have h_row_eq :
      (fun (i : Fin n) => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
        have hi := i.isLt
        show _ < P1.toPhased.toTM.tapeLength N
        have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
        rw [h_c_P1_head]
        show (c.head : ℕ) + Δrowbase + i.val <
          N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
        rw [evalOneGateCS_timeBound]
        omega⟩) =
      (rowFromConfig c Δrowbase
        (rowFromConfig_bounds (g :: g' :: rest') offset Δrowbase Δscratch hle c hbound)) := by
    funext i
    show c_P1.tape _ = c.tape _
    rfl
  have h_compute_P1 : g.compute
      (fun (i : Fin n) => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
        have hi := i.isLt
        show _ < P1.toPhased.toTM.tapeLength N
        have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
        rw [h_c_P1_head]
        show (c.head : ℕ) + Δrowbase + i.val <
          N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
        rw [evalOneGateCS_timeBound]
        omega⟩) prior = some v := by
    rw [h_row_eq]; exact h_compute
  have h_write := evalOneGateCS_writes_compute_result g offset Δrowbase Δscratch hle
    c_P1 h_P1_phase h_P1_state_snd h_P1_bound prior h_prior_len h_prior_match_P1 v h_compute_P1
  rw [h_write]
  -- c_P1.write at ⟨c_P1.head + Δscratch + offset, _⟩ v at position ⟨c.head + Δrowbase + i.val, h_pos_in_P1⟩.
  -- The position Δrowbase + i.val ≤ Δrowbase + n - 1 < Δrowbase + n ≤ Δscratch ≤ Δscratch + offset.
  -- So position ≠ write location.
  have h_ne : (⟨(c.head : ℕ) + Δrowbase + i.val, h_pos_in_P1⟩ : Fin _) ≠
      ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
    intro heq
    have hval : (c.head : ℕ) + Δrowbase + i.val = (c_P1.head : ℕ) + (Δscratch + offset) :=
      Fin.val_eq_of_eq heq
    have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
    rw [h_c_P1_head] at hval
    omega
  rw [Configuration.write_other c_P1 h_ne v]
  -- c_P1.tape = c.tape (by projectSeqP1).
  rfl

/-! ### h_prior_match extension for lift

Extends `h_prior_match` from `prior` (at c's scratch slots [0, offset))
to `prior ++ [v]` (at lift's scratch slots [0, offset + 1)) after
applying the gate g. -/

theorem cons_any_h_prior_match_lift {n : Nat} (g : SLGate n) (g' : SLGate n)
    (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (g :: g' :: rest').length ≤ N)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS g offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
          c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (prior : List Bool) (v : Bool)
    (h_prior_len : prior.length = offset)
    (h_prior_match : ∀ (k : Nat) (_hk : k < prior.length)
        (hpos : (c.head : ℕ) + Δscratch + k <
          (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        prior[k]? = some (c.tape ⟨(c.head : ℕ) + Δscratch + k, hpos⟩))
    (h_compute : g.compute
      (rowFromConfig c Δrowbase
        (rowFromConfig_bounds (g :: g' :: rest') offset Δrowbase Δscratch hle c hbound))
      prior = some v) :
    let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    let c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    let lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head
    ∀ (k : Nat) (_hk : k < (prior ++ [v]).length)
      (hpos : (lift.head : ℕ) + Δscratch + k < P2.toPhased.toTM.tapeLength N),
      (prior ++ [v])[k]? = some (lift.tape ⟨(lift.head : ℕ) + Δscratch + k, hpos⟩) := by
  intro P1 P2 c_P1 c_P1_final lift
  intro k hk hpos
  have h_lift_head : (lift.head : ℕ) = (c.head : ℕ) := by
    show (c_P1_final.head : ℕ) = (c.head : ℕ)
    have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
    have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c_P1.head : ℕ) + (Δscratch + offset) <
        N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
      rw [evalOneGateCS_timeBound, h_c_P1_head]
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have := evalOneGateCS_run_preserves_head g offset Δrowbase Δscratch hle c_P1
      h_phase h_state_snd h_P1_bound
    rw [this, h_c_P1_head]
  have hk_total : k < offset + 1 := by
    have hl : (prior ++ [v]).length = prior.length + 1 := by simp
    rw [hl, h_prior_len] at hk
    exact hk
  have h_pos_in_P1 : (c.head : ℕ) + Δscratch + k < P1.toPhased.toTM.tapeLength N := by
    show (c.head : ℕ) + Δscratch + k <
      N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    omega
  -- Use Fin.ext to change the Fin to c.head + Δscratch + k.
  have h_fin_eq : (⟨(lift.head : ℕ) + Δscratch + k, hpos⟩ :
      Fin (P2.toPhased.toTM.tapeLength N)) =
      ⟨(c.head : ℕ) + Δscratch + k, by rw [← h_lift_head]; exact hpos⟩ := by
    apply Fin.ext
    show (lift.head : ℕ) + Δscratch + k = (c.head : ℕ) + Δscratch + k
    rw [h_lift_head]
  rw [h_fin_eq]
  -- Now lift.tape at ⟨c.head + Δscratch + k, _⟩ with position < P1.tapeLength.
  show (prior ++ [v])[k]? = some
    (if h : (c.head : ℕ) + Δscratch + k < P1.toPhased.toTM.tapeLength N
      then c_P1_final.tape ⟨(c.head : ℕ) + Δscratch + k, h⟩ else false)
  rw [dif_pos h_pos_in_P1]
  -- c_P1_final.tape = c_P1.write ⟨c_P1.head + Δscratch + offset, _⟩ v.
  have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
  have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
  have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
    show (c_P1.head : ℕ) + (Δscratch + offset) <
      N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
    rw [evalOneGateCS_timeBound]
    have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
    rw [h_c_P1_head]
    have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
    omega
  have h_prior_match_P1 : ∀ (k' : Nat) (hk' : k' < prior.length)
      (hpos' : (c_P1.head : ℕ) + Δscratch + k' < P1.toPhased.toTM.tapeLength N),
      prior[k']? = some (c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k', hpos'⟩) := by
    intro k' hk' hpos'
    have hk'_lt_offset : k' < offset := by rw [h_prior_len] at hk'; exact hk'
    have hpos_composite : (c.head : ℕ) + Δscratch + k' <
        (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      have hlen_ge : N ≤
          (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
        show N ≤ N + _ + 1; omega
      have hlen2 : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have := h_prior_match k' hk' hpos_composite
    rw [this]
    rfl
  have h_row_eq :
      (fun (i : Fin n) => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
        have hi := i.isLt
        show _ < P1.toPhased.toTM.tapeLength N
        have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
        rw [h_c_P1_head]
        show (c.head : ℕ) + Δrowbase + i.val <
          N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
        rw [evalOneGateCS_timeBound]
        omega⟩) =
      (rowFromConfig c Δrowbase
        (rowFromConfig_bounds (g :: g' :: rest') offset Δrowbase Δscratch hle c hbound)) := by
    funext i
    show c_P1.tape _ = c.tape _
    rfl
  have h_compute_P1 : g.compute
      (fun (i : Fin n) => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
        have hi := i.isLt
        show _ < P1.toPhased.toTM.tapeLength N
        have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
        rw [h_c_P1_head]
        show (c.head : ℕ) + Δrowbase + i.val <
          N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
        rw [evalOneGateCS_timeBound]
        omega⟩) prior = some v := by
    rw [h_row_eq]; exact h_compute
  have h_write := evalOneGateCS_writes_compute_result g offset Δrowbase Δscratch hle
    c_P1 h_P1_phase h_P1_state_snd h_P1_bound prior h_prior_len h_prior_match_P1 v h_compute_P1
  show (prior ++ [v])[k]? = some
    (c_P1_final.tape ⟨(c.head : ℕ) + Δscratch + k, h_pos_in_P1⟩)
  rw [h_write]
  -- Case k < offset vs k = offset.
  by_cases hk_lt_offset : k < offset
  · -- prior[k]? = prior[k]? (from list append lemma).
    have h_list_get : (prior ++ [v])[k]? = prior[k]? := by
      rw [List.getElem?_append_left]; rw [h_prior_len]; exact hk_lt_offset
    rw [h_list_get]
    -- Position ≠ write location (offset).
    have h_ne : (⟨(c.head : ℕ) + Δscratch + k, h_pos_in_P1⟩ : Fin _) ≠
        ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
      intro heq
      have hval : (c.head : ℕ) + Δscratch + k = (c_P1.head : ℕ) + (Δscratch + offset) :=
        Fin.val_eq_of_eq heq
      have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
      rw [h_c_P1_head] at hval
      omega
    rw [Configuration.write_other c_P1 h_ne v]
    -- c_P1.tape ⟨c.head + Δscratch + k, _⟩ = c.tape ⟨c.head + Δscratch + k, _⟩.
    -- Use h_prior_match_P1.
    show prior[k]? = some (c_P1.tape ⟨(c.head : ℕ) + Δscratch + k, h_pos_in_P1⟩)
    have := h_prior_match_P1 k (by rw [h_prior_len]; exact hk_lt_offset) (by
      have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
      rw [h_c_P1_head]; exact h_pos_in_P1)
    rw [this]
    rfl
  · -- k = offset.
    have hk_eq : k = offset := by omega
    subst hk_eq
    -- Position = c.head + Δscratch + k = c_P1.head + Δscratch + k.
    have h_pos_eq : (⟨(c.head : ℕ) + Δscratch + k, h_pos_in_P1⟩ : Fin _) =
        ⟨(c_P1.head : ℕ) + (Δscratch + k), h_P1_bound⟩ := by
      apply Fin.ext
      show (c.head : ℕ) + Δscratch + k = (c_P1.head : ℕ) + (Δscratch + k)
      have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
      rw [h_c_P1_head]; omega
    rw [h_pos_eq]
    rw [Configuration.write_self c_P1 _ v]
    -- (prior ++ [v])[k]? = some v (k = prior.length).
    have h_list_get : (prior ++ [v])[k]? = some v := by
      rw [List.getElem?_append_right]
      · rw [h_prior_len]; simp
      · rw [h_prior_len]
    exact h_list_get

/-! ### rowFromConfig consistency between c and lift

Establishes that `rowFromConfig lift Δrowbase (bounds')` equals
`rowFromConfig c Δrowbase (bounds)` when gate g is run. -/

theorem cons_any_rowFromConfig_lift_eq {n : Nat} (g : SLGate n) (g' : SLGate n)
    (rest' : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + (g :: g' :: rest').length ≤ N)
    (hphase_lt : c.state.fst.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).numPhases)
    (hhead_lt : c.head.val <
      (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (h_tG_head :
      (TM.runConfig
        (M := (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM)
        (ConstStatePhasedProgram.projectSeqP1
          (evalOneGateCS g offset Δrowbase Δscratch hle)
          (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
          c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3)).head.val <
      (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)
    (prior : List Bool) (v : Bool)
    (h_prior_len : prior.length = offset)
    (h_prior_match : ∀ (k : Nat) (_hk : k < prior.length)
        (hpos : (c.head : ℕ) + Δscratch + k <
          (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        prior[k]? = some (c.tape ⟨(c.head : ℕ) + Δscratch + k, hpos⟩))
    (h_compute : g.compute
      (rowFromConfig c Δrowbase
        (rowFromConfig_bounds (g :: g' :: rest') offset Δrowbase Δscratch hle c hbound))
      prior = some v)
    (h_lift_bound : ((ConstStatePhasedProgram.liftP1ToP2
        (evalOneGateCS g offset Δrowbase Δscratch hle)
        (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
        (TM.runConfig (M := (evalOneGateCS g offset Δrowbase Δscratch hle).toPhased.toTM)
          (ConstStatePhasedProgram.projectSeqP1
            (evalOneGateCS g offset Δrowbase Δscratch hle)
            (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle)
            c hphase_lt hhead_lt) (2 * (Δscratch + offset) + 3))
        h_tG_head).head : ℕ) + Δscratch + (offset + 1) +
        ((g' :: rest').map id).length ≤ N) :
    let P1 := evalOneGateCS g offset Δrowbase Δscratch hle
    let P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle
    let c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt
    let c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    let lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head
    (rowFromConfig lift Δrowbase
        (rowFromConfig_bounds (g' :: rest') (offset + 1) Δrowbase Δscratch hle lift
          (by simpa using h_lift_bound))) =
      (rowFromConfig c Δrowbase
        (rowFromConfig_bounds (g :: g' :: rest') offset Δrowbase Δscratch hle c hbound)) := by
  intro P1 P2 c_P1 c_P1_final lift
  funext i
  show lift.tape _ = c.tape _
  have h_row_eq := cons_any_row_lift_eq_c g g' rest' offset Δrowbase Δscratch hle
    c h_phase h_state_snd hbound hphase_lt hhead_lt h_tG_head prior v h_prior_len
    h_prior_match h_compute i (by
      have hi := i.isLt
      have h_lift_head_val : (lift.head : ℕ) = (c.head : ℕ) := by
        show (c_P1_final.head : ℕ) = (c.head : ℕ)
        have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
        have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
          show (c_P1.head : ℕ) + (Δscratch + offset) <
            N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
          rw [evalOneGateCS_timeBound, h_c_P1_head]
          have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
          omega
        have := evalOneGateCS_run_preserves_head g offset Δrowbase Δscratch hle c_P1
          h_phase h_state_snd h_P1_bound
        rw [this, h_c_P1_head]
      show (lift.head : ℕ) + Δrowbase + i.val < P2.toPhased.toTM.tapeLength N
      rw [h_lift_head_val]
      show (c.head : ℕ) + Δrowbase + i.val <
        N + (circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle).timeBound N + 1
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega)
  exact h_row_eq

/-! ### Mathematical formulation: full conditional correctness

We define the correctness predicate `CircuitEvaluatorCSAt_CondCorrect gates`
once, then prove `∀ gates, CircuitEvaluatorCSAt_CondCorrect gates` by
well-founded recursion on `gates.length`. -/

/-- Mathematical statement: the TM correctly simulates SLProgram.evalAux. -/
def CircuitEvaluatorCSAt_CondCorrect {n : Nat} (gates : List (SLGate n)) : Prop :=
  ∀ (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (_h_phase : c.state.fst.val = 0)
    (_h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + gates.length ≤ N)
    (_htape_clean : ∀ i : Fin
        ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false)
    (prior vals : List Bool)
    (_h_prior_len : prior.length = offset)
    (_h_prior_match : ∀ (k : Nat) (_hk : k < prior.length)
        (hpos : (c.head : ℕ) + Δscratch + k <
          (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        prior[k]? = some (c.tape ⟨(c.head : ℕ) + Δscratch + k, hpos⟩))
    (_h_vals_len : vals.length = gates.length)
    (_h_eval : SLProgram.evalAux
        (rowFromConfig c Δrowbase
          (rowFromConfig_bounds gates offset Δrowbase Δscratch hle c hbound))
        gates prior = some (prior ++ vals)),
    (∀ i : Fin gates.length,
      (TM.runConfig (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N)).tape
        ⟨(c.head : ℕ) + Δscratch + offset + i.val, by
          have hi := i.isLt
          have h_len_ge : N ≤
              ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
            show N ≤ N + (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N + 1
            omega
          omega⟩ = vals[i.val]?.getD false) ∧
    (∀ j : Fin
        ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      (j.val < (c.head : ℕ) + Δscratch + offset ∨
       (c.head : ℕ) + Δscratch + offset + gates.length ≤ j.val) →
      (TM.runConfig (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N)).tape j =
        c.tape j)

/-- Nil case of the correctness predicate. -/
theorem CircuitEvaluatorCSAt_CondCorrect_nil {n : Nat} :
    CircuitEvaluatorCSAt_CondCorrect ([] : List (SLGate n)) := by
  intro offset Δrowbase Δscratch hle N c _ _ _ _ prior vals _ _ h_vals_len _
  have hv_empty : vals = [] := List.length_eq_zero_iff.mp (by simpa using h_vals_len)
  subst hv_empty
  exact circuitEvaluatorCSAt_run_correct_cond_nil offset Δrowbase Δscratch hle c

/-- Single-gate case, derived from `circuitEvaluatorCSAt_run_correct_cond_single`. -/
theorem CircuitEvaluatorCSAt_CondCorrect_single {n : Nat} (g : SLGate n) :
    CircuitEvaluatorCSAt_CondCorrect ([g] : List (SLGate n)) := by
  intro offset Δrowbase Δscratch hle N c h_phase h_state_snd hbound htape_clean
    prior vals h_prior_len h_prior_match h_vals_len h_eval
  -- Extract v from h_eval.
  obtain ⟨v, vals_rest, h_compute, h_vals_eq, hvr_len, _⟩ :=
    SLProgram_evalAux_cons_split _ g [] prior vals h_eval
  have hvr_empty : vals_rest = [] := List.length_eq_zero_iff.mp hvr_len
  subst hvr_empty
  subst h_vals_eq
  have h_single := circuitEvaluatorCSAt_run_correct_cond_single g offset
    Δrowbase Δscratch hle c h_phase h_state_snd hbound htape_clean
    prior v h_prior_len h_prior_match h_compute
  refine ⟨?_, h_single.2⟩
  rintro ⟨n_i, hn_i⟩
  match n_i, hn_i with
  | 0, _ =>
    show (TM.runConfig (M := (circuitEvaluatorCSAt [g] offset Δrowbase Δscratch hle).toPhased.toTM) c
        ((circuitEvaluatorCSAt [g] offset Δrowbase Δscratch hle).timeBound N)).tape
        ⟨(c.head : ℕ) + Δscratch + offset + 0, _⟩ = [v][(0 : Nat)]?.getD false
    simp only [List.getElem?_cons_zero, Option.getD_some]
    have hb1 : (c.head : ℕ) + Δscratch + offset + 1 ≤ N := by
      have := hbound; simp at this; exact this
    have hlen_ge : N ≤
        (circuitEvaluatorCSAt [g] offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      show N ≤ N + (circuitEvaluatorCSAt [g] offset Δrowbase Δscratch hle).timeBound N + 1
      omega
    have h_fin_eq : (⟨(c.head : ℕ) + Δscratch + offset + 0, by omega⟩ :
        Fin ((circuitEvaluatorCSAt [g] offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N)) =
        ⟨(c.head : ℕ) + Δscratch + offset, by omega⟩ := by
      apply Fin.ext
      show (c.head : ℕ) + Δscratch + offset + 0 = (c.head : ℕ) + Δscratch + offset
      omega
    rw [h_fin_eq]
    exact h_single.1
  | k + 1, hk_bound =>
    have : k + 1 < 1 := hk_bound
    omega

/-! ### Multi-gate cons step for CondCorrect

Given CondCorrect on the tail `(g' :: rest')`, derives CondCorrect on
`(g :: g' :: rest')` by combining decomposition + IH + slot-0-from-gate. -/

theorem CircuitEvaluatorCSAt_CondCorrect_cons_multi {n : Nat}
    (g : SLGate n) (g' : SLGate n) (rest' : List (SLGate n))
    (ih : CircuitEvaluatorCSAt_CondCorrect (g' :: rest')) :
    CircuitEvaluatorCSAt_CondCorrect (g :: g' :: rest') := by
  intro offset Δrowbase Δscratch hle N c h_phase h_state_snd hbound htape_clean
    prior vals h_prior_len h_prior_match h_vals_len h_eval
  -- Step 1: Extract v and vals_rest via cons_split.
  obtain ⟨v, vals_rest, h_compute, h_vals_eq, hvr_len, h_eval_rest⟩ :=
    SLProgram_evalAux_cons_split _ g (g' :: rest') prior vals h_eval
  -- Step 2: Get decomposition + lift bindings.
  obtain ⟨hphase_lt, hhead_lt, h_tG_head, hdecomp⟩ :=
    cons_any_nonempty_composite_run_tape_at g g' rest' offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean
  set P1 := evalOneGateCS g offset Δrowbase Δscratch hle with hP1_def
  set P2 := circuitEvaluatorCSAt (g' :: rest') (offset + 1) Δrowbase Δscratch hle with hP2_def
  set c_P1 := ConstStatePhasedProgram.projectSeqP1 P1 P2 c hphase_lt hhead_lt with hc_P1_def
  set c_P1_final := TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)
    with hc_P1_final_def
  set lift := ConstStatePhasedProgram.liftP1ToP2 P1 P2 c_P1_final h_tG_head with hlift_def
  -- Step 3: Lift preconditions for ih.
  obtain ⟨h_lift_phase, h_lift_state_snd, h_lift_bound, h_lift_clean⟩ :=
    cons_any_nonempty_lift_preconditions g g' rest' offset Δrowbase Δscratch hle
      c h_phase h_state_snd hbound htape_clean hphase_lt hhead_lt h_tG_head
  -- Step 4: Lift h_prior_match.
  have h_lift_pm := cons_any_h_prior_match_lift g g' rest' offset Δrowbase Δscratch hle
    c h_phase h_state_snd hbound hphase_lt hhead_lt h_tG_head prior v h_prior_len
    h_prior_match h_compute
  -- Step 5: rowFromConfig equality for h_eval transport.
  have h_row_eq := cons_any_rowFromConfig_lift_eq g g' rest' offset Δrowbase Δscratch hle
    c h_phase h_state_snd hbound hphase_lt hhead_lt h_tG_head prior v h_prior_len
    h_prior_match h_compute (by simpa using h_lift_bound)
  -- Step 6: Prior ++ [v] has correct length.
  have h_prior_v_len : (prior ++ [v]).length = offset + 1 := by
    simp [h_prior_len]
  -- Step 7: vals_rest length.
  have hvr_len_eq : vals_rest.length = (g' :: rest').length := hvr_len
  -- Step 8: Apply ih on lift with prior ++ [v] and vals_rest.
  have h_lift_bound_for_ih : (lift.head : ℕ) + Δscratch + (offset + 1) +
      (g' :: rest').length ≤ N := h_lift_bound
  -- Transport h_eval_rest from c's row to lift's row.
  have h_eval_lift : SLProgram.evalAux
      (rowFromConfig lift Δrowbase
        (rowFromConfig_bounds (g' :: rest') (offset + 1) Δrowbase Δscratch hle lift h_lift_bound_for_ih))
      (g' :: rest') (prior ++ [v]) = some ((prior ++ [v]) ++ vals_rest) := by
    rw [h_row_eq]
    exact h_eval_rest
  have h_ih := ih (offset + 1) Δrowbase Δscratch hle lift h_lift_phase h_lift_state_snd
    h_lift_bound_for_ih h_lift_clean (prior ++ [v]) vals_rest h_prior_v_len h_lift_pm
    hvr_len_eq h_eval_lift
  obtain ⟨h_ih_slots, h_ih_pres⟩ := h_ih
  -- Step 9: Combine outer slot + preservation facts via hdecomp.
  -- vals = v :: vals_rest (from h_vals_eq).
  subst h_vals_eq
  -- h_lift_head: lift.head.val = c.head.val.
  have h_lift_head : (lift.head : ℕ) = (c.head : ℕ) := by
    show (c_P1_final.head : ℕ) = (c.head : ℕ)
    have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
    have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
      show (c_P1.head : ℕ) + (Δscratch + offset) <
        N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
      rw [evalOneGateCS_timeBound, h_c_P1_head]
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    have := evalOneGateCS_run_preserves_head g offset Δrowbase Δscratch hle c_P1
      h_phase h_state_snd h_P1_bound
    rw [this, h_c_P1_head]
  refine ⟨?_, ?_⟩
  · -- Outer slots.
    rintro ⟨n_i, hn_i⟩
    rw [hdecomp]
    have hi_bound_for_outer : (c.head : ℕ) + Δscratch + offset + n_i <
        (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      have h_len_ge : N ≤
          (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
        show N ≤ N + _ + 1; omega
      have hi_val : n_i < rest'.length + 2 := by
        have : (g :: g' :: rest').length = rest'.length + 2 := by simp
        rw [this] at hn_i; exact hn_i
      omega
    -- Position is within P2.tapeLength.
    have h_p_in_P2 : (c.head : ℕ) + Δscratch + offset + n_i < P2.toPhased.toTM.tapeLength N := by
      have hi_val : n_i < rest'.length + 2 := by
        have : (g :: g' :: rest').length = rest'.length + 2 := by simp
        rw [this] at hn_i; exact hn_i
      show (c.head : ℕ) + Δscratch + offset + n_i < N + P2.timeBound N + 1
      have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
      omega
    rw [ConstStatePhasedProgram.embedSeqP2Config_tape_in_range P1 P2 _ _ h_p_in_P2]
    -- Case analysis: n_i = 0 vs n_i ≥ 1.
    match n_i, hn_i with
    | 0, _ =>
      -- Slot 0: Outside P2's scratch.  Use h_ih_pres + lift.tape at offset = v.
      have h_pos_outside_P2 :
          (⟨(c.head : ℕ) + Δscratch + offset + 0, h_p_in_P2⟩ : Fin _).val <
            (lift.head : ℕ) + Δscratch + (offset + 1) ∨
          (lift.head : ℕ) + Δscratch + (offset + 1) + (g' :: rest').length ≤
            (⟨(c.head : ℕ) + Δscratch + offset + 0, h_p_in_P2⟩ : Fin _).val := by
        left
        show (c.head : ℕ) + Δscratch + offset + 0 < (lift.head : ℕ) + Δscratch + (offset + 1)
        rw [h_lift_head]
        omega
      have h_pres := h_ih_pres ⟨(c.head : ℕ) + Δscratch + offset + 0, h_p_in_P2⟩ h_pos_outside_P2
      rw [h_pres]
      -- Now lift.tape at the position.  Use h_lift_pm with k = offset.
      have h_lift_bound_for_match : ((lift.head : ℕ) + Δscratch + offset) < P2.toPhased.toTM.tapeLength N := by
        rw [h_lift_head]
        have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
        show (c.head : ℕ) + Δscratch + offset < N + P2.timeBound N + 1
        omega
      have h_pm_offset := h_lift_pm offset (by simp [h_prior_len]) h_lift_bound_for_match
      -- h_pm_offset : (prior ++ [v])[offset]? = some (lift.tape ⟨lift.head + Δscratch + offset, _⟩)
      have h_val : (prior ++ [v])[offset]? = some v := by
        rw [List.getElem?_append_right (by rw [h_prior_len])]
        rw [h_prior_len]; simp
      rw [h_val] at h_pm_offset
      have h_lift_tape_eq : lift.tape ⟨(lift.head : ℕ) + Δscratch + offset, h_lift_bound_for_match⟩ = v :=
        (Option.some.inj h_pm_offset).symm
      -- Position identification.
      have h_fin_eq : (⟨(c.head : ℕ) + Δscratch + offset + 0, h_p_in_P2⟩ : Fin _) =
          ⟨(lift.head : ℕ) + Δscratch + offset, h_lift_bound_for_match⟩ := by
        apply Fin.ext
        show (c.head : ℕ) + Δscratch + offset + 0 = (lift.head : ℕ) + Δscratch + offset
        rw [h_lift_head]; omega
      rw [h_fin_eq]
      -- Goal: lift.tape at ⟨lift.head + Δscratch + offset, _⟩ = (v :: vals_rest)[0]?.getD false.
      simp only [List.getElem?_cons_zero, Option.getD_some]
      exact h_lift_tape_eq
    | k + 1, hk_bound =>
      -- Slot k+1: Use h_ih_slots at index k.
      have hk_val : k < (g' :: rest').length := by
        have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
        rw [hlen] at hk_bound
        have : (g' :: rest').length = rest'.length + 1 := by simp
        rw [this]; omega
      have h_slot_k := h_ih_slots ⟨k, hk_val⟩
      -- h_slot_k gives tape at lift.head + Δscratch + (offset+1) + k = c.head + Δscratch + offset + (k+1).
      have h_fin_eq : (⟨(c.head : ℕ) + Δscratch + offset + (k + 1), h_p_in_P2⟩ : Fin _) =
          ⟨(lift.head : ℕ) + Δscratch + (offset + 1) + k, by
            rw [h_lift_head]
            show (c.head : ℕ) + Δscratch + (offset + 1) + k < P2.toPhased.toTM.tapeLength N
            omega⟩ := by
        apply Fin.ext
        show (c.head : ℕ) + Δscratch + offset + (k + 1) =
          (lift.head : ℕ) + Δscratch + (offset + 1) + k
        rw [h_lift_head]; omega
      rw [h_fin_eq]
      -- Goal: (P2.runConfig lift T_P2).tape ⟨lift.head + Δscratch + (offset+1) + k, _⟩ =
      --   (v :: vals_rest)[k+1]?.getD false = vals_rest[k]?.getD false.
      have h_list_get : (v :: vals_rest)[k + 1]? = vals_rest[k]? := by
        rfl
      rw [h_list_get]
      exact h_slot_k
  · -- Outer preservation.
    intro j hj_outside
    rw [hdecomp]
    -- Case j within or outside P2.tapeLength.
    by_cases hj_P2 : j.val < P2.toPhased.toTM.tapeLength N
    · rw [ConstStatePhasedProgram.embedSeqP2Config_tape_in_range P1 P2 _ j hj_P2]
      -- j is also outside P2's scratch.
      have h_j_outside_P2 :
          j.val < (lift.head : ℕ) + Δscratch + (offset + 1) ∨
          (lift.head : ℕ) + Δscratch + (offset + 1) + (g' :: rest').length ≤ j.val := by
        rw [h_lift_head]
        have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
        have hlen2 : (g' :: rest').length = rest'.length + 1 := by simp
        rcases hj_outside with hlt | hge
        · left; omega
        · right; omega
      have h_pres := h_ih_pres ⟨j.val, hj_P2⟩ h_j_outside_P2
      rw [h_pres]
      -- Now lift.tape at j.  For j.val < P1.tapeLength, lift.tape = c_P1.write ... .tape.
      -- For j ≠ slot offset (by hj_outside), this = c_P1.tape = c.tape.
      -- For j.val ≥ P1.tapeLength, lift.tape = false, but then we need c.tape j = false too,
      -- which follows from htape_clean if j.val ≥ N.
      by_cases hj_P1 : j.val < P1.toPhased.toTM.tapeLength N
      · -- j within P1.tapeLength.
        show (if h : j.val < P1.toPhased.toTM.tapeLength N
                then c_P1_final.tape ⟨j.val, h⟩ else false) = c.tape j
        rw [dif_pos hj_P1]
        -- c_P1_final.tape = c_P1.write (slot offset) v.
        have h_P1_phase : c_P1.state.fst.val = 0 := h_phase
        have h_P1_state_snd : c_P1.state.snd = (false, false) := h_state_snd
        have h_P1_bound : (c_P1.head : ℕ) + (Δscratch + offset) < P1.toPhased.toTM.tapeLength N := by
          show (c_P1.head : ℕ) + (Δscratch + offset) <
            N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
          rw [evalOneGateCS_timeBound]
          have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
          rw [h_c_P1_head]
          have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
          omega
        have h_prior_match_P1 : ∀ (k' : Nat) (hk' : k' < prior.length)
            (hpos' : (c_P1.head : ℕ) + Δscratch + k' < P1.toPhased.toTM.tapeLength N),
            prior[k']? = some (c_P1.tape ⟨(c_P1.head : ℕ) + Δscratch + k', hpos'⟩) := by
          intro k' hk' hpos'
          have hk'_lt_offset : k' < offset := by rw [h_prior_len] at hk'; exact hk'
          have hpos_composite : (c.head : ℕ) + Δscratch + k' <
              (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
            have hlen_ge : N ≤
                (circuitEvaluatorCSAt (g :: g' :: rest') offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
              show N ≤ N + _ + 1; omega
            have hlen2 : (g :: g' :: rest').length = rest'.length + 2 := by simp
            omega
          have := h_prior_match k' hk' hpos_composite
          rw [this]; rfl
        have h_row_eq_P1 :
            (fun (i : Fin n) => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
              have hi := i.isLt
              show _ < P1.toPhased.toTM.tapeLength N
              have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
              rw [h_c_P1_head]
              show (c.head : ℕ) + Δrowbase + i.val <
                N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
              rw [evalOneGateCS_timeBound]
              omega⟩) =
            (rowFromConfig c Δrowbase
              (rowFromConfig_bounds (g :: g' :: rest') offset Δrowbase Δscratch hle c hbound)) := by
          funext i
          show c_P1.tape _ = c.tape _
          rfl
        have h_compute_P1 : g.compute
            (fun (i : Fin n) => c_P1.tape ⟨(c_P1.head : ℕ) + Δrowbase + i.val, by
              have hi := i.isLt
              show _ < P1.toPhased.toTM.tapeLength N
              have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
              rw [h_c_P1_head]
              show (c.head : ℕ) + Δrowbase + i.val <
                N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
              rw [evalOneGateCS_timeBound]
              omega⟩) prior = some v := by
          rw [h_row_eq_P1]; exact h_compute
        have h_write := evalOneGateCS_writes_compute_result g offset Δrowbase Δscratch hle
          c_P1 h_P1_phase h_P1_state_snd h_P1_bound prior h_prior_len h_prior_match_P1 v h_compute_P1
        show (TM.runConfig (M := P1.toPhased.toTM) c_P1 (2 * (Δscratch + offset) + 3)).tape
          ⟨j.val, hj_P1⟩ = c.tape j
        rw [h_write]
        -- j ≠ slot offset position.
        have h_ne : (⟨j.val, hj_P1⟩ : Fin _) ≠
            ⟨(c_P1.head : ℕ) + (Δscratch + offset), h_P1_bound⟩ := by
          intro heq
          have hval : j.val = (c_P1.head : ℕ) + (Δscratch + offset) := Fin.val_eq_of_eq heq
          have h_c_P1_head : (c_P1.head : ℕ) = (c.head : ℕ) := rfl
          rw [h_c_P1_head] at hval
          rcases hj_outside with hlt | hge
          · omega
          · have hlen : (g :: g' :: rest').length = rest'.length + 2 := by simp
            omega
        rw [Configuration.write_other c_P1 h_ne v]
        rfl
      · -- j ≥ P1.tapeLength.
        show (if h : j.val < P1.toPhased.toTM.tapeLength N
                then c_P1_final.tape ⟨j.val, h⟩ else false) = c.tape j
        rw [dif_neg hj_P1]
        symm
        apply htape_clean
        have hP1_ge_N : N ≤ P1.toPhased.toTM.tapeLength N := by
          show N ≤ N + (evalOneGateCS g offset Δrowbase Δscratch hle).timeBound N + 1
          omega
        omega
    · -- j outside P2.tapeLength.
      rw [ConstStatePhasedProgram.embedSeqP2Config_tape_out_of_range P1 P2 _ j
        (Nat.le_of_not_lt hj_P2)]
      symm
      apply htape_clean
      have h_P2_ge_N : N ≤ P2.toPhased.toTM.tapeLength N := by
        show N ≤ N + P2.timeBound N + 1; omega
      omega

/-! ### FULL UNCONDITIONAL CORRECTNESS

By well-founded recursion on `gates.length`, using the three case theorems. -/

/-- **Full unconditional correctness of `circuitEvaluatorCSAt` for ARBITRARY gate lists**.

Combines:
- `CircuitEvaluatorCSAt_CondCorrect_nil` (nil case)
- `CircuitEvaluatorCSAt_CondCorrect_single` (single-gate case, any type)
- `CircuitEvaluatorCSAt_CondCorrect_cons_multi` (multi-gate cons step)

via well-founded recursion on `gates.length`.

This is the complete mathematical F.4 correctness theorem: the circuit
evaluator TM correctly simulates SLProgram.evalAux for ANY list of gates
and ANY offset/prior configuration (assuming consistency). -/
theorem CircuitEvaluatorCSAt_CondCorrect_all {n : Nat} (gates : List (SLGate n)) :
    CircuitEvaluatorCSAt_CondCorrect gates := by
  match gates with
  | [] => exact CircuitEvaluatorCSAt_CondCorrect_nil
  | [g] => exact CircuitEvaluatorCSAt_CondCorrect_single g
  | g :: g' :: rest' =>
    exact CircuitEvaluatorCSAt_CondCorrect_cons_multi g g' rest'
      (CircuitEvaluatorCSAt_CondCorrect_all (g' :: rest'))
termination_by gates.length

/-! ### Canonical-prior version of CondCorrect for ∃-form derivation

A universally-quantified user-supplied prior cannot in general match the
scratch tape (its `h_prior_match` hypothesis fails for tape-dependent
gates), but we can still derive tape facts by applying `CondCorrect_all`
with a CANONICAL prior that DOES match the tape.  For const/input gates,
the vals are prior-independent, so the tape facts transfer directly. -/

/-- Canonical prior: `c.tape ⟨c.head + Δscratch + k, _⟩` for k in [0, offset). -/
noncomputable def canonicalPrior {n : Nat} (gates : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (hbound : (c.head : ℕ) + Δscratch + offset + gates.length ≤ N) : List Bool :=
  List.ofFn (fun (k : Fin offset) => c.tape ⟨(c.head : ℕ) + Δscratch + k.val, by
    have hk := k.isLt
    have hlen_ge : N ≤
        (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N := by
      show N ≤ N + _ + 1; omega
    omega⟩)

theorem canonicalPrior_length {n : Nat} (gates : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (hbound : (c.head : ℕ) + Δscratch + offset + gates.length ≤ N) :
    (canonicalPrior gates offset Δrowbase Δscratch hle c hbound).length = offset := by
  unfold canonicalPrior; simp

theorem canonicalPrior_h_prior_match {n : Nat} (gates : List (SLGate n))
    (offset Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (hbound : (c.head : ℕ) + Δscratch + offset + gates.length ≤ N) :
    ∀ (k : Nat) (_hk : k < (canonicalPrior gates offset Δrowbase Δscratch hle c hbound).length)
      (hpos : (c.head : ℕ) + Δscratch + k <
        (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
      (canonicalPrior gates offset Δrowbase Δscratch hle c hbound)[k]? =
        some (c.tape ⟨(c.head : ℕ) + Δscratch + k, hpos⟩) := by
  intro k hk hpos
  -- canonicalPrior = List.ofFn (fun k => c.tape ⟨..., _⟩)
  -- So canonicalPrior[k]? = some (c.tape ⟨c.head + Δscratch + k, _⟩).
  have hk_offset : k < offset := by
    have hlen := canonicalPrior_length gates offset Δrowbase Δscratch hle c hbound
    rw [hlen] at hk; exact hk
  unfold canonicalPrior
  rw [List.getElem?_ofFn]
  simp only [dif_pos hk_offset]

/-! ### F.4 closure for ARBITRARY gate lists via positional well-formedness

The all-const and all-input ∃-form theorems above exploit
*prior-independence*: for those gate types, `SLGate.compute` ignores
the accumulator, so `evalAux` always succeeds.  The remaining gate
types — `.notGate`, `.andGate`, `.orGate` — read from the accumulator,
so `evalAux` may fail on malformed lists (references out of bounds).

To close F.4 for arbitrary gate lists (including `.notGate`/`.andGate`/
`.orGate` and mixed combinations), we introduce a **positional
well-formedness** predicate: each gate at position `i` (relative to
accumulator length `offset + i`) must reference only indices in
`[0, offset + i)`.

Under this hypothesis, `evalAux` succeeds for any list, and the F.4
correctness theorem extends to arbitrary gates via the canonical-prior
construction (session 49u). -/

/-- Positional well-formedness for a single gate at accumulator length
`L`: each of `.notGate`/`.andGate`/`.orGate`'s indices must be strictly
less than `L`.  `.const b` and `.input i` are always well-formed. -/
def SLGate_wfAtLen {n : Nat} (L : Nat) : SLGate n → Prop
  | .input _ => True
  | .const _ => True
  | .notGate k => k < L
  | .andGate k l => k < L ∧ l < L
  | .orGate k l => k < L ∧ l < L

/-- Positional well-formedness for a gate list starting from accumulator
length `offset`: each gate at position `i` in the list is well-formed
at level `offset + i`. -/
def SLProgram_wfFromOffset {n : Nat} :
    List (SLGate n) → Nat → Prop
  | [], _ => True
  | g :: rest, offset =>
    SLGate_wfAtLen offset g ∧ SLProgram_wfFromOffset rest (offset + 1)

/-- Single-gate positional well-formedness is decidable (each case is `True` or a
conjunction of `Nat <` tests).  Placed next to the predicate (not in a downstream module)
so the instance is canonical and `Classical`-free. -/
instance SLGate_wfAtLen_decidable {n : Nat} (L : Nat) (g : SLGate n) :
    Decidable (SLGate_wfAtLen L g) := by
  cases g <;> (unfold SLGate_wfAtLen; infer_instance)

/-- Gate-list positional well-formedness is decidable, by structural recursion on the list
(each step is an `And` of the decidable single-gate check and the decidable tail).  This is the
spec-layer well-formedness guard the NP verifier uses to reject ill-formed circuits before
invoking `circuitEvaluatorCS_run_correct_wf` (its `hwf` hypothesis). -/
instance decSLProgram_wfFromOffset {n : Nat} :
    (gates : List (SLGate n)) → (offset : Nat) → Decidable (SLProgram_wfFromOffset gates offset)
  | [], _ => isTrue trivial
  | g :: rest, offset =>
    match SLGate_wfAtLen_decidable offset g, decSLProgram_wfFromOffset rest (offset + 1) with
    | isTrue hg, isTrue hr => isTrue ⟨hg, hr⟩
    | isFalse hg, _ => isFalse (fun h => hg h.1)
    | _, isFalse hr => isFalse (fun h => hr h.2)

/-- **Key existence lemma**: any well-formed gate list admits a
successful `evalAux` computation with any prior of matching length.
Used to build the `h_eval` hypothesis for `CondCorrect_all` in the
arbitrary-gates ∃-form theorem below. -/
theorem evalAux_of_wf {n : Nat} (row : Fin n → Bool) :
    ∀ (gates : List (SLGate n)) (offset : Nat) (prior : List Bool),
      prior.length = offset →
      SLProgram_wfFromOffset gates offset →
      ∃ vals : List Bool,
        vals.length = gates.length ∧
        SLProgram.evalAux row gates prior = some (prior ++ vals)
  | [], _, prior, _, _ => by
    refine ⟨[], rfl, ?_⟩
    show SLProgram.evalAux row [] prior = some (prior ++ [])
    simp [SLProgram.evalAux]
  | g :: rest, offset, prior, h_len, hwf => by
    obtain ⟨h_g_wf, h_rest_wf⟩ := hwf
    -- For any well-formed gate, `g.compute row prior` succeeds.
    have h_compute : ∃ v, g.compute row prior = some v := by
      cases g with
      | input i => exact ⟨row i, rfl⟩
      | const b => exact ⟨b, rfl⟩
      | notGate k =>
        -- h_g_wf : SLGate_wfAtLen offset (.notGate k) unfolds to k < offset.
        have h_k : k < offset := h_g_wf
        have hk : k < prior.length := by rw [h_len]; exact h_k
        have h_eq : prior[k]? = some prior[k] := List.getElem?_eq_getElem hk
        refine ⟨! prior[k], ?_⟩
        show prior[k]?.map (!·) = some (! prior[k])
        rw [h_eq]; rfl
      | andGate k l =>
        obtain ⟨h_k, h_l⟩ : k < offset ∧ l < offset := h_g_wf
        have hk : k < prior.length := by rw [h_len]; exact h_k
        have hl : l < prior.length := by rw [h_len]; exact h_l
        have hk_eq : prior[k]? = some prior[k] := List.getElem?_eq_getElem hk
        have hl_eq : prior[l]? = some prior[l] := List.getElem?_eq_getElem hl
        refine ⟨prior[k] && prior[l], ?_⟩
        show (match prior[k]?, prior[l]? with
              | some a, some b => some (a && b)
              | _, _ => none) = some (prior[k] && prior[l])
        rw [hk_eq, hl_eq]
      | orGate k l =>
        obtain ⟨h_k, h_l⟩ : k < offset ∧ l < offset := h_g_wf
        have hk : k < prior.length := by rw [h_len]; exact h_k
        have hl : l < prior.length := by rw [h_len]; exact h_l
        have hk_eq : prior[k]? = some prior[k] := List.getElem?_eq_getElem hk
        have hl_eq : prior[l]? = some prior[l] := List.getElem?_eq_getElem hl
        refine ⟨prior[k] || prior[l], ?_⟩
        show (match prior[k]?, prior[l]? with
              | some a, some b => some (a || b)
              | _, _ => none) = some (prior[k] || prior[l])
        rw [hk_eq, hl_eq]
    obtain ⟨v, hv⟩ := h_compute
    -- Recurse on `rest` with `prior ++ [v]` at `offset + 1`.
    have h_new_len : (prior ++ [v]).length = offset + 1 := by
      rw [List.length_append, List.length_singleton]; omega
    obtain ⟨vals_rest, h_rest_len, h_rest_eval⟩ :=
      evalAux_of_wf row rest (offset + 1) (prior ++ [v]) h_new_len h_rest_wf
    refine ⟨v :: vals_rest, ?_, ?_⟩
    · simp [h_rest_len]
    · rw [SLProgram.evalAux_cons, hv]
      simp only [Option.bind_some]
      rw [h_rest_eval]
      -- `prior ++ [v] ++ vals_rest = prior ++ (v :: vals_rest)`.
      rw [List.append_assoc]
      rfl

/-! ### Arbitrary-gates ∃-form correctness via canonical prior

Combining `evalAux_of_wf` (existence of vals for well-formed gate lists)
with `CircuitEvaluatorCSAt_CondCorrect_all` (conditional tape facts)
and the canonical prior machinery yields a fully unconditional ∃-form
correctness theorem for ARBITRARY well-formed gate lists.

The theorem is stated directly (not through a universally-quantified
user-prior Prop) because such a Prop quantifies over a `prior` which
cannot in general be reconciled with tape-dependent gates (`notGate`/`andGate`/
`orGate`): the tape records the TM's computation based on canonical tape
contents, not on an arbitrary user prior.  Using the canonical prior
internally resolves this tension. -/

/-- **Arbitrary-gates ∃-form correctness** (unconditional, canonical prior).
For any well-formed gate list and any appropriate configuration, the TM
computes values that (i) match `evalAux` applied with the canonical
prior derived from the tape, (ii) appear at the expected scratch slots,
and (iii) leave all tape positions outside the write region unchanged. -/
theorem circuitEvaluatorCSAt_RunCorrect_wf_unconditional {n : Nat}
    (gates : List (SLGate n)) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (hwf : SLProgram_wfFromOffset gates offset)
    {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + offset + gates.length ≤ N)
    (htape_clean : ∀ i : Fin
        ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false) :
    ∃ vals : List Bool,
      vals.length = gates.length ∧
      SLProgram.evalAux
        (rowFromConfig c Δrowbase
          (rowFromConfig_bounds gates offset Δrowbase Δscratch hle c hbound))
        gates (canonicalPrior gates offset Δrowbase Δscratch hle c hbound) =
        some (canonicalPrior gates offset Δrowbase Δscratch hle c hbound ++ vals) ∧
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
            omega⟩ = vals[i.val]?.getD false) ∧
      (∀ j : Fin
          ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        (j.val < (c.head : ℕ) + Δscratch + offset ∨
         (c.head : ℕ) + Δscratch + offset + gates.length ≤ j.val) →
        (TM.runConfig
            (M := (circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).toPhased.toTM) c
            ((circuitEvaluatorCSAt gates offset Δrowbase Δscratch hle).timeBound N)).tape j =
          c.tape j) := by
  set row := rowFromConfig c Δrowbase
    (rowFromConfig_bounds gates offset Δrowbase Δscratch hle c hbound) with hrow_def
  set prior_canonical := canonicalPrior gates offset Δrowbase Δscratch hle c hbound
    with hpc_def
  have hpc_len : prior_canonical.length = offset :=
    canonicalPrior_length gates offset Δrowbase Δscratch hle c hbound
  have hpc_match :=
    canonicalPrior_h_prior_match gates offset Δrowbase Δscratch hle c hbound
  -- Use evalAux_of_wf to get existential vals + evalAux equality.
  obtain ⟨vals, h_vals_len, h_eval⟩ :=
    evalAux_of_wf row gates offset prior_canonical hpc_len hwf
  -- Apply CondCorrect_all to get tape + preservation facts.
  have h_all := CircuitEvaluatorCSAt_CondCorrect_all gates offset Δrowbase Δscratch hle
    c h_phase h_state_snd hbound htape_clean prior_canonical vals hpc_len hpc_match
    h_vals_len h_eval
  obtain ⟨h_slots, h_pres⟩ := h_all
  exact ⟨vals, h_vals_len, h_eval, h_slots, h_pres⟩

/-- **Public CS-form arbitrary-gates correctness** (unconditional).
Specialisation to `offset = 0`, where the canonical prior collapses to
`[]` and the `prior ++ vals = vals` simplification applies.

This is the full closure of Milestone F for arbitrary gate lists: for
any well-formed gate list (including any mix of `.input`, `.const`,
`.notGate`, `.andGate`, `.orGate`), the `circuitEvaluatorCSAt gates 0`
TM correctly simulates `SLProgram.evalAux row gates []`. -/
theorem circuitEvaluatorCS_run_correct_wf {n : Nat}
    (gates : List (SLGate n)) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (hwf : SLProgram_wfFromOffset gates 0)
    {N : Nat}
    (c : Configuration
      (M := (circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0)
    (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + gates.length ≤ N)
    (htape_clean : ∀ i : Fin
        ((circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle).toPhased.toTM.tapeLength N),
        N ≤ i.val → c.tape i = false) :
    ∃ vals : List Bool,
      vals.length = gates.length ∧
      SLProgram.evalAux
        (rowFromConfig c Δrowbase
          (rowFromConfig_bounds gates 0 Δrowbase Δscratch hle c (by simpa using hbound)))
        gates [] = some vals ∧
      ∀ i : Fin gates.length,
        (TM.runConfig
            (M := (circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle).toPhased.toTM) c
            ((circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle).timeBound N)).tape
          ⟨(c.head : ℕ) + Δscratch + i.val, by
            have hi := i.isLt
            have h_len_ge : N ≤
                ((circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle).toPhased.toTM).tapeLength N := by
              show N ≤ N + (circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle).timeBound N + 1
              omega
            omega⟩ = vals[i.val]?.getD false := by
  have hbound' : (c.head : ℕ) + Δscratch + 0 + gates.length ≤ N := by simpa using hbound
  obtain ⟨vals, h_vals_len, h_eval, h_slots, _h_pres⟩ :=
    circuitEvaluatorCSAt_RunCorrect_wf_unconditional gates 0 Δrowbase Δscratch hle
      hwf c h_phase h_state_snd hbound' htape_clean
  refine ⟨vals, h_vals_len, ?_, ?_⟩
  · -- canonicalPrior at offset=0 is [], and `[] ++ vals = vals`.
    have hpc_len : (canonicalPrior gates 0 Δrowbase Δscratch hle c hbound').length = 0 :=
      canonicalPrior_length gates 0 Δrowbase Δscratch hle c hbound'
    have hpc_nil : canonicalPrior gates 0 Δrowbase Δscratch hle c hbound' = [] :=
      List.length_eq_zero_iff.mp hpc_len
    rw [hpc_nil] at h_eval
    simpa using h_eval
  · -- Slot equality: Δscratch + 0 + i = Δscratch + i (def-eq).
    intro i
    have := h_slots i
    simpa using this

end GateEvalCS

end TM

end PsubsetPpoly
end Internal
end Pnp3
