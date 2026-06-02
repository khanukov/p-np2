import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v
variable {S : Type v} [Fintype S] [DecidableEq S] [Inhabited S]

/-!
# Bounded loop for uniform-state phased programs

NP-verifier track (Phase 6 → 5/6): the missing control-flow primitive identified in
`TM_VERIFIER_STRATEGY.md`.

The Turing-machine model runs a program for a *fixed* number of steps (`runTime n`) and the toolkit's
`seq` / `seqList` are straight-line (no back-edges).  Iterating a body `k` times for a **symbolic** `k`
(e.g. `k = 2 ^ n`, the number of truth-table rows) is nonetheless expressible: `seqList` of
`List.replicate k body` is a well-typed `ConstStatePhasedProgram` for any `k : Nat`, and its
`timeBound` / run behaviour follow from the existing `seqList` recurrences by induction on `k`.  No new
back-edge machinery is needed — this is the verifier's row-iteration loop.
-/

/-- Run `body` sequentially `k` times (straight-line repetition, valid for symbolic `k`). -/
def repeatProgram (body : ConstStatePhasedProgram S) (k : Nat) : ConstStatePhasedProgram S :=
  seqList (List.replicate k body)

@[simp] theorem repeatProgram_zero (body : ConstStatePhasedProgram S) :
    repeatProgram body 0 = idleCS := rfl

/-- One iteration peels off the front (this is `rfl`, since `List.replicate (k+1)` is a cons). -/
theorem repeatProgram_succ (body : ConstStatePhasedProgram S) (k : Nat) :
    repeatProgram body (k + 1) = seq body (repeatProgram body k) := rfl

/-- Closed-form `timeBound`: `k` copies of the body plus one handoff per copy. -/
theorem repeatProgram_timeBound (body : ConstStatePhasedProgram S) (k n : Nat) :
    (repeatProgram body k).timeBound n = k * body.timeBound n + k := by
  induction k with
  | zero => simp [repeatProgram_zero]
  | succ k ih =>
      rw [repeatProgram_succ, seq_timeBound, ih]
      have hmul : (k + 1) * body.timeBound n = k * body.timeBound n + body.timeBound n :=
        Nat.succ_mul k (body.timeBound n)
      omega

/--
Per-iteration run decomposition: running `repeatProgram body (k+1)` for its full `timeBound`
equals running the body once (its own `timeBound` steps) and then running the remaining `k` copies
(for `(repeatProgram body k).timeBound + 1` steps).  Inherited from `seqList_run_decomp`; this is the
inductive backbone for the eventual loop invariant.
-/
theorem repeatProgram_run_succ (body : ConstStatePhasedProgram S) (k : Nat) {n : Nat}
    (c : Configuration (M := (repeatProgram body (k + 1)).toPhased.toTM) n) :
    TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM) c
        ((repeatProgram body (k + 1)).timeBound n)
      = TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM)
          (TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM) c (body.timeBound n))
          ((repeatProgram body k).timeBound n + 1) := by
  simp only [repeatProgram, List.replicate_succ] at c ⊢
  exact seqList_run_decomp body (List.replicate k body) c

/-- Base case: zero iterations leave the configuration unchanged.  Together with
`repeatProgram_run_succ` this is the base/step pair for a loop invariant by induction on `k`. -/
theorem repeatProgram_run_zero (body : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (repeatProgram body 0).toPhased.toTM) n) :
    TM.runConfig (M := (repeatProgram body 0).toPhased.toTM) c
        ((repeatProgram body 0).timeBound n) = c := by
  have h0 : (repeatProgram body 0).timeBound n = 0 := by
    rw [repeatProgram_timeBound]; simp
  rw [h0]
  rfl

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
