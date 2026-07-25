import Mathlib.Data.Fin.Tuple.Basic
import Pnp4.Frontier.SequentialMagnification.HSGWindowNoGo

/-!
# Bounded-update-time streaming: the repair identified by `HSGWindowNoGo`

## Why this module exists

`MCSPStreamingTarget.lean` models a one-pass device as an *arbitrary* finite
state machine with `2 ^ space` states.  That is a faithful upper bound on
memory, but it is far too generous on everything else: such a machine may have a
completely arbitrary transition and accept function, i.e. it is **non-uniform**
and may hardwire an arbitrary set into its answers.

`HSGWindowNoGo.lean` shows this is not a harmless over-approximation.  A machine
that hardwires the (at most `2 ^ seedLen`) last-`w` windows realised by a
generator defeats every local hitting-set generator, so the whole local-HSG
sufficient condition is unsatisfiable at the port's parameters.

McKay–Murray–Williams do not produce such a machine.  Their Theorem 1.3 gives a
one-pass streaming algorithm with **space and update time** both `poly(s(n))`.
An algorithm whose update step is computed by a small circuit cannot hardwire an
arbitrary set.

This module supplies that model.

## What it changes, on both sides

* **Contract side (weaker, hence safer to assume).**  The MMW conclusion really
  does bound update time, so a contract that produces a *circuit-bounded*
  solver is closer to the published statement than one producing an arbitrary
  automaton.
* **Hardness side (weaker, hence easier to discharge).**  "No circuit-bounded
  solver" is implied by "no space-bounded solver": every circuit-bounded device
  forgets to a space-bounded one (`CircuitBoundedStreaming.toSpaceBounded`), so
  `MCSPStreamingHard → UniformMCSPStreamingHard`
  (`UniformMCSPStreamingHard_of_MCSPStreamingHard`).

So moving to this class improves the port in both directions at once, which is
why the repair is not a patch but a correction.

## Status

Definitions and bridges, all proved.  The magnification contract remains an
external published input.  Nothing here proves `P ≠ NP`, and nothing here
constructs a hitting-set generator.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

open Pnp4.AlgorithmsToLowerBounds
open Pnp3.Models

/--
A one-pass streaming device whose memory is `space` bits and whose update and
output steps are computed by circuits of size at most `updateBudget`.

`stepCircuit i` computes the new value of memory bit `i` from the current memory
contents together with the freshly read input bit (appended as the last
coordinate by `Fin.snoc`).
-/
structure CircuitBoundedStreaming (space updateBudget : Nat) where
  /-- One circuit per memory bit, over `space` state bits plus the input bit. -/
  stepCircuit : Fin space → Circuit (space + 1)
  /-- Output circuit over the memory bits. -/
  acceptCircuit : Circuit space
  /-- Update-time budget for each memory bit. -/
  step_size : ∀ i, (stepCircuit i).size ≤ updateBudget
  /-- Update-time budget for the output. -/
  accept_size : acceptCircuit.size ≤ updateBudget

namespace CircuitBoundedStreaming

variable {space updateBudget : Nat}

/-- Memory contents. -/
abbrev Memory (space : Nat) := Pnp3.Core.BitVec space

/-- One update step of the device. -/
def step (A : CircuitBoundedStreaming space updateBudget)
    (st : Memory space) (b : Bool) : Memory space :=
  fun i => (A.stepCircuit i).eval (Fin.snoc st b)

/-- Output of the device on a memory configuration. -/
def accept (A : CircuitBoundedStreaming space updateBudget)
    (st : Memory space) : Bool :=
  A.acceptCircuit.eval st

/-- The underlying transition system. -/
def toStreamingAlgo (A : CircuitBoundedStreaming space updateBudget) :
    StreamingAlgo (Memory space) where
  init := fun _ => false
  step := A.step
  accept := A.accept

/--
Forgetting the circuit bounds gives an ordinary space-bounded device: the memory
is `space` bits, so there are exactly `2 ^ space` states.
-/
def toSpaceBounded (A : CircuitBoundedStreaming space updateBudget) :
    SpaceBoundedStreaming space where
  State := Memory space
  fintypeState := inferInstance
  card_le := by simp
  algo := A.toStreamingAlgo

@[simp] lemma decideOn_toSpaceBounded
    (A : CircuitBoundedStreaming space updateBudget) (xs : List Bool) :
    A.toSpaceBounded.decideOn xs = A.toStreamingAlgo.decideOn xs := rfl

end CircuitBoundedStreaming

/-!
### The MCSP target in the restricted class
-/

/-- `MCSP[s]` at slice `n` has a circuit-bounded one-pass solver. -/
def UniformMCSPStreamingSolvable (space updateBudget n s : Nat) : Prop :=
  ∃ A : CircuitBoundedStreaming space updateBudget,
    SolvesMCSPSlice A.toSpaceBounded n s

/-- The corresponding weak lower bound. -/
def UniformMCSPStreamingHard (space updateBudget n s : Nat) : Prop :=
  ¬ UniformMCSPStreamingSolvable space updateBudget n s

/--
The restricted obligation is **weaker** than the space-only one: every
circuit-bounded solver forgets to a space-bounded solver, so a space-bounded
lower bound implies a circuit-bounded lower bound.

This is the precise sense in which the repair makes the port easier, not
harder.
-/
theorem UniformMCSPStreamingHard_of_MCSPStreamingHard
    {space updateBudget n s : Nat}
    (h : MCSPStreamingHard space n s) :
    UniformMCSPStreamingHard space updateBudget n s := by
  rintro ⟨A, hA⟩
  exact h ⟨A.toSpaceBounded, hA⟩

/-!
### The port over the restricted class
-/

/--
**Published contract, faithful form (McKay–Murray–Williams, STOC 2019,
Theorem 1.3).**

If `P = NP` then MCSP has one-pass streaming solvers whose memory *and update
time* are polynomial in the size parameter.

This records both halves of the published conclusion, unlike
`MMWStreamingMagnification`, which recorded only the space half.
-/
structure MMWUniformStreamingMagnification where
  /-- Memory budget. -/
  spaceBudget : Nat → Nat
  /-- Update-time budget, i.e. circuit-size budget per step. -/
  updateBudget : Nat → Nat
  /-- Both budgets are polynomially bounded. -/
  budgets_poly :
    ∃ c : Nat, ∀ x : Nat, spaceBudget x ≤ x ^ c + c ∧ updateBudget x ≤ x ^ c + c
  /-- The magnification content. -/
  streamingFromCollapse :
    Pnp3.ComplexityInterfaces.P = Pnp3.ComplexityInterfaces.NP →
      ∀ (s : Nat → Nat) (n : Nat),
        UniformMCSPStreamingSolvable
          (spaceBudget (s n)) (updateBudget (s n)) n (s n)

/--
**The repaired port.**  A single-slice circuit-bounded streaming lower bound for
MCSP yields `P ≠ NP`.
-/
theorem P_ne_NP_of_uniform_mcsp_streaming_hardness
    (C : MMWUniformStreamingMagnification) (s : Nat → Nat) (n : Nat)
    (hHard : UniformMCSPStreamingHard
      (C.spaceBudget (s n)) (C.updateBudget (s n)) n (s n)) :
    Pnp3.ComplexityInterfaces.P_ne_NP := by
  intro hCollapse
  exact hHard (C.streamingFromCollapse hCollapse s n)

/-- Closure witness for the repaired port. -/
structure UniformSequentialWitness where
  /-- The published magnification contract, faithful form. -/
  contract : MMWUniformStreamingMagnification
  /-- The MCSP size parameter. -/
  sizeParam : Nat → Nat
  /-- The slice at which the lower bound is claimed. -/
  slice : Nat
  /-- The weak sequential lower bound in the restricted class. -/
  hardness :
    UniformMCSPStreamingHard
      (contract.spaceBudget (sizeParam slice))
      (contract.updateBudget (sizeParam slice))
      slice (sizeParam slice)

/-- Final consequence of a discharged repaired witness. -/
theorem P_ne_NP_of_uniformSequentialWitness (w : UniformSequentialWitness) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_uniform_mcsp_streaming_hardness
    w.contract w.sizeParam w.slice w.hardness

/-!
### Why the window attack does not transfer for free

The window test of `HSGWindowNoGo.lean` accepts exactly the tables whose
last-`w` window avoids a hardwired set `P`.  To live in the restricted class it
would need its output to be computed by a circuit of size at most
`updateBudget`.

The theorem below is that observation stated precisely: a circuit-bounded device
implementing the window test *is* a small circuit for the indicator of `P`.
Since `P` is the set of windows realised by the generator, the attack survives
the uniformity restriction exactly when the generator's own window set is easy —
which is a genuine, checkable condition on a proposed construction, not a free
lunch for the attacker.
-/
theorem windowAttack_forces_easy_indicator {w u : Nat}
    (P : Finset (Fin w → Bool)) (A : CircuitBoundedStreaming w u)
    (hA : ∀ st : Pnp3.Core.BitVec w,
      A.accept st = decide (st ∉ P)) :
    ∃ c : Circuit w, c.size ≤ u ∧
      ∀ st : Pnp3.Core.BitVec w, c.eval st = decide (st ∉ P) :=
  ⟨A.acceptCircuit, A.accept_size, hA⟩

end SequentialMagnification
end Frontier
end Pnp4
