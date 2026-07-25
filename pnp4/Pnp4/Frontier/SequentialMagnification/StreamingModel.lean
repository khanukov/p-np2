import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

/-!
# One-pass streaming model (sequential magnification track)

This module fixes concrete syntax and semantics for the *weak sequential
model* used by the McKay–Murray–Williams compression-magnification theorem
(STOC 2019), as restated by Cheraghchi–Hirahara–Myrisiotis–Yoshida
(STACS 2021, ECCC TR20-103).

Why a new model at all?  Every previously refuted route in this repository
died the same death: a **non-uniform** witness class (`PpolyFormula`,
`PpolyDAG`, `AcceptedFamilyCertificateAt`, …) is closed under *truth-table
hardwiring at a fixed input length*, so any predicate that quantifies over
arbitrary witnesses of such a class is satisfiable for free and the resulting
source assumption collapses to `False`.

A one-pass streaming algorithm is a genuinely different kind of object:

* it is a **finite-state** device, so its power is measured by the number of
  reachable memory states, not by a syntactic size budget;
* it reads the input **once, left to right**, so it cannot re-inspect earlier
  bits;
* consequently "hardwiring the truth table" is *not free*: memorising an
  `N`-bit prefix literally costs `2 ^ N` states.

`StreamingLowerBounds.lean` turns that last sentence into a kernel-checked
theorem, which is exactly the falsifiability property the previous routes
lacked.

## Design notes

* State spaces are arbitrary `Type`s; the space budget is imposed *externally*
  as a bound on `Fintype.card`.  A machine with `space` bits of memory has at
  most `2 ^ space` states, which is the standard translation.
* Inputs are `List Bool`, consumed left to right.  Slices of fixed length `N`
  are selected by the hypothesis `xs.length = N`.
* Nothing here is specific to MCSP; the MCSP instantiation lives in
  `MCSPStreamingTarget.lean`.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

/--
A one-pass streaming algorithm with memory-state type `σ`.

The device starts in `init`, consumes input bits left to right through `step`,
and answers with `accept` applied to the final state.  There is no way to
revisit an already-consumed bit: that irreversibility is the whole point of the
model.
-/
structure StreamingAlgo (σ : Type) where
  /-- Initial memory state. -/
  init : σ
  /-- Transition on the next input bit. -/
  step : σ → Bool → σ
  /-- Output predicate on the final memory state. -/
  accept : σ → Bool

namespace StreamingAlgo

variable {σ : Type}

/-- Run the algorithm on `xs`, starting from an arbitrary state `s`. -/
def runFrom (A : StreamingAlgo σ) : σ → List Bool → σ
  | s, [] => s
  | s, b :: bs => A.runFrom (A.step s b) bs

/-- Run the algorithm on `xs` from its initial state. -/
def run (A : StreamingAlgo σ) (xs : List Bool) : σ :=
  A.runFrom A.init xs

/-- Boolean answer of the algorithm on `xs`. -/
def decideOn (A : StreamingAlgo σ) (xs : List Bool) : Bool :=
  A.accept (A.run xs)

@[simp] lemma runFrom_nil (A : StreamingAlgo σ) (s : σ) :
    A.runFrom s [] = s := rfl

@[simp] lemma runFrom_cons (A : StreamingAlgo σ) (s : σ) (b : Bool)
    (bs : List Bool) :
    A.runFrom s (b :: bs) = A.runFrom (A.step s b) bs := rfl

/--
The defining structural property of a one-pass device: after reading `xs`, the
only thing that survives is the memory state.
-/
lemma runFrom_append (A : StreamingAlgo σ) (s : σ) (xs ys : List Bool) :
    A.runFrom s (xs ++ ys) = A.runFrom (A.runFrom s xs) ys := by
  induction xs generalizing s with
  | nil => simp
  | cons b bs ih => simpa using ih (A.step s b)

/-- `run` version of `runFrom_append`. -/
lemma run_append (A : StreamingAlgo σ) (xs ys : List Bool) :
    A.run (xs ++ ys) = A.runFrom (A.run xs) ys := by
  simpa [run] using A.runFrom_append A.init xs ys

/--
Two prefixes that drive the machine into the same memory state are
indistinguishable by every continuation.  This is the formal content of "the
machine cannot look back".
-/
lemma decideOn_append_congr (A : StreamingAlgo σ) {xs ys : List Bool}
    (h : A.run xs = A.run ys) (zs : List Bool) :
    A.decideOn (xs ++ zs) = A.decideOn (ys ++ zs) := by
  simp [decideOn, run_append, h]

end StreamingAlgo

/--
A one-pass streaming algorithm whose memory is bounded by `space` bits, i.e.
whose state space has at most `2 ^ space` elements.

The state type is packaged inside the structure so that "there is a
space-bounded streaming solver" can be written as an ordinary `Prop`.
-/
structure SpaceBoundedStreaming (space : Nat) : Type 1 where
  /-- Memory-state type. -/
  State : Type
  /-- Finiteness of the memory. -/
  fintypeState : Fintype State
  /-- The memory budget, in bits. -/
  card_le : @Fintype.card State fintypeState ≤ 2 ^ space
  /-- The underlying transition system. -/
  algo : StreamingAlgo State

namespace SpaceBoundedStreaming

variable {space : Nat}

/-- Boolean answer of a space-bounded solver. -/
def decideOn (A : SpaceBoundedStreaming space) (xs : List Bool) : Bool :=
  A.algo.decideOn xs

/-- A solver decides the Boolean function `f` on inputs of length `N`. -/
def SolvesLength (A : SpaceBoundedStreaming space) (N : Nat)
    (f : List Bool → Bool) : Prop :=
  ∀ xs : List Bool, xs.length = N → A.decideOn xs = f xs

/-- Enlarging the memory budget only adds solvers. -/
def widen {space' : Nat} (A : SpaceBoundedStreaming space)
    (h : space ≤ space') : SpaceBoundedStreaming space' where
  State := A.State
  fintypeState := A.fintypeState
  card_le := le_trans A.card_le (Nat.pow_le_pow_right (by omega) h)
  algo := A.algo

@[simp] lemma decideOn_widen {space' : Nat} (A : SpaceBoundedStreaming space)
    (h : space ≤ space') (xs : List Bool) :
    (A.widen h).decideOn xs = A.decideOn xs := by
  simp [decideOn, widen]

/-- Solving a length slice is monotone in the memory budget. -/
lemma SolvesLength.widen {space' N : Nat} {A : SpaceBoundedStreaming space}
    {f : List Bool → Bool} (hA : A.SolvesLength N f) (h : space ≤ space') :
    (A.widen h).SolvesLength N f := by
  intro xs hxs
  simpa using hA xs hxs

end SpaceBoundedStreaming

end SequentialMagnification
end Frontier
end Pnp4
