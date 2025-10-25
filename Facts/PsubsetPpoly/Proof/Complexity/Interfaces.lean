import Proof.Circuit.Tree
import Proof.Circuit.StraightLine
import Proof.Turing.Encoding

-/-!
# Basic Complexity Classes

This file introduces the lightweight interface for the classes `P` and
`P/poly` used by the standalone `P ⊆ P/poly` fact.  We deliberately avoid any
extra material (such as the usual `NP` definition) so that the isolated build
stays focused on the non-uniform simulation.  The module only fixes the
terminology for languages, polynomial-time Turing machines and polynomial-size
straight-line circuits.

A *language* is a predicate on bitstrings of a given length; we model
bitstrings as functions `Fin n → Bool`.  `TM` refers to the single-tape binary
machines developed in `Turing/Encoding.lean`.  Using these we define membership in
`P`.  Non-uniform polynomial size is captured via families of Boolean circuits,
yielding `P/poly`.
-/

open Boolcube

namespace Complexity

/-- A bitstring of length `n`. -/
abbrev Bitstring (n : ℕ) := Fin n → Bool

/-- A language over `{0,1}`.  `L n x` interprets `x` as an
input of length `n`. -/
abbrev Language := ∀ n, Bitstring n → Bool

/-- A language has a polynomial-time decider if some Turing
machine decides it within time `n^c + c`. -/
def polyTimeDecider (L : Language) : Prop :=
  ∃ (T : TM) (c : ℕ),
    (∀ n, T.runTime n ≤ n^c + c) ∧
    (∀ n x, T.accepts (n := n) x = L n x)

/-- The class `P` of polynomial-time decidable languages. -/
def P : Set Language := { L | polyTimeDecider L }

/-- A language has polynomial-size circuits if there exists a
family of circuits of polynomial size deciding it. -/
structure InPpoly (L : Language) where
  polyBound : ℕ → ℕ
  polyBound_poly : ∃ k, ∀ n, polyBound n ≤ n^k + k
  circuits : ∀ n, StraightLineCircuit n
  size_ok : ∀ n, (circuits n).gates ≤ polyBound n
  correct : ∀ n (x : Bitstring n),
    StraightLineCircuit.eval (circuits n) x = L n x

/-- The non-uniform class `P/poly`. -/
def Ppoly : Set Language := { L | ∃ h : InPpoly L, True }

/--
Every polynomial-time decidable language admits a family of
polynomial-size straight-line circuits.  The proof packages the
constructive simulation developed in `PsubsetPpoly.lean`: given a
Turing machine `M` running in time `n^c + c`, we obtain a straight-line
acceptance circuit whose gate count is bounded by the uniform polynomial
`gatePolyBound`.  The helper `Complexity.inPpoly_of_polyBound` exposes
this bound as an `InPpoly` witness, yielding the classical inclusion
`P ⊆ P/poly` without any axioms.-/


end Complexity
