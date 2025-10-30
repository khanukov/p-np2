import OldAttempts.canonical_circuit
import OldAttempts.Circuit.StraightLine
import OldAttempts.PsubsetPpoly
import OldAttempts.TM.Encoding

/-!
# Basic Complexity Classes

This file introduces minimal definitions of the classical
complexity classes `P`, `NP` and `P/poly`.  The goal is not
an extensive development but a small set of notions that
allow the rest of the repository to state complexity
statements in a familiar language.

A *language* is a predicate on bitstrings of a given
length; we model bitstrings as functions `Fin n → Bool`.
`TM` refers to the single-tape binary machines developed in
`TM/Encoding.lean`.  Using these we define membership in `P`
and `NP`.  Non-uniform polynomial size is captured via
families of Boolean circuits, yielding `P/poly`.
-/

open Boolcube

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

/-- A language has a polynomial-time verifier if there is a
Turing machine which, given a certificate of length `n^k`,
checks membership in polynomial time.  The certificate is
fed to the machine after the input. -/
def polyTimeVerifier (L : Language) : Prop :=
  ∃ (k : ℕ) (T : TM) (c : ℕ),
    (∀ n, T.runTime n ≤ n^c + c) ∧
    (∀ n x, L n x ↔ ∃ w : Bitstring (n^k),
      T.accepts (n := n + n^k) (fun i =>
        if h : (i : ℕ) < n then x ⟨i, h⟩ else w ⟨i - n, by
          have : (i : ℕ) - n < n^k := by
            have hi : (i : ℕ) ≥ n := Nat.le_of_not_lt h
            have : (i : ℕ) < n + n^k := by exact i.is_lt
            have : (i : ℕ) - n < n^k := by
              have := Nat.sub_lt_sub_right this hi
              simpa [Nat.add_comm] using this
            exact this
          exact this
        ) = true)

/-- The class `NP` defined via polynomial-time verifiers. -/
def NP : Set Language := { L | polyTimeVerifier L }

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
theorem P_subset_Ppoly : P ⊆ Ppoly := by
  intro L hL
  rcases hL with ⟨M, c, hRun, hCorrect⟩
  refine ⟨Complexity.inPpoly_of_polyBound (M := M) (c := c)
      hRun hCorrect, trivial⟩
