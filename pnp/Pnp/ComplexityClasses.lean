import Pnp.Boolcube

open Boolcube

/-- A bitstring of length `n`. -/
abbrev Bitstring (n : ℕ) := Fin n → Bool

/-- A language over `{0,1}`. `L n x` interprets `x` as an input of length `n`. -/
abbrev Language := ∀ n, Bitstring n → Bool

/-- A small model of deterministic Turing machines. -/
structure TM where
  runTime : ℕ → ℕ
  accepts : ∀ n, Bitstring n → Bool

/-- A simple inductive datatype for Boolean circuits. -/
inductive Circuit (n : ℕ) where
  | var   : Fin n → Circuit n
  | const : Bool → Circuit n
  | not   : Circuit n → Circuit n
  | and   : Circuit n → Circuit n → Circuit n
  | or    : Circuit n → Circuit n → Circuit n
  deriving DecidableEq

namespace Circuit

/-- Evaluate a circuit on a Boolean input vector. -/
noncomputable def eval {n : ℕ} : Circuit n → Point n → Bool
  | var i, x      => x i
  | const b, _    => b
  | not c, x      => !(eval c x)
  | and c₁ c₂, x  => eval c₁ x && eval c₂ x
  | or c₁ c₂, x   => eval c₁ x || eval c₂ x

end Circuit

/-- A language has a polynomial-time decider if some Turing machine decides it within time `n^c + c`. -/
def polyTimeDecider (L : Language) : Prop :=
  ∃ (T : TM) (c : ℕ),
    (∀ n, T.runTime n ≤ n^c + c) ∧
    (∀ n x, T.accepts n x = L n x)

/-- The class `P` of polynomial-time decidable languages. -/
def P : Set Language := { L | polyTimeDecider L }

/-- A language has a polynomial-time verifier if there exists a Turing machine
checking membership in polynomial time, possibly using certificates of length
`n^k`.  The precise encoding of certificates is omitted here. -/
def polyTimeVerifier (L : Language) : Prop :=
  ∃ (k : ℕ) (T : TM) (c : ℕ),
    (∀ n, T.runTime n ≤ n^c + c) ∧ True

/-- The class `NP` defined via polynomial-time verifiers. -/
def NP : Set Language := { L | polyTimeVerifier L }

/-- A language has polynomial-size circuits if there exists a family of circuits of polynomial size deciding it. -/
structure InPpoly (L : Language) where
  polyBound : ℕ → ℕ
  polyBound_poly : ∃ k, ∀ n, polyBound n ≤ n^k + k
  circuits : ∀ n, Circuit n
  size_ok : ∀ n, sizeOf (circuits n) ≤ polyBound n
  correct : ∀ n (x : Bitstring n), Circuit.eval (circuits n) x = L n x

/-- The non-uniform class `P/poly`. -/
def Ppoly : Set Language := { L | ∃ h : InPpoly L, True }

