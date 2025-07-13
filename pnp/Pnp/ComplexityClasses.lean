import Pnp.Boolcube
import Pnp.CanonicalCircuit

open Boolcube

/-- A bitstring of length `n`. -/
abbrev Bitstring (n : ℕ) := Fin n → Bool

/-- A language over `{0,1}`.  `L n x` interprets `x` as an input of length `n`. -/
abbrev Language := ∀ n, Bitstring n → Bool

/-- A very small model of deterministic Turing machines.
`runTime n` is the claimed running time on inputs of length `n`, and `accepts` is the machine's decision procedure.  No operational semantics are provided; this stub merely allows one to state complexity-theoretic definitions. -/

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

/-- A language has a polynomial-time verifier if there is a Turing machine which, given a certificate of length `n^k`, checks membership in polynomial time.  The certificate is fed to the machine after the input. -/
def polyTimeVerifier (L : Language) : Prop :=
  ∃ (k : ℕ) (T : TM) (c : ℕ),
    (∀ n, T.runTime n ≤ n^c + c) ∧
    (∀ n x, L n x ↔ ∃ w : Bitstring (n^k),
      T.accepts (n := n + n^k) (fun i =>
        if h : (i : ℕ) < n then
          x ⟨i, h⟩
        else
          w ⟨i - n, by
            have hi : n ≤ (i : ℕ) := Nat.le_of_not_lt h
            have hlt : (i : ℕ) < n + n^k := by exact i.is_lt
            have := Nat.sub_lt_sub_right (a := (i : ℕ)) (b := n + n^k) (c := n) hi hlt
            simpa [Nat.add_comm] using this
          ⟩
      ) = true)

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

