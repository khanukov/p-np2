import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

/-!
# Complexity Classes: P, NP, P/poly

Minimal definitions of classical complexity classes for the P≠NP proof.

This file provides:
- `Language`: predicates on bitstrings
- `P`: polynomial-time decidable languages
- `NP`: languages with polynomial-time verifiers
- `Ppoly`: non-uniform polynomial-size circuits

## Design Philosophy

We use **abstract definitions** for Turing machines and circuits to keep
the complexity theory independent from the lower bounds machinery.

The key theorem `P_subset_Ppoly` (P ⊆ P/poly) is currently an axiom.
It can be proven by formalizing the classical TM-to-circuit simulation
(see Pnp2/PsubsetPpoly.lean for a full constructive proof, ~11,000 LOC).

## References

- Arora-Barak (2009): "Computational Complexity: A Modern Approach"
- Sipser (2012): "Introduction to the Theory of Computation"
-/


namespace Pnp3
namespace Complexity

/-- A bitstring of length `n`. -/
abbrev Bitstring (n : ℕ) := Fin n → Bool

/-- A language over {0,1}ⁿ.
    `L n x` means that bitstring `x` of length `n` is in the language. -/
abbrev Language := ∀ n : ℕ, Bitstring n → Bool

/-! ## Turing Machines (Abstract Interface)

For this phase, we use an **abstract axiomatization** of Turing machines.
A full constructive development exists in Pnp2/TM/ but is not needed yet.
-/

/-- Abstract single-tape Turing machine.
    Full implementation available in Pnp2/TM/Encoding.lean. -/
axiom TuringMachine : Type

/-- Running time of a TM on inputs of length n. -/
axiom TM.runTime : TuringMachine → ℕ → ℕ

/-- Whether a TM accepts a given bitstring. -/
axiom TM.accepts : (M : TuringMachine) → ∀ {n : ℕ}, Bitstring n → Bool

/-! ## Boolean Circuits (Abstract Interface)

Similarly, circuits are abstracted for now. Full implementation exists
in Pnp2/Circuit/StraightLine.lean.
-/

/-- Abstract Boolean circuit with n inputs. -/
axiom Circuit : ℕ → Type

/-- Number of gates in a circuit. -/
axiom Circuit.size : ∀ {n : ℕ}, Circuit n → ℕ

/-- Evaluation of a circuit on a bitstring. -/
axiom Circuit.eval : ∀ {n : ℕ}, Circuit n → Bitstring n → Bool

/-! ## Complexity Class P

A language is in P if there exists a Turing machine that:
1. Runs in polynomial time: runTime(n) ≤ n^c + c for some constant c
2. Correctly decides the language on all inputs
-/

/-- A language has a polynomial-time decider. -/
def PolyTimeDecider (L : Language) : Prop :=
  ∃ (M : TuringMachine) (c : ℕ),
    (∀ n, TM.runTime M n ≤ n^c + c) ∧
    (∀ n x, TM.accepts M x = L n x)

/-- The complexity class P (polynomial time). -/
def P : Set Language :=
  { L | PolyTimeDecider L }

/-! ## Complexity Class NP

A language is in NP if there exists a polynomial-time verifier:
given a candidate certificate of polynomial length, the verifier can
check membership in polynomial time.
-/

/-- A language has a polynomial-time verifier.
    The verifier gets an input x of length n plus a certificate w of length n^k,
    and runs in polynomial time. -/
def PolyTimeVerifier (L : Language) : Prop :=
  ∃ (k : ℕ) (M : TuringMachine) (c : ℕ),
    (∀ n, TM.runTime M (n + n^k) ≤ (n + n^k)^c + c) ∧
    (∀ n (x : Bitstring n),
      L n x ↔ ∃ (w : Bitstring (n^k)),
        -- Concatenate x and w as input to verifier
        let input : Bitstring (n + n^k) := fun i =>
          if h : (i : ℕ) < n then
            x ⟨i, h⟩
          else
            w ⟨(i : ℕ) - n, by
              have : (i : ℕ) ≥ n := Nat.le_of_not_lt h
              have : (i : ℕ) < n + n^k := i.isLt
              omega
            ⟩
        TM.accepts M input = true)

/-- The complexity class NP (nondeterministic polynomial time). -/
def NP : Set Language :=
  { L | PolyTimeVerifier L }

/-! ## Complexity Class P/poly

A language is in P/poly if there exists a family of polynomial-size
circuits deciding it (one circuit per input length).
-/

/-- A language has polynomial-size circuits. -/
structure InPpoly (L : Language) where
  /-- Polynomial bound on circuit size. -/
  polyBound : ℕ → ℕ
  /-- The bound is truly polynomial: ∃k such that bound(n) ≤ n^k + k. -/
  polyBound_poly : ∃ k, ∀ n, polyBound n ≤ n^k + k
  /-- Family of circuits, one per input length. -/
  circuits : ∀ n, Circuit n
  /-- Each circuit respects the polynomial size bound. -/
  size_ok : ∀ n, (circuits n).size ≤ polyBound n
  /-- Each circuit correctly decides the language on inputs of length n. -/
  correct : ∀ n (x : Bitstring n), (circuits n).eval x = L n x

/-- The complexity class P/poly (non-uniform polynomial size). -/
def Ppoly : Set Language :=
  { L | ∃ (_ : InPpoly L), True }

/-! ## The Classical Inclusion P ⊆ P/poly

**This is currently an axiom.** It can be proven constructively by
simulating Turing machines with circuits.

A full proof exists in Pnp2/PsubsetPpoly.lean (~11,000 LOC).
The simulation constructs explicit circuits from TM configurations.

For the current phase (Level 1), we keep this as an axiom to maintain
independence from the full TM/circuit infrastructure.
-/

/-- Classical inclusion: P ⊆ P/poly.

    Every polynomial-time decidable language admits polynomial-size circuits.
    This is proven in Pnp2/PsubsetPpoly.lean via explicit TM-to-circuit simulation.

    **TODO**: Port the constructive proof from Pnp2 (Level 2 or 3). -/
axiom P_subset_Ppoly : P ⊆ Ppoly

/-! ## Basic Properties

Sanity checks that our definitions make sense.
-/

/-- P is a subset of NP (every polynomial-time decider is a polynomial-time verifier
    with trivial certificates).

    NOTE: This proof has issues with the abstract axiom interface.
    For the main P≠NP result, we don't need this - the logical step is separate.
    Left as sorry for now. -/
theorem P_subset_NP : P ⊆ NP := by
  sorry

end Complexity
end Pnp3
