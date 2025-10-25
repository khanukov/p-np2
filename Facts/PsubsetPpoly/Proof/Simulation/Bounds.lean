import Proof.Simulation.Core

/-!
# Polynomial bounds for the straight-line simulation

This module packages the long gate-count argument into a compact statement that
produces the `InPpoly` witness used by the final inclusion theorem.  It lives on top
of `Proof.Simulation.Core`, reusing the straight-line simulation and its quantitative
estimates.
-/

open Boolcube
open TM

namespace Proof
namespace Complexity

open scoped BigOperators

/--
Helper statement: a natural number is always bounded by an exponential with
base `2`.  We phrase the inequality using `k + 1` on the right-hand side to
avoid tedious special cases for zero.
-/
lemma le_two_pow_succ (k : ℕ) : k ≤ 2 ^ (k + 1) := by
  have hSucc : k + 1 ≤ 2 ^ (k + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
        -- The induction hypothesis yields `k + 1 ≤ 2^(k + 1)`.
        -- Adding the same quantity to both sides preserves the inequality,
        -- giving `(k + 1) + 1 ≤ 2^(k + 1) + 2^(k + 1) = 2^(k + 2)`.
        have hstep := Nat.add_le_add ih ih
        simpa [two_mul, Nat.pow_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hstep
  exact Nat.le_trans (Nat.le_succ _) hSucc

/--
Monotonicity of exponentiation with respect to the base.
-/
lemma pow_le_pow_of_le_base {a b k : ℕ} (h : a ≤ b) : a ^ k ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      -- Multiply both sides of the inductive inequality by the base bound.
      have := Nat.mul_le_mul ih h
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this

/--
Auxiliary inequality packaging the previous two lemmas for the concrete base
`max P 2`.  This base is convenient later on because it uniformly dominates
both `polyBase` and the constant `2`.
-/
lemma const_le_pow_max (P c : ℕ) :
    c ≤ (max P 2) ^ (c + 1) := by
  have hTwo : c ≤ 2 ^ (c + 1) := le_two_pow_succ c
  have hBase : 2 ≤ max P 2 := Nat.le_max_right _ _
  have hmono := pow_le_pow_of_le_base (a := 2) (b := max P 2)
    (k := c + 1) hBase
  exact Nat.le_trans hTwo hmono

/--
The base used in the final polynomial bound; taking the maximum with `2`
avoids vacuous corner cases where `polyBase` becomes `1` on very small
inputs.
-/
def gateBoundBase (M : TM) (c n : ℕ) : ℕ :=
  max (polyBase (M := M) (c := c) n) 2

/-- Exponent coefficient controlling the main growth of the accepting circuit. -/
def gateBoundExponent (M : TM) : ℕ := affineFactorPolyCoeff M + 3

/-- Constant offset appearing in the exponent of the final bound. -/
def gateBoundOffset (M : TM) : ℕ := affineIterLeadCoeff M + 5

/--
Polynomial upper bound for the straight-line acceptance circuit.  The bound is
expressed purely in terms of the input length, making the subsequent
normalisation to `n ^ k + k` straightforward.
-/
def gatePolyBound (M : TM) (c n : ℕ) : ℕ :=
  straightRuntimeGateCoeff (M := M) *
    (n + 2) ^ straightRuntimeGateExp (c := c)

lemma straightAcceptCircuit_le_gatePolyBound
    (hRun : ∀ m, M.runTime m ≤ m ^ c + c) (n : ℕ) :
    (straightAcceptCircuit (M := M) (n := n)).gates ≤
      gatePolyBound (M := M) (c := c) n := by
  have h := straightRuntime_gate_le_shifted_pow
    (M := M) (n := n) (c := c) hRun
  simpa [gatePolyBound, straightAcceptCircuit_gates]
    using h

/-- The packaged gate bound `gatePolyBound` is dominated by a uniform polynomial
of the form `n ^ k + k`.  The proof isolates small input lengths and then uses
monotonicity of exponentiation for `n ≥ 2`.-/
lemma gatePolyBound_poly (M : TM) (c : ℕ) :
    ∃ k, ∀ n, gatePolyBound (M := M) (c := c) n ≤ n ^ k + k := by
  classical
  set C := straightRuntimeGateCoeff (M := M)
  set E := straightRuntimeGateExp (c := c)
  set C' := C * 3 ^ E
  set k := C' + E + 1
  refine ⟨k, ?_⟩
  intro n
  have hConst_le : C * 2 ^ E ≤ k := by
    have hBase : (2 : ℕ) ≤ 3 := by decide
    have hThree : C * 2 ^ E ≤ C * 3 ^ E :=
      Nat.mul_le_mul_left _ (pow_le_pow_of_le_base hBase E)
    have hAdd : C * 3 ^ E ≤ C * 3 ^ E + E + 1 := Nat.le_add_right _ _
    simpa [C', k, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using le_trans hThree hAdd
  have hSmall : ∀ n ≤ 1, gatePolyBound (M := M) (c := c) n ≤ k := by
    intro n hn
    cases n with
    | zero =>
        simpa [gatePolyBound] using hConst_le
    | succ n =>
        cases n with
        | zero =>
            have : C * 3 ^ E ≤ k := by
              simpa [C', k, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                using Nat.le_add_right (C * 3 ^ E) (E + 1)
            simpa [gatePolyBound]
        | succ n =>
            cases hn
  by_cases hTwo : 2 ≤ n
  · -- Large inputs: dominate by a power of `n`.
    have hBase : n + 2 ≤ 3 * n := by
      have hAdd₁ : n + 2 ≤ n + n := Nat.add_le_add_left hTwo _
      have hAdd₂ : n + n ≤ n + (n + n) := Nat.le_add_left _ _
      have : 3 * n = n + (n + n) := by
        simp [three_mul, two_mul, Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc]
      simpa [this]
        using le_trans hAdd₁ hAdd₂
    have hPow : (n + 2) ^ E ≤ (3 * n) ^ E :=
      pow_le_pow_of_le_base hBase E
    have hGate : gatePolyBound (M := M) (c := c) n ≤ C' * n ^ E := by
      have := Nat.mul_le_mul_left C hPow
      have hRewrite : (3 * n) ^ E = 3 ^ E * n ^ E := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.pow_mul]
      simpa [gatePolyBound, C', hRewrite, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc]
        using this
    have hPowBase : C' ≤ n ^ C' := by
      have hTwoPow : C' ≤ 2 ^ C' := by
        simpa [C'] using self_le_pow_two C'
      have hPowDom := pow_le_pow_of_le_base hTwo C'
      exact le_trans hTwoPow hPowDom
    have hLarge : C' * n ^ E ≤ n ^ (C' + E) := by
      have := Nat.mul_le_mul_right (n := n ^ E) hPowBase
      simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this
    have hExpLe : C' + E ≤ k := by
      simp [C', k, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    have hOne : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hTwo
    have hFinal : gatePolyBound (M := M) (c := c) n ≤ n ^ k :=
      le_trans hGate (le_trans hLarge
        (Nat.pow_le_pow_of_le_right hOne hExpLe))
    exact le_trans hFinal (Nat.le_add_right _ _)
  · -- Small inputs: fall back to the explicit bound `k`.
    have hn : n ≤ 1 := by
      exact Nat.le_of_lt_succ (lt_of_not_ge hTwo)
    have := hSmall n hn
    exact le_trans this (Nat.le_add_right _ _)

/--
A bundled polynomial bound witnessing that the simulated circuits decide the
language recognised by `M`.
-/
noncomputable def inPpoly_of_polyBound
    {L : Complexity.Language} {M : TM} {c : ℕ}
    (hRun : ∀ n, M.runTime n ≤ n ^ c + c)
    (hCorrect : ∀ n (x : Boolcube.Bitstring n),
      Complexity.TM.accepts (M := M) (n := n) x = L n x) :
    Complexity.InPpoly L := by
  classical
  refine
    { polyBound := fun n => gatePolyBound (M := M) (c := c) n
      , polyBound_poly := gatePolyBound_poly (M := M) (c := c)
      , circuits := fun n => straightAcceptCircuit (M := M) (n := n)
      , size_ok := ?_, correct := ?_ }
  · intro n
    simpa [gatePolyBound]
      using straightAcceptCircuit_le_gatePolyBound (M := M) (c := c)
        hRun n
  · intro n x
    simpa [hCorrect n x]
      using straightAcceptCircuit_spec (M := M) (n := n) x

end Complexity
end Proof

