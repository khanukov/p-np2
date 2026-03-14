import Complexity.Simulation.TM_Encoding
import Complexity.PsubsetPpolyDAG_Internal
import Complexity.PsubsetPpolyInternal.Simulation
import Complexity.PsubsetPpolyInternal.StraightLineSemantics

namespace Pnp3
namespace Complexity
namespace Simulation

open ComplexityInterfaces
open StraightLineAdapter

/-!
Active inclusion route for `P_subset_PpolyDAG`.

This file keeps only the linear compiled-runtime closure path used by
`proved_P_subset_PpolyDAG_internal`.
-/

/--
Evaluator-agreement contract for the linear compiled-runtime acceptance family.
-/
def CompiledAcceptCircuitEvalAgreementLinear : Prop :=
  ∀ (M : TM) (n : Nat) (x : Bitstring n),
    StraightLineAdapter.eval
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n)) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M
          (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n)) x

/--
Narrower evaluator-agreement contract for the linear compiled-runtime route:
agreement is required only on the acceptance output wire.
-/
def CompiledAcceptOutputWireAgreementLinear : Prop :=
  ∀ (M : TM) (n : Nat) (x : Bitstring n),
    StraightLineAdapter.evalWire
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit x
      ((Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).state M.accept) =
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit x
      ((Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).state M.accept)

theorem compiledAcceptEvalAgreementLinear_of_outputWireAgreement
    (hOut : CompiledAcceptOutputWireAgreementLinear) :
    CompiledAcceptCircuitEvalAgreementLinear := by
  intro M n x
  let sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n
  have hArch :
      StraightLineAdapter.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M sc) x =
      StraightLineAdapter.evalWire sc.circuit x (sc.state M.accept) := by
    change StraightLineAdapter.eval
      (StraightLineAdapter.withOutput sc.circuit (sc.state M.accept)) x =
      StraightLineAdapter.evalWire sc.circuit x (sc.state M.accept)
    rfl
  have hInt :
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M sc) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.state M.accept) := by
    simpa [Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf, sc] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := sc.circuit) (out := sc.state M.accept) (x := x))
  exact hArch.trans ((hOut M n x).trans hInt.symm)

/--
Linear-runtime size contract.

`Linear` in this name refers to the linear-step builder route, not to an
`O(n)` bound; the contract shape is still polynomial (`n^k + k`).
-/
def CompiledRuntimeCircuitSizeBoundLinear : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      (toDag
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit).size ≤
        n ^ k + k

/--
Residual correctness contract restricted to the linear compiled-runtime family.
-/
def CompiledRuntimeAcceptCorrectnessLinear : Prop :=
  ∀ (M : TM) (n : Nat) (x : Bitstring n),
    Pnp3.Internal.PsubsetPpoly.StraightLine.eval
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n)) x =
      TM.accepts M n x

/--
Residual polynomial-domination obligation for accumulated runtime budget:
`2 + runTime * linearStepBudgetExpanded` must be polynomially bounded.
-/
def CompiledRuntimeBudgetPolyBound : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      2 + M.runTime n *
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
        n ^ k + k

/-- Any natural constant is bounded by `n^const` once `n ≥ 2`. -/
private lemma const_le_pow_of_two_le
    {n : Nat} (hn2 : 2 ≤ n) (m : Nat) :
    m ≤ n ^ m := by
  cases m with
  | zero =>
      simp
  | succ m =>
      have hlt : Nat.succ m < 2 ^ Nat.succ m := Nat.lt_two_pow_self
      have hpow : 2 ^ Nat.succ m ≤ n ^ Nat.succ m := Nat.pow_le_pow_left hn2 _
      exact Nat.le_trans (Nat.le_of_lt hlt) hpow

/--
If `a ≤ n^A` and `b ≤ n^B` (with `n ≥ 2`), then `a + b` is bounded by a
single power of `n` with one extra additive exponent slack.
-/
private lemma add_le_pow_of_le_pow
    {n a b A B : Nat}
    (hn2 : 2 ≤ n)
    (ha : a ≤ n ^ A)
    (hb : b ≤ n ^ B) :
    a + b ≤ n ^ (A + B + 1) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn2
  have ha' : a ≤ n ^ (A + B) := by
    exact Nat.le_trans ha (Nat.pow_le_pow_right hn1 (Nat.le_add_right A B))
  have hb' : b ≤ n ^ (A + B) := by
    have hB : B ≤ A + B := Nat.le_add_left B A
    exact Nat.le_trans hb (Nat.pow_le_pow_right hn1 hB)
  have hsum : a + b ≤ n ^ (A + B) + n ^ (A + B) := Nat.add_le_add ha' hb'
  have hstep : n ^ (A + B) + n ^ (A + B) ≤ n * n ^ (A + B) := by
    calc
      n ^ (A + B) + n ^ (A + B) = 2 * n ^ (A + B) := by omega
      _ ≤ n * n ^ (A + B) := Nat.mul_le_mul_right _ hn2
  calc
    a + b ≤ n ^ (A + B) + n ^ (A + B) := hsum
    _ ≤ n * n ^ (A + B) := hstep
    _ = n ^ (A + B + 1) := by
          simp [Nat.pow_succ, Nat.mul_comm]

/-- Multiplicative closure of `≤ n^k` bounds. -/
private lemma mul_le_pow_of_le_pow
    {n a b A B : Nat}
    (ha : a ≤ n ^ A)
    (hb : b ≤ n ^ B) :
    a * b ≤ n ^ (A + B) := by
  calc
    a * b ≤ n ^ A * n ^ B := Nat.mul_le_mul ha hb
    _ = n ^ (A + B) := by
          simp [Nat.pow_add]

/--
For `n ≥ 2`, a polytime bound `runTime n ≤ n^c + c` collapses to
`runTime n ≤ n^(c+1)`.
-/
private lemma runTime_le_pow_succ_of_poly
    (M : TM) (c n : Nat)
    (hn2 : 2 ≤ n)
    (hRun : M.runTime n ≤ n ^ c + c) :
    M.runTime n ≤ n ^ (c + 1) := by
  have hc : c ≤ n ^ c := const_le_pow_of_two_le hn2 c
  have h1 : n ^ c + c ≤ n ^ c + n ^ c := Nat.add_le_add_left hc (n ^ c)
  have h2 : n ^ c + n ^ c = 2 * n ^ c := by omega
  have h3 : 2 * n ^ c ≤ n * n ^ c := Nat.mul_le_mul_right _ hn2
  calc
    M.runTime n ≤ n ^ c + c := hRun
    _ ≤ n ^ c + n ^ c := h1
    _ = 2 * n ^ c := h2
    _ ≤ n * n ^ c := h3
    _ = n ^ (c + 1) := by
          simp [Nat.pow_succ, Nat.mul_comm]

/--
For `n ≥ 2`, tape length is bounded by a polynomial power `n^(c+3)` under the
same polytime assumption.
-/
private lemma tapeLength_le_pow_of_poly
    (M : TM) (c n : Nat)
    (hn2 : 2 ≤ n)
    (hRun : M.runTime n ≤ n ^ c + c) :
    M.tapeLength n ≤ n ^ (c + 3) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn2
  have hrt : M.runTime n ≤ n ^ (c + 1) :=
    runTime_le_pow_succ_of_poly (M := M) (c := c) (n := n) hn2 hRun
  have hn : n ≤ n ^ (c + 1) := Nat.le_self_pow (Nat.succ_ne_zero c) n
  have hOne : 1 ≤ n ^ (c + 1) := Nat.le_trans hn1 hn
  have hsum :
      n + M.runTime n + 1 ≤ n ^ (c + 1) + n ^ (c + 1) + n ^ (c + 1) := by
    omega
  have hthree : n ^ (c + 1) + n ^ (c + 1) + n ^ (c + 1) = 3 * n ^ (c + 1) := by omega
  have h3le : 3 ≤ n ^ 2 := by
    have h4 : 4 ≤ n * n := Nat.mul_le_mul hn2 hn2
    exact Nat.le_trans (by decide : 3 ≤ 4) (by simpa [pow_two] using h4)
  have hmul : 3 * n ^ (c + 1) ≤ n ^ 2 * n ^ (c + 1) := Nat.mul_le_mul_right _ h3le
  have hpow : n ^ 2 * n ^ (c + 1) = n ^ (c + 3) := by
    calc
      n ^ 2 * n ^ (c + 1) = n ^ (2 + (c + 1)) := by
        simp [Nat.pow_add]
      _ = n ^ (c + 3) := by
        simp [Nat.add_assoc, Nat.add_comm]
  have htape : M.tapeLength n = n + M.runTime n + 1 := by
    rfl
  calc
    M.tapeLength n = n + M.runTime n + 1 := htape
    _ ≤ n ^ (c + 1) + n ^ (c + 1) + n ^ (c + 1) := hsum
    _ = 3 * n ^ (c + 1) := hthree
    _ ≤ n ^ 2 * n ^ (c + 1) := hmul
    _ = n ^ (c + 3) := hpow

theorem compiledRuntimeBudgetPolyBound_internal :
    CompiledRuntimeBudgetPolyBound := by
  intro M c hRun
  let S : Nat := Pnp3.Internal.PsubsetPpoly.Simulation.stateCard M
  let E1 : Nat := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1)
  let E2 : Nat := (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S)) + 1 + 1)
  let E3 : Nat := (2 + (c + 3))
  let E4 : Nat := ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3))
  let E5 : Nat := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S)
  let kBudget : Nat := (((E1 + E2 + 1) + E3 + 1) + E4 + 1) + E5 + 1
  let kCore : Nat := 1 + ((c + 1) + (kBudget + 3)) + 1
  let v0 : Nat :=
    2 + M.runTime 0 *
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M 0
  let v1 : Nat :=
    2 + M.runTime 1 *
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M 1
  refine ⟨max kCore (max v0 v1), ?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst hn0
    have hk : v0 ≤ max kCore (max v0 v1) := by
      exact Nat.le_trans (Nat.le_max_left v0 v1) (Nat.le_max_right kCore (max v0 v1))
    exact Nat.le_trans hk (Nat.le_add_left _ _)
  · by_cases hn1 : n = 1
    · subst hn1
      have hk : v1 ≤ max kCore (max v0 v1) := by
        exact Nat.le_trans (Nat.le_max_right v0 v1) (Nat.le_max_right kCore (max v0 v1))
      exact Nat.le_trans hk (Nat.le_add_left _ _)
    · have hn2 : 2 ≤ n := by omega
      have hnPos : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn2
      let L : Nat := M.tapeLength n
      have hL : L ≤ n ^ (c + 3) := by
        simpa [L] using tapeLength_le_pow_of_poly (M := M) (c := c) (n := n) hn2 (hRun n)
      have hRunPow : M.runTime n ≤ n ^ (c + 1) :=
        runTime_le_pow_succ_of_poly (M := M) (c := c) (n := n) hn2 (hRun n)
      have hS : S ≤ n ^ S := by
        simpa [S] using const_le_pow_of_two_le (n := n) hn2 S
      have hOne : (1 : Nat) ≤ n ^ 1 := by
        simpa using hnPos
      have hTwo : (2 : Nat) ≤ n ^ 1 := by
        rw [Nat.pow_one]
        exact hn2
      have hFour : (4 : Nat) ≤ n ^ 2 := by
        have hmul : 4 ≤ n * n := Nat.mul_le_mul hn2 hn2
        simpa [pow_two] using hmul
      have hFive : (5 : Nat) ≤ n ^ 3 := by
        have h8 : 8 ≤ n ^ 3 := by
          have h2pow : 2 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn2 3
          simpa using h2pow
        exact Nat.le_trans (by decide : 5 ≤ 8) h8
      have h2L : 2 * L ≤ n ^ (1 + (c + 3)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2) (b := L) (A := 1) (B := c + 3) hTwo hL
      have h2S : 2 * S ≤ n ^ (1 + S) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2) (b := S) (A := 1) (B := S) hTwo hS
      have h2L4 : 2 * L + 4 ≤ n ^ ((1 + (c + 3)) + 2 + 1) := by
        exact add_le_pow_of_le_pow (n := n) (a := 2 * L) (b := 4)
          (A := 1 + (c + 3)) (B := 2) hn2 h2L hFour
      have h2L5 : 2 * L + 5 ≤ n ^ ((1 + (c + 3)) + 3 + 1) := by
        exact add_le_pow_of_le_pow (n := n) (a := 2 * L) (b := 5)
          (A := 1 + (c + 3)) (B := 3) hn2 h2L hFive
      have hL2S : L * (2 * S) ≤ n ^ ((c + 3) + (1 + S)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := L) (b := 2 * S)
          (A := c + 3) (B := 1 + S) hL h2S
      have hT1 : ((2 * L + 4) * (2 * S) + 5) ≤
          n ^ ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) := by
        have hProd :
            (2 * L + 4) * (2 * S) ≤ n ^ (((1 + (c + 3)) + 2 + 1) + (1 + S)) := by
          exact mul_le_pow_of_le_pow (n := n) (a := 2 * L + 4) (b := 2 * S)
            (A := ((1 + (c + 3)) + 2 + 1)) (B := 1 + S) h2L4 h2S
        exact add_le_pow_of_le_pow (n := n) (a := (2 * L + 4) * (2 * S)) (b := 5)
          (A := (((1 + (c + 3)) + 2 + 1) + (1 + S))) (B := 3) hn2 hProd hFive
      have hProd2 :
          (2 * L + 5) * (L * (2 * S)) ≤
            n ^ (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2 * L + 5) (b := L * (2 * S))
          (A := ((1 + (c + 3)) + 3 + 1)) (B := ((c + 3) + (1 + S))) h2L5 hL2S
      have hT2 : ((2 * L + 5) * (L * (2 * S)) + 1) ≤
          n ^ ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1) := by
        exact add_le_pow_of_le_pow (n := n) (a := (2 * L + 5) * (L * (2 * S))) (b := 1)
          (A := (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S)))) (B := 1)
          hn2 hProd2 hOne
      have hT3 : 4 * L ≤ n ^ (2 + (c + 3)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 4) (b := L) (A := 2) (B := c + 3) hFour hL
      have hT4 : ((2 * L + 5) * (L * (2 * S))) * L ≤
          n ^ ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) := by
        exact mul_le_pow_of_le_pow (n := n)
          (a := ((2 * L + 5) * (L * (2 * S)))) (b := L)
          (A := (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S)))) (B := c + 3) hProd2 hL
      have hProd1 :
          ((2 * L + 4) * (2 * S)) ≤ n ^ (((1 + (c + 3)) + 2 + 1) + (1 + S)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2 * L + 4) (b := 2 * S)
          (A := ((1 + (c + 3)) + 2 + 1)) (B := (1 + S)) h2L4 h2S
      have hT5 : ((2 * L + 4) * (2 * S)) * S ≤
          n ^ ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S) := by
        exact mul_le_pow_of_le_pow (n := n) (a := ((2 * L + 4) * (2 * S))) (b := S)
          (A := (((1 + (c + 3)) + 2 + 1) + (1 + S))) (B := S) hProd1 hS
      have h12 : ((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1) ≤
          n ^ ((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) := by
        exact add_le_pow_of_le_pow (n := n)
          (a := ((2 * L + 4) * (2 * S) + 5))
          (b := ((2 * L + 5) * (L * (2 * S)) + 1))
          (A := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1))
          (B := ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1))
          hn2 hT1 hT2
      have h123 :
          (((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L ≤
            n ^ (((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                (2 + (c + 3)) + 1) := by
        exact add_le_pow_of_le_pow (n := n)
          (a := (((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)))
          (b := 4 * L)
          (A := ((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1))
          (B := (2 + (c + 3)))
          hn2 h12 hT3
      have h1234 :
          ((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
              ((2 * L + 5) * (L * (2 * S))) * L ≤
            n ^ ((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                (2 + (c + 3)) + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1) := by
        exact add_le_pow_of_le_pow (n := n)
          (a := ((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L))
          (b := ((2 * L + 5) * (L * (2 * S))) * L)
          (A := (((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                (2 + (c + 3)) + 1))
          (B := ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)))
          hn2 h123 hT4
      have h12345 :
          (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
              ((2 * L + 5) * (L * (2 * S))) * L) + ((2 * L + 4) * (2 * S)) * S ≤
            n ^ kBudget := by
        have hRaw :
            (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
                ((2 * L + 5) * (L * (2 * S))) * L) + ((2 * L + 4) * (2 * S)) * S ≤
              n ^ (((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                  (2 + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S) + 1) := by
          exact add_le_pow_of_le_pow (n := n)
            (a := (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
                  ((2 * L + 5) * (L * (2 * S))) * L))
            (b := ((2 * L + 4) * (2 * S)) * S)
            (A := ((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                  (2 + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1))
            (B := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S))
            hn2 h1234 hT5
        have hk :
            ((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                  (2 + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S) + 1
              = kBudget := by
          simp [kBudget, E1, E2, E3, E4, E5, Nat.add_assoc]
        rw [← hk]
        exact hRaw
      have hBudgetPow :
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
            n ^ (kBudget + 3) := by
        let oldBudget : Nat :=
          (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
            ((2 * L + 5) * (L * (2 * S))) * L) + ((2 * L + 4) * (2 * S)) * S
        have hOld : oldBudget ≤ n ^ kBudget := by
          simpa [oldBudget] using h12345
        have hOld' : oldBudget ≤ n ^ (kBudget + 1) := by
          exact Nat.le_trans hOld (Nat.pow_le_pow_right hnPos (Nat.le_add_right kBudget 1))
        have hL' : L ≤ n ^ (kBudget + 1) := by
          exact Nat.le_trans hL (Nat.pow_le_pow_right hnPos (by omega))
        have hS' : S ≤ n ^ (kBudget + 1) := by
          exact Nat.le_trans hS (Nat.pow_le_pow_right hnPos (by omega))
        have hSum :
            oldBudget + L + S ≤ n ^ (kBudget + 1) + n ^ (kBudget + 1) + n ^ (kBudget + 1) := by
          have hTmp1 : oldBudget + L ≤ n ^ (kBudget + 1) + n ^ (kBudget + 1) :=
            Nat.add_le_add hOld' hL'
          have hTmp2 : oldBudget + L + S ≤
              (n ^ (kBudget + 1) + n ^ (kBudget + 1)) + n ^ (kBudget + 1) :=
            Nat.add_le_add hTmp1 hS'
          simpa [Nat.add_assoc] using hTmp2
        have hThree : n ^ (kBudget + 1) + n ^ (kBudget + 1) + n ^ (kBudget + 1) = 3 * n ^ (kBudget + 1) := by
          omega
        have h3le : 3 ≤ n ^ 2 := by
          have h4 : 4 ≤ n * n := Nat.mul_le_mul hn2 hn2
          exact Nat.le_trans (by decide : 3 ≤ 4) (by simpa [pow_two] using h4)
        have hMul : 3 * n ^ (kBudget + 1) ≤ n ^ 2 * n ^ (kBudget + 1) := Nat.mul_le_mul_right _ h3le
        have hPow : n ^ 2 * n ^ (kBudget + 1) = n ^ (kBudget + 3) := by
          calc
            n ^ 2 * n ^ (kBudget + 1) = n ^ (2 + (kBudget + 1)) := by
              simp [Nat.pow_add]
            _ = n ^ (kBudget + 3) := by
              have hk : 2 + (kBudget + 1) = kBudget + 3 := by omega
              simp [hk]
        have hBudgetUpper :
            Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
              oldBudget + L + S := by
          have hHeadSplit :
              (((2 * L + 5) * (L * (2 * S)) + 1) * L) =
                ((2 * L + 5) * (L * (2 * S))) * L + L := by
            rw [Nat.add_mul]
            simp
          have hStateSplit :
              (((2 * L + 4) * (2 * S) + 1) * S) =
                ((2 * L + 4) * (2 * S)) * S + S := by
            rw [Nat.add_mul]
            simp
          dsimp [oldBudget, L, S]
          unfold Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded
          rw [hHeadSplit, hStateSplit]
          apply le_of_eq
          ac_rfl
        calc
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n
              ≤ oldBudget + L + S := hBudgetUpper
          _ ≤ n ^ (kBudget + 1) + n ^ (kBudget + 1) + n ^ (kBudget + 1) := hSum
          _ = 3 * n ^ (kBudget + 1) := hThree
          _ ≤ n ^ 2 * n ^ (kBudget + 1) := hMul
          _ = n ^ (kBudget + 3) := hPow
      have hMul :
          M.runTime n *
              Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
            n ^ ((c + 1) + (kBudget + 3)) := by
        exact mul_le_pow_of_le_pow (n := n)
          (a := M.runTime n)
          (b := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n)
          (A := c + 1) (B := kBudget + 3) hRunPow hBudgetPow
      have hMain :
          2 + M.runTime n *
              Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
            n ^ kCore := by
        have hRaw :
            2 + M.runTime n *
                Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
              n ^ (1 + ((c + 1) + (kBudget + 3)) + 1) := by
          exact add_le_pow_of_le_pow (n := n) (a := 2)
            (b := M.runTime n *
              Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n)
            (A := 1) (B := (c + 1) + (kBudget + 3)) hn2 hTwo hMul
        have hk : 1 + ((c + 1) + (kBudget + 3)) + 1 = kCore := by
          simp [kCore]
        simpa [hk] using hRaw
      have hkCore : kCore ≤ max kCore (max v0 v1) := Nat.le_max_left _ _
      have hPowLift : n ^ kCore ≤ n ^ (max kCore (max v0 v1)) :=
        Nat.pow_le_pow_right hnPos hkCore
      exact Nat.le_trans hMain (Nat.le_trans hPowLift (Nat.le_add_right _ _))

theorem compiledRuntimeCircuitSizeBoundLinear_internal :
    CompiledRuntimeCircuitSizeBoundLinear := by
  intro M c hRun
  rcases compiledRuntimeBudgetPolyBound_internal M c hRun with ⟨k, hk⟩
  refine ⟨k + 2, ?_⟩
  intro n
  have hIter :
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit.gates ≤
        2 + M.runTime n *
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n :=
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear_gates_le_budgetExpanded
      (M := M) (n := n)
  have hGates :
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit.gates ≤
        n ^ k + k := Nat.le_trans hIter (hk n)
  have hSize :
      (toDag
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit).size ≤
        (n ^ k + k) + 1 := by
    simpa [size_toDag, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right hGates 1
  have hTarget :
      (n ^ k + k) + 1 ≤ n ^ (k + 2) + (k + 2) := by
    by_cases hn : n = 0
    · subst hn
      cases k with
      | zero =>
          simp
      | succ k' =>
          simp
    · have hpow : n ^ k ≤ n ^ (k + 2) := by
        have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        simpa [Nat.add_assoc] using Nat.pow_le_pow_right h1 (Nat.le_add_right k 2)
      have hk1 : k + 1 ≤ k + 2 := Nat.le_succ (k + 1)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_le_add hpow hk1
  exact le_trans hSize hTarget

theorem compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider
    (hStepLinear :
      ∀ (M : TM) (n : Nat),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.StepCompiledLinearCandidateStepSpecProvider M n) :
    CompiledRuntimeAcceptCorrectnessLinear := by
  intro M n x
  have hRun :
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
        (sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n)
        (f := fun y => M.run (n := n) y) := by
    have hRunRaw :
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
          (sc := Nat.iterate
            (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate M)
            (M.runTime n)
            (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.initialStraightConfig M n))
          (f := fun y => M.run (n := n) y) :=
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtime_spec_of_stepCompiledLinearCandidateStepSpecProvider
        (M := M) (n := n) (hStep := hStepLinear M n)
    simpa [Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear,
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinear] using hRunRaw
  exact
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf_spec_of_runSpec
      (M := M) (n := n)
      (sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n)
      hRun x

/--
Closed internal witness for linear-route output-wire evaluator agreement.
-/
theorem compiledAcceptOutputWireAgreementLinear_internal :
    CompiledAcceptOutputWireAgreementLinear := by
  intro M n x
  let sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n
  simpa [sc] using
    (Pnp3.Internal.PsubsetPpoly.StraightLine.adapter_evalWire_eq_evalWire
      (C := sc.circuit)
      (x := x)
      (i := sc.state M.accept))

/--
Linear compiled-runtime contract bundle with the narrower output-wire
agreement surface.
-/
def PsubsetPpolyCompiledRuntimeLinearOutputContracts : Prop :=
  CompiledAcceptOutputWireAgreementLinear ∧
    CompiledRuntimeCircuitSizeBoundLinear ∧
    CompiledRuntimeAcceptCorrectnessLinear

private theorem p_subset_PpolyDAG_of_compiledRuntimeLinearContracts
    (hEval : CompiledAcceptCircuitEvalAgreementLinear)
    (hSize : CompiledRuntimeCircuitSizeBoundLinear)
    (hCorrectLinear : CompiledRuntimeAcceptCorrectnessLinear) :
    P_subset_PpolyDAG := by
  refine P_subset_PpolyDAG_of_P_subset_PpolyStraightLine ?_
  intro L hPL
  rcases exists_poly_tm_for_P (L := L) hPL with ⟨M, c, hRun, hLangCorrect⟩
  rcases hSize M c hRun with ⟨k, hk⟩
  refine ⟨({
    polyBound := fun n => n ^ k + k
    polyBound_poly := ⟨k, by
      intro n
      exact Nat.le_refl _⟩
    family := fun n =>
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n)
    family_size_le := by
      intro n
      have hSizeBase :
          (toDag
            (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit).size ≤
              n ^ k + k := hk n
      simpa [size_toDag, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf] using hSizeBase
    correct := by
      intro n x
      let Cacc : StraightLineCircuit n :=
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M
          (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n)
      calc
        eval Cacc x =
            Pnp3.Internal.PsubsetPpoly.StraightLine.eval Cacc x := hEval M n x
        _ = TM.accepts M n x := by simpa [Cacc] using hCorrectLinear M n x
        _ = L n x := hLangCorrect n x
  } : InPpolyStraightLine L), trivial⟩

theorem proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts
    (hContracts : PsubsetPpolyCompiledRuntimeLinearOutputContracts) :
    P_subset_PpolyDAG := by
  rcases hContracts with ⟨hOut, hSize, hCorrectLinear⟩
  exact p_subset_PpolyDAG_of_compiledRuntimeLinearContracts
    (compiledAcceptEvalAgreementLinear_of_outputWireAgreement hOut)
    hSize
    hCorrectLinear

/--
No-arg internal closure endpoint for the active linear compiled-runtime route.
-/
theorem proved_P_subset_PpolyDAG_internal :
    P_subset_PpolyDAG := by
  exact proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts
    ⟨ compiledAcceptOutputWireAgreementLinear_internal
    , compiledRuntimeCircuitSizeBoundLinear_internal
    , compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidateStepSpecProvider_internal ⟩

/--
Audit helper: the no-arg endpoint is definitionally the linear output/step
provider closure route.
-/
theorem proved_P_subset_PpolyDAG_internal_defeq_linear :
    proved_P_subset_PpolyDAG_internal =
      proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts
        ⟨ compiledAcceptOutputWireAgreementLinear_internal
        , compiledRuntimeCircuitSizeBoundLinear_internal
        , compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider
            Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidateStepSpecProvider_internal ⟩ :=
  rfl

end Simulation
end Complexity
end Pnp3
