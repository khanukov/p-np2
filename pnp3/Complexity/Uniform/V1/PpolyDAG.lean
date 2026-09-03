import Complexity.Uniform.V1.StepBundle
import Complexity.Uniform.V1.PolynomialTime

/-!
# Uniform V1 run circuits and the PpolyDAG bridge

The compiler is fixed by `M`, `c`, and `n`.  In particular, neither a language
nor a decision proof is construction data.
-/

namespace Pnp3.Complexity.Uniform.V1.Circuit

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-- Iterate the direct step bundle for exactly the pinned polynomial clock. -/
def clockedRunBundle (M : UniformTM) (c n : Nat) :
    EncodedConfig M n (polyClock c n) :=
  let b := polyClock c n
  runBundle M n b (stepBundle M n b) b

/-- The accepting-state output of the fixed clocked run bundle. -/
def runCircuit (M : UniformTM) (c n : Nat) : DagCircuit n :=
  (clockedRunBundle M c n).asCircuit
    (stateIndex M n (polyClock c n) M.accept)

/-- One explicit exponent dominating the complete run circuit at every input
length, including zero and one. -/
def runCircuitExponent (M : UniformTM) (c : Nat) : Nat :=
  3 + (c + 1) * (19 * c + 16 * M.stateCount + 70)

/-- Exact shared-gate count of the clocked accepting circuit. -/
@[simp] theorem runCircuit_gates (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).gates =
      2 + polyClock c n * (stepBundle M n (polyClock c n)).gates := by
  change (clockedRunBundle M c n).gates = _
  simp [clockedRunBundle]

/-- Exact size, including the single designated-output accounting node. -/
@[simp] theorem runCircuit_size (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).size =
      3 + polyClock c n * (stepBundle M n (polyClock c n)).gates := by
  rw [DagCircuit.size, runCircuit_gates]
  omega

/-- Raw size bound before polynomial domination. -/
theorem runCircuit_size_le_raw (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).size ≤
      3 + polyClock c n *
        (19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13) := by
  rw [runCircuit_size]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left (polyClock c n)
      (by simpa [tapeLength] using stepBundle_gates_le M n (polyClock c n))) 3

/-- Acceptance of the selected output is literal exact-deadline acceptance. -/
theorem runCircuit_accept_iff (M : UniformTM) (c n : Nat)
    (x : Bitstring n) :
    eval (runCircuit M c n) x = true ↔
      AcceptsAt M (polyClock c n) (polyClock c n) x := by
  let b := polyClock c n
  simpa [runCircuit, clockedRunBundle, DagBundle.evalOutput, b] using
    (runBundle_accept_iff M (stepBundle M n b)
      (stepBundle_spec M n b) b x)

/-- A literal exact decision fixes the circuit output.  The false branch uses
literal rejection and terminal-state exclusivity; mere nonacceptance is never
accepted as a false verdict. -/
theorem runCircuit_eval_of_decidesAt (M : UniformTM) (c n : Nat)
    (x : Bitstring n) (answer : Bool)
    (h : DecidesAt M (polyClock c n) (polyClock c n) x answer) :
    eval (runCircuit M c n) x = answer := by
  cases answer with
  | false =>
      have hr : RejectsAt M (polyClock c n) (polyClock c n) x := by
        simpa [DecidesAt] using h
      cases heval : eval (runCircuit M c n) x with
      | false => rfl
      | true =>
          exfalso
          exact not_acceptsAt_and_rejectsAt M x
            ⟨(runCircuit_accept_iff M c n x).1 heval, hr⟩
  | true =>
      apply (runCircuit_accept_iff M c n x).2
      simpa [DecidesAt] using h

private theorem const_le_pow_of_two_le {n : Nat} (hn2 : 2 ≤ n) (m : Nat) :
    m ≤ n ^ m := by
  cases m with
  | zero => simp
  | succ m =>
      have hlt : Nat.succ m < 2 ^ Nat.succ m := Nat.lt_two_pow_self
      exact Nat.le_trans (Nat.le_of_lt hlt)
        (Nat.pow_le_pow_left hn2 (m + 1))

private theorem add_le_pow_of_le_pow {n a b A B : Nat}
    (hn2 : 2 ≤ n) (ha : a ≤ n ^ A) (hb : b ≤ n ^ B) :
    a + b ≤ n ^ (A + B + 1) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn2
  have ha' : a ≤ n ^ (A + B) :=
    Nat.le_trans ha (Nat.pow_le_pow_right hn1 (Nat.le_add_right A B))
  have hb' : b ≤ n ^ (A + B) :=
    Nat.le_trans hb (Nat.pow_le_pow_right hn1 (Nat.le_add_left B A))
  calc
    a + b ≤ n ^ (A + B) + n ^ (A + B) := Nat.add_le_add ha' hb'
    _ = 2 * n ^ (A + B) := by omega
    _ ≤ n * n ^ (A + B) := Nat.mul_le_mul_right _ hn2
    _ = n ^ (A + B + 1) := by simp [Nat.pow_succ, Nat.mul_comm]

private theorem mul_le_pow_of_le_pow {n a b A B : Nat}
    (ha : a ≤ n ^ A) (hb : b ≤ n ^ B) :
    a * b ≤ n ^ (A + B) := by
  calc
    a * b ≤ n ^ A * n ^ B := Nat.mul_le_mul ha hb
    _ = n ^ (A + B) := by simp [Nat.pow_add]

private theorem polyClock_le_pow_succ {c n : Nat} (hn2 : 2 ≤ n) :
    polyClock c n ≤ n ^ (c + 1) := by
  have hc : c ≤ n ^ c := const_le_pow_of_two_le hn2 c
  calc
    polyClock c n = n ^ c + c := rfl
    _ ≤ n ^ c + n ^ c := Nat.add_le_add_left hc _
    _ = 2 * n ^ c := by omega
    _ ≤ n * n ^ c := Nat.mul_le_mul_right _ hn2
    _ = n ^ (c + 1) := by simp [Nat.pow_succ, Nat.mul_comm]

private theorem tapeLength_clock_le_pow {c n : Nat} (hn2 : 2 ≤ n) :
    n + polyClock c n + 1 ≤ n ^ (c + 3) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn2
  have hn : n ≤ n ^ (c + 1) := Nat.le_self_pow (Nat.succ_ne_zero c) n
  have hb := polyClock_le_pow_succ (c := c) hn2
  have h3 : 3 ≤ n ^ 2 := by
    have h4 : 4 ≤ n * n := Nat.mul_le_mul hn2 hn2
    exact Nat.le_trans (by decide : 3 ≤ 4) (by simpa [pow_two] using h4)
  calc
    n + polyClock c n + 1 ≤
        n ^ (c + 1) + n ^ (c + 1) + n ^ (c + 1) := by omega
    _ = 3 * n ^ (c + 1) := by omega
    _ ≤ n ^ 2 * n ^ (c + 1) := Nat.mul_le_mul_right _ h3
    _ = n ^ (c + 3) := by
      rw [← Nat.pow_add]
      congr 1
      omega

private theorem polyClock_le_small (c n : Nat) (hn : n ≤ 1) :
    polyClock c n ≤ c + 1 := by
  cases n with
  | zero => cases c <;> simp [polyClock]
  | succ n =>
      have : n = 0 := by omega
      subst n
      simp [polyClock, Nat.add_comm]

private theorem tapeLength_clock_le_small (c n : Nat) (hn : n ≤ 1) :
    n + polyClock c n + 1 ≤ c + 3 := by
  have := polyClock_le_small c n hn
  omega

private theorem runCircuit_raw_le_exponent_small (M : UniformTM) (c n : Nat)
    (hn : n ≤ 1) :
    3 + polyClock c n *
        (19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13) ≤
      runCircuitExponent M c := by
  have hb := polyClock_le_small c n hn
  have htape := tapeLength_clock_le_small c n hn
  have hstep :
      19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13 ≤
        19 * (c + 3) + 16 * M.stateCount + 13 := by omega
  have hproduct := Nat.mul_le_mul hb hstep
  have hcoefficient :
      19 * (c + 3) + 16 * M.stateCount + 13 =
        19 * c + 16 * M.stateCount + 70 := by omega
  rw [hcoefficient] at hproduct
  unfold runCircuitExponent
  exact Nat.add_le_add_left hproduct 3

private theorem runCircuit_size_le_poly_zero (M : UniformTM) (c : Nat) :
    (runCircuit M c 0).size ≤
      0 ^ runCircuitExponent M c + runCircuitExponent M c := by
  have hpos : 0 < runCircuitExponent M c := by simp [runCircuitExponent]
  rw [Nat.zero_pow hpos, Nat.zero_add]
  exact Nat.le_trans (runCircuit_size_le_raw M c 0)
    (runCircuit_raw_le_exponent_small M c 0 (by omega))

private theorem runCircuit_size_le_poly_one (M : UniformTM) (c : Nat) :
    (runCircuit M c 1).size ≤
      1 ^ runCircuitExponent M c + runCircuitExponent M c := by
  rw [Nat.one_pow, Nat.one_add]
  exact Nat.le_trans
    (Nat.le_trans (runCircuit_size_le_raw M c 1)
      (runCircuit_raw_le_exponent_small M c 1 (by omega)))
    (Nat.le_succ _)

private theorem runCircuit_size_le_poly_large (M : UniformTM) (c n : Nat)
    (hn2 : 2 ≤ n) :
    (runCircuit M c n).size ≤
      n ^ runCircuitExponent M c + runCircuitExponent M c := by
  let K := 19 + (c + 3) + (16 * M.stateCount + 13) + 1
  let E := 3 + ((c + 1) + K) + 1
  have h19 : 19 ≤ n ^ 19 := const_le_pow_of_two_le hn2 19
  have htape : n + polyClock c n + 1 ≤ n ^ (c + 3) :=
    tapeLength_clock_le_pow hn2
  have htapeTerm : 19 * (n + polyClock c n + 1) ≤ n ^ (19 + (c + 3)) :=
    mul_le_pow_of_le_pow h19 htape
  have hconstant : 16 * M.stateCount + 13 ≤
      n ^ (16 * M.stateCount + 13) :=
    const_le_pow_of_two_le hn2 _
  have hstep :
      19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13 ≤ n ^ K := by
    simpa [K, Nat.add_assoc] using
      add_le_pow_of_le_pow hn2 htapeTerm hconstant
  have hclock : polyClock c n ≤ n ^ (c + 1) := polyClock_le_pow_succ hn2
  have hproduct : polyClock c n *
      (19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13) ≤
        n ^ ((c + 1) + K) :=
    mul_le_pow_of_le_pow hclock hstep
  have hthree : 3 ≤ n ^ 3 := const_le_pow_of_two_le hn2 3
  have hraw : 3 + polyClock c n *
      (19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13) ≤ n ^ E := by
    exact add_le_pow_of_le_pow hn2 hthree hproduct
  have hE : E ≤ runCircuitExponent M c := by
    dsimp [E, K, runCircuitExponent]
    nlinarith
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn2
  calc
    (runCircuit M c n).size ≤
        3 + polyClock c n *
          (19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13) :=
      runCircuit_size_le_raw M c n
    _ ≤ n ^ E := hraw
    _ ≤ n ^ runCircuitExponent M c := Nat.pow_le_pow_right hn1 hE
    _ ≤ n ^ runCircuitExponent M c + runCircuitExponent M c :=
      Nat.le_add_right _ _

/-- The explicit exponent bounds the concrete run circuit for every length. -/
theorem runCircuit_size_le_poly (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).size ≤
      n ^ runCircuitExponent M c + runCircuitExponent M c := by
  cases n with
  | zero => exact runCircuit_size_le_poly_zero M c
  | succ n =>
      cases n with
      | zero => exact runCircuit_size_le_poly_one M c
      | succ n => exact runCircuit_size_le_poly_large M c (n + 2) (by omega)

end Pnp3.Complexity.Uniform.V1.Circuit

namespace Pnp3.Complexity.Uniform.V1

open Pnp3.ComplexityInterfaces
open Circuit

/-- Every language in the versioned `UniformP` class has a concrete
polynomial-size canonical DAG family. -/
theorem uniformP_subset_PpolyDAG :
    ∀ L : Language, UniformP L → Pnp3.ComplexityInterfaces.PpolyDAG L := by
  intro L hL
  rcases (uniformP_iff_exists_decidesAt L).1 hL with ⟨M, c, hM⟩
  refine ⟨{
    polyBound := fun n => n ^ runCircuitExponent M c + runCircuitExponent M c
    polyBound_poly := ⟨runCircuitExponent M c, fun n => Nat.le_refl _⟩
    family := runCircuit M c
    family_size_le := runCircuit_size_le_poly M c
    correct := ?_ }, trivial⟩
  intro n x
  exact runCircuit_eval_of_decidesAt M c n x (L n x) (hM n x)

end Pnp3.Complexity.Uniform.V1
