import UniformClassBridgeClosure.TM0RunCircuit

/-! Direct literal-TM0 circuit family. OrdinaryPpolyDAG now composes this
family with the actual model transport proved in TM0OrdinaryTrace, yielding
unconditional same-language Ordinary.UniformP to canonical PpolyDAG. No simulator
assumption is added here, and the differently typed legacy bridge remains unfilled. -/
namespace UniformClassBridgeClosure.TM0DAG.Window
open Turing Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit

private def rawBound (q B : Nat) : Nat :=
  2+24*q+(B+1)*(12*q+6*(2*(B+1)+1))*(1+144*q)+6*(12*q+6*(2*(B+1)+1))

private def coefficient (q : Nat) : Nat :=
  (2+24*q)+(12*q+18)*(1+144*q)+6*(12*q+18)

private theorem bound_square (q B : Nat) : rawBound q B ≤ coefficient q*(B+2)^2 := by
  unfold rawBound coefficient
  nlinarith [Nat.zero_le (q^2*B^2),Nat.zero_le (q^2*B),Nat.zero_le (q*B^2)]

private theorem absorb (K e : Nat) : ∃ d : Nat, ∀ N : Nat, K*(N+1)^e ≤ N^d+d := by
  let d := K+2*e+K*2^e+1
  refine ⟨d,?_⟩
  intro N
  rcases N with _ | _ | N
  · simp only [Nat.zero_add,one_pow,mul_one]
    dsimp [d];omega
  · change K*2^e ≤ 1^d+d
    rw [Nat.one_pow]
    dsimp [d];omega
  · have hn : 2 ≤ N+2 := by omega
    have hc : K ≤ (N+2)^K := by
      cases K with
      | zero => simp
      | succ k =>
        have hk : k+1 < 2^(k+1) := Nat.lt_two_pow_self
        exact Nat.le_trans (Nat.le_of_lt hk) (Nat.pow_le_pow_left hn (k+1))
    have hs : N+2+1 ≤ (N+2)^2 := by nlinarith
    have hp := Nat.pow_le_pow_left hs e
    calc
      K*(N+2+1)^e ≤ (N+2)^K*((N+2)^2)^e := Nat.mul_le_mul hc hp
      _ = (N+2)^(K+2*e) := by rw [← pow_mul,← pow_add]
      _ ≤ (N+2)^d := Nat.pow_le_pow_right (by omega) (by dsimp [d];omega)
      _ ≤ _ := Nat.le_add_right _ _

/-- One machine/clock-dependent exponent works for every raw length, including 0 and 1. -/
theorem raw_size_polynomial {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (accept : Λ) (c : Nat) :
    ∃ d : Nat, ∀ N : Nat, (rawCircuit labels T accept (N^c+c) N).size ≤ N^d+d := by
  obtain ⟨d,hd⟩ := absorb (coefficient labels.length*(c+3)^2) (2*c)
  refine ⟨d,fun N => ?_⟩
  have hp : 1 ≤ (N+1)^c := Nat.one_le_pow c (N+1) (by omega)
  have hn : N^c ≤ (N+1)^c := Nat.pow_le_pow_left (by omega) c
  have hs : N^c+c+2 ≤ (c+3)*(N+1)^c := by nlinarith
  calc
    _ ≤ rawBound labels.length (N^c+c) := raw_circuit_size labels T accept (N^c+c) N
    _ ≤ coefficient labels.length*(N^c+c+2)^2 := bound_square _ _
    _ ≤ coefficient labels.length*((c+3)*(N+1)^c)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
    _ = (coefficient labels.length*(c+3)^2)*(N+1)^(2*c) := by ring
    _ ≤ N^d+d := hd N

/-- Literal raw TM0 halting correctness suffices for the canonical same-language DAG class.
The operational premise is used only to prove correctness, never as construction data. -/
theorem literal_decider_ppolyDAG (L : Language) {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (accept reject : Λ) (different : accept ≠ reject) (c : Nat)
    (decides : ∀ N (y : Bitstring N), ∃ (t : Nat) (last : TM0.Cfg Symbol Λ),
      t ≤ N^c+c ∧ rawTrace T t (inputConfig y) = some last ∧
      last.q = (if L N y then accept else reject) ∧ TM0.step T last = none) :
    Pnp3.ComplexityInterfaces.PpolyDAG L := by
  obtain ⟨d,hd⟩ := raw_size_polynomial labels T accept c
  refine ⟨{
    polyBound := fun N => N^d+d
    polyBound_poly := ⟨d,fun _ => Nat.le_refl _⟩
    family := fun N => rawCircuit labels T accept (N^c+c) N
    family_size_le := hd
    correct := ?_},trivial⟩
  intro N y
  obtain ⟨t,last,ht,htrace,hverdict,hstop⟩ := decides N y
  exact raw_circuit_correct labels complete T accept reject different (N^c+c) N y
    (L N y) t last ht htrace hverdict hstop

-- SG4_LITERAL_AUDIT: mechanical checks, not independent mathematical reproof.
theorem check_raw_size_polynomial {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (accept : Λ) (c : Nat) :
    ∃ d : Nat, ∀ N : Nat, (rawCircuit labels T accept (N^c+c) N).size ≤ N^d+d :=
  raw_size_polynomial labels T accept c

theorem check_literal_decider_ppolyDAG (L : Language) {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (accept reject : Λ) (different : accept ≠ reject) (c : Nat)
    (decides : ∀ N (y : Bitstring N), ∃ (t : Nat) (last : TM0.Cfg Symbol Λ),
      t ≤ N^c+c ∧ rawTrace T t (inputConfig y) = some last ∧
      last.q = (if L N y then accept else reject) ∧ TM0.step T last = none) :
    Pnp3.ComplexityInterfaces.PpolyDAG L :=
  literal_decider_ppolyDAG L labels complete T accept reject different c decides

#check (@rawBound : ∀ (_q _B : Nat),
    Nat)
#check (@coefficient : ∀ (_q : Nat),
    Nat)
#check (@bound_square : ∀ (_q _B : Nat),
    rawBound _q _B ≤ coefficient _q*(_B+2)^2)
#check (@absorb : ∀ (_K _e : Nat),
    ∃ d : Nat, ∀ N : Nat, _K*(N+1)^_e ≤ N^d+d)
#check (@raw_size_polynomial : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_accept : _Λ) (_c : Nat),
    ∃ d : Nat, ∀ N : Nat, (rawCircuit _labels _T _accept (N^_c+_c) N).size ≤ N^d+d)
#check (@literal_decider_ppolyDAG : ∀ (_L : Language) {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_accept _reject : _Λ) (_different : _accept ≠ _reject) (_c : Nat)
    (_decides : ∀ N (y : Bitstring N), ∃ (t : Nat) (last : TM0.Cfg Symbol _Λ),
      t ≤ N^_c+_c ∧ rawTrace _T t (inputConfig y) = some last ∧
      last.q = (if _L N y then _accept else _reject) ∧ TM0.step _T last = none),
    Pnp3.ComplexityInterfaces.PpolyDAG _L)
#check (@check_raw_size_polynomial : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_accept : _Λ) (_c : Nat),
    ∃ d : Nat, ∀ N : Nat, (rawCircuit _labels _T _accept (N^_c+_c) N).size ≤ N^d+d)
#check (@check_literal_decider_ppolyDAG : ∀ (_L : Language) {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_accept _reject : _Λ) (_different : _accept ≠ _reject) (_c : Nat)
    (_decides : ∀ N (y : Bitstring N), ∃ (t : Nat) (last : TM0.Cfg Symbol _Λ),
      t ≤ N^_c+_c ∧ rawTrace _T t (inputConfig y) = some last ∧
      last.q = (if _L N y then _accept else _reject) ∧ TM0.step _T last = none),
    Pnp3.ComplexityInterfaces.PpolyDAG _L)
#print axioms rawBound
#print axioms coefficient
#print axioms bound_square
#print axioms absorb
#print axioms raw_size_polynomial
#print axioms literal_decider_ppolyDAG
#print axioms check_raw_size_polynomial
#print axioms check_literal_decider_ppolyDAG

end UniformClassBridgeClosure.TM0DAG.Window
