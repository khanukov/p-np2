/-
  NP membership for concrete global language
  
  Constructive proof using explicit TM witness for circuit verification.
  
  For baseParams with sYES=1, only n+2 circuits exist (input 0..n-1, const true, const false).
  The TM verifies by enumerating and checking consistency.
-/
import MistralTestLib.SourceTheorems.ConcreteFamily
import Pnp3.Models.Model_PartialMCSP

namespace MistralTestLib.ConcreteGlobalNP

open Pnp3.Models Pnp3.ComplexityInterfaces Pnp3.Core
open Pnp3.Internal.PsubsetPpoly

/-! Circuit enumeration for size ≤ 1 -/

-- Enumerate all circuits of size ≤ 1 on n inputs
-- Index 0..n-1: input j
-- Index n: const true
-- Index n+1: const false
private def enumerateCircuit (n j : Nat) : Models.Circuit n :=
  if h : j < n then Models.Circuit.input ⟨j, h⟩
  else if j = n then Models.Circuit.const true
  else Models.Circuit.const false

private theorem enumerateCircuit_surjective (n : Nat) (C : Models.Circuit n) (hC : C.size ≤ 1) :
    ∃ j < n + 2, enumerateCircuit n j = C := by
  cases C with
  | input i => 
    use i.val, Nat.lt_succ_of_lt i.isLt
    simp [enumerateCircuit]
    split_ifs <;> try rfl
    omega
  | const b => 
    by_cases hb : b = true
    · subst hb
      use n, Nat.lt_succ_self n
      simp [enumerateCircuit]
      split_ifs <;> try rfl
      all_goals omega
    · have : b = false := Bool.eq_false_of_ne_true hb
      subst this
      use n + 1
      simp [enumerateCircuit]
      split_ifs <;> try rfl
      all_goals omega
  | not c => 
    have : 1 ≤ c.size := by
      have := Nat.succ_le_iff.mpr (Nat.zero_le _)
      omega
    have : c.size + 1 ≤ 1 := by omega
    have : c.size ≤ 0 := by omega
    have : c.size = 0 := by omega
    -- Circuit of size 0 doesn't exist in our definition
    exfalso
    cases c
  | and c1 c2 =>
    have : 1 ≤ c1.size + c2.size + 1 := by omega
    have : c1.size + c2.size + 1 ≤ 1 := by omega
    have : c1.size = 0 ∧ c2.size = 0 := by omega
    exfalso
    cases c1 <;> cases c2
  | or c1 c2 =>
    have : 1 ≤ c1.size + c2.size + 1 := by omega
    have : c1.size + c2.size + 1 ≤ 1 := by omega
    have : c1.size = 0 ∧ c2.size = 0 := by omega
    exfalso
    cases c1 <;> cases c2

/-! Boolean consistency check -/

private def isConsistentBool (n : Nat) (C : Models.Circuit n) (T : Models.PartialTruthTable n) : Bool :=
  (List.finRange (Models.Partial.tableLen n)).all fun i =>
    match T i with | none => true | some b => Models.Circuit.eval C (Pnp3.Core.vecOfNat n i.val) == b

private theorem isConsistentBool_of_isConsistent (n : Nat) (C : Models.Circuit n) (T : Models.PartialTruthTable n) :
    Models.is_consistent C T → isConsistentBool n C T = true := by
  intro hCons
  unfold isConsistentBool
  refine List.all_eq_true.mpr ?_
  intro i _
  cases hTi : T i with
  | none => simp
  | some b =>
      have hAt := hCons (Core.vecOfNat n i.val)
      have hIdx : Models.assignmentIndex (Core.vecOfNat n i.val) = i := Models.assignmentIndex_vecOfNat_eq i
      have hEval : Models.Circuit.eval C (Core.vecOfNat n i.val) = b := by
        have hAt' := hAt
        simpa [Models.is_consistent, hIdx, hTi] using hAt'
      simp [hEval]

/-! Main NP proof -/

/--
Concrete global language ∈ NP.

For baseParams with sYES=1:
- Only n+2 circuits of size ≤ 1 exist
- Certificate encodes circuit index j ∈ {0, ..., n+1}
- Verifier: check enumerateCircuit n j is consistent with decoded table
- Runtime: O(n · 2^n) = O(N log N) where N = input length, polynomial

Using classical logic to obtain witness.
-/
theorem concreteGlobalLanguage_in_NP : 
    ComplexityInterfaces.NP 
      (fun N x =>
        let n_of_N := Nat.find (fun k => 2^(k+1) = N) 0
        if h : ∃ k, 2^(k+1)=N ∧ 8≤k 
        then Models.gapPartialMCSP_Language (SourceTheorems.concreteFamily.paramsOf n_of_N 0) N x 
        else false) := by
  classical
  unfold ComplexityInterfaces.NP ComplexityInterfaces.NP_TM
  
  -- Parameters for the TM witness
  let k_cert : Nat := 1  -- Certificate is a circuit index, encoded in k bits
  let c_exp : Nat := 5  -- Runtime exponent: (n + cert)^5 + 5 bounds n·2^n
  
  -- Certificate length: enough to encode any circuit index for any n
  -- For baseParams, n ≥ 8, and we have n+2 circuits, so we need log2(n+2) bits
  -- We use a fixed certificate length that works for all n ≥ 8
  let cert_len : Nat -> Nat := fun n => n + 2  -- Generous bound: n+2 bits
  
  -- Define the TM
  -- State encodes: phase (parse/prove), current circuit index, current assignment, current bit
  inductive VerifierState : Type where
    | parseCertStart : VerifierState      -- Start parsing certificate
    | parseCert : Fin (n + 2) → Fin Nat → VerifierState  -- Parsing cert bit by bit
    | checkAssignmentStart : VerifierState  -- Start checking assignments
    | checkAssignment : Fin (2^n) → VerifierState  -- Current assignment
    | checkBit : Fin (2^n) → Fin n → VerifierState  -- Current bit of current assignment
    | verifyCircuit : VerifierState        -- Verify circuit evaluation
    | acceptState : VerifierState
    | rejectState : VerifierState
  
  sorry  -- Need to complete TM definition
