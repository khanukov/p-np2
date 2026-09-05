import Mathlib.Tactic
import Complexity.Uniform.V1.Relation
import Complexity.Uniform.V1.CombinedMachine
import Complexity.Uniform.V1.BudgetTransport

/-!
# Sharp-clock correctness of the routed combined machine

The parser prefix and verifier suffix execute in one `run` on one ambient
`Config`.  `run_add` is used only to decompose that run in the proof.
-/

namespace Pnp3.Complexity.Uniform.V1
namespace FixedParserVerifier

open PairEncoding

/-- Public name used by the B3 packaging theorem.  It is definitionally the
routed B2 constructor; no new machine or restart is introduced. -/
abbrev combinedMachine (V : UniformTM) : UniformTM := machine V

def totalClock (verifierExponent N : Nat) : Nat :=
  FixedPairParser.clock N + polyClock verifierExponent N

/-- The sharp deadline is exactly the parser prefix plus the verifier suffix.
The parser's accepting edge enters `V.start` in its final transition, so no
handoff transition is present in this equation. -/
theorem totalClock_eq (c N : Nat) :
    totalClock c N =
      FixedPairParser.clock N + polyClock c N := by
  rfl

/-- Closed form of the same exact additive deadline. -/
theorem totalClock_closedForm (c N : Nat) :
    totalClock c N = (2 * N + 1) + (N ^ c + c) := by
  rfl

theorem parserClock_le_totalClock (c N : Nat) :
    FixedPairParser.clock N ≤ totalClock c N := by
  simp [totalClock]

theorem verifierClock_le_totalClock (c N : Nat) :
    polyClock c N ≤ totalClock c N := by
  simp [totalClock]

theorem total_tapeLength (c N : Nat) :
    tapeLength N (totalClock c N) =
      3 * N + polyClock c N + 2 := by
  unfold tapeLength totalClock FixedPairParser.clock
  omega

theorem verifier_decidesAt_ambient
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    {N : Nat} (y : Bitstring N) :
    DecidesAt V (totalClock c N) (polyClock c N) y
      (encodedRelationLanguage R N y) := by
  have hsmall :
      DecidesAt V (polyClock c N) (polyClock c N) y
        (encodedRelationLanguage R N y) :=
    (decidesAt_budget_iff_decidesWithin V y
      (encodedRelationLanguage R N y)).2 (hV N y)
  exact V.decidesAt_budget_mono y
    (encodedRelationLanguage R N y) (Nat.le_refl _)
    (verifierClock_le_totalClock c N) hsmall

theorem run_total_split (V : UniformTM) (c : Nat)
    {N : Nat} (y : Bitstring N) :
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
      (machine V).run (polyClock c N)
        ((machine V).run (FixedPairParser.clock N)
          (initialConfig (machine V) (totalClock c N) y)) := by
  exact (machine V).run_add
    (FixedPairParser.clock N) (polyClock c N)
    (initialConfig (machine V) (totalClock c N) y)

/-- On syntactically successful input, the exact total run is literally the
embedded verifier run on the same ambient budget. -/
theorem run_total_of_decodePair_some
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (p : DecodedPair) (hdecode : decodePair y = some p) :
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
      embedConfig V
        (V.run (polyClock c N)
          (initialConfig V (totalClock c N) y)) := by
  calc
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
        (machine V).run (polyClock c N)
          ((machine V).run (FixedPairParser.clock N)
            (initialConfig (machine V) (totalClock c N) y)) :=
      run_total_split V c y
    _ = (machine V).run (polyClock c N)
          (embedConfig V
            (initialConfig V (totalClock c N) y)) := by
      rw [parser_handoff_of_decodePair_some V y
        (parserClock_le_totalClock c N) p hdecode]
    _ = embedConfig V
          (V.run (polyClock c N)
            (initialConfig V (totalClock c N) y)) :=
      run_embed V (polyClock c N)
        (initialConfig V (totalClock c N) y)

/-- On malformed or empty input, the exact total run is the restored initial
configuration with literal combined reject as its state. -/
theorem run_total_of_decodePair_none
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (hdecode : decodePair y = none) :
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
      { initialConfig (machine V) (totalClock c N) y with
        state := (machine V).reject } := by
  let rejected : Config (machine V).stateCount N (totalClock c N) :=
    { initialConfig (machine V) (totalClock c N) y with
      state := (machine V).reject }
  have hr : rejected.state = (machine V).reject := rfl
  calc
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
        (machine V).run (polyClock c N)
          ((machine V).run (FixedPairParser.clock N)
            (initialConfig (machine V) (totalClock c N) y)) :=
      run_total_split V c y
    _ = (machine V).run (polyClock c N) rejected := by
      rw [parser_reject_of_decodePair_none V y
        (parserClock_le_totalClock c N) hdecode]
    _ = rejected := (machine V).run_reject rejected hr (polyClock c N)

/-- The empty raw word is a concrete malformed instance.  Its whole total
run, including the verifier-sized suffix, remains the literal rejecting
configuration by terminal absorption. -/
theorem run_total_empty
    (V : UniformTM) (c : Nat) (y : Bitstring 0) :
    (machine V).run (totalClock c 0)
        (initialConfig (machine V) (totalClock c 0) y) =
      { initialConfig (machine V) (totalClock c 0) y with
        state := (machine V).reject } := by
  let rejected : Config (machine V).stateCount 0 (totalClock c 0) :=
    { initialConfig (machine V) (totalClock c 0) y with
      state := (machine V).reject }
  have hr : rejected.state = (machine V).reject := rfl
  calc
    (machine V).run (totalClock c 0)
        (initialConfig (machine V) (totalClock c 0) y) =
        (machine V).run (polyClock c 0)
          ((machine V).run (FixedPairParser.clock 0)
            (initialConfig (machine V) (totalClock c 0) y)) :=
      run_total_split V c y
    _ = (machine V).run (polyClock c 0) rejected := by
      rw [parser_reject_empty V (totalClock c 0) y
        (parserClock_le_totalClock c 0)]
    _ = rejected := (machine V).run_reject rejected hr (polyClock c 0)

theorem malformed_rejectsAt_parserClock
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (hdecode : decodePair y = none) :
    RejectsAt (machine V) (totalClock c N)
      (FixedPairParser.clock N) y := by
  change
    ((machine V).run (FixedPairParser.clock N)
      (initialConfig (machine V) (totalClock c N) y)).state =
        (machine V).reject
  rw [parser_reject_of_decodePair_none V y
    (parserClock_le_totalClock c N) hdecode]

theorem malformed_rejectsAt_total
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (hdecode : decodePair y = none) :
    RejectsAt (machine V) (totalClock c N) (totalClock c N) y := by
  change
    ((machine V).run (totalClock c N)
      (initialConfig (machine V) (totalClock c N) y)).state =
        (machine V).reject
  rw [run_total_of_decodePair_none V c y hdecode]

theorem combined_decidesAt
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    {N : Nat} (y : Bitstring N) :
    DecidesAt (machine V) (totalClock c N) (totalClock c N) y
      (encodedRelationLanguage R N y) := by
  cases hdecode : decodePair y with
  | none =>
      have hanswer : encodedRelationLanguage R N y = false := by
        simp [encodedRelationLanguage, hdecode]
      rw [hanswer]
      exact malformed_rejectsAt_total V c y hdecode
  | some p =>
      have hv := verifier_decidesAt_ambient V c R hV y
      have hrun := run_total_of_decodePair_some V c y p hdecode
      cases hanswer : encodedRelationLanguage R N y with
      | false =>
          change
            ((machine V).run (totalClock c N)
              (initialConfig (machine V) (totalClock c N) y)).state =
                (machine V).reject
          rw [hrun]
          change inVerifier V
              (V.run (polyClock c N)
                (initialConfig V (totalClock c N) y)).state =
            inVerifier V V.reject
          apply congrArg (inVerifier V)
          simpa [DecidesAt, RejectsAt, hanswer] using hv
      | true =>
          change
            ((machine V).run (totalClock c N)
              (initialConfig (machine V) (totalClock c N) y)).state =
                (machine V).accept
          rw [hrun]
          change inVerifier V
              (V.run (polyClock c N)
                (initialConfig V (totalClock c N) y)).state =
            inVerifier V V.accept
          apply congrArg (inVerifier V)
          simpa [DecidesAt, AcceptsAt, hanswer] using hv

theorem combined_decidesWithin
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    {N : Nat} (y : Bitstring N) :
    DecidesWithin (machine V) (totalClock c N) y
      (encodedRelationLanguage R N y) := by
  exact (decidesAt_budget_iff_decidesWithin
    (machine V) y (encodedRelationLanguage R N y)).1
      (combined_decidesAt V c R hV y)

/-!
The sharp clock is not itself a member of the pinned `polyClock` family.
This deliberately conditional wrapper records the one arithmetic fact needed
for the existing `VerifiesRelation` interface; the sharp theorems above do
not depend on it.
-/
def TotalClockPolynomialDomination (c d : Nat) : Prop :=
  ∀ N, totalClock c N ≤ polyClock d N

private theorem add_le_mul_add_one_of_pos (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) :
    a + b ≤ a * b + 1 := by
  cases a with
  | zero => simp at ha
  | succ a =>
      have hmul : a ≤ a * b := by
        have h := Nat.mul_le_mul_left a hb
        simpa using h
      simp only [Nat.add_mul, Nat.one_mul]
      omega

private theorem two_mul_add_one_le_cube (N : Nat) (hN : 2 ≤ N) :
    2 * N + 1 ≤ N ^ 3 := by
  have hsquare : 3 ≤ N * N := by
    have hmul : 2 * 2 ≤ N * N := Nat.mul_le_mul hN hN
    omega
  have hthree : 3 * N ≤ N ^ 3 := by
    calc
      3 * N ≤ (N * N) * N := Nat.mul_le_mul_right N hsquare
      _ = N ^ 3 := by ring
  omega

/-- `c+3` dominates the sharp clock for all natural input lengths.  The
zero-length cases explicitly respect Lean's `0^0 = 1`. -/
theorem totalClock_le_polyClock_add_three (c N : Nat) :
    totalClock c N ≤ polyClock (c + 3) N := by
  cases N with
  | zero =>
      cases c with
      | zero => norm_num [totalClock, FixedPairParser.clock, polyClock]
      | succ c =>
          simp [totalClock, FixedPairParser.clock, polyClock]
          omega
  | succ N =>
      cases N with
      | zero =>
          simp [totalClock, FixedPairParser.clock, polyClock]
          omega
      | succ N =>
          let n := Nat.succ (Nat.succ N)
          have hn : 2 ≤ n := by omega
          have hlinear : 2 * n + 1 ≤ n ^ 3 :=
            two_mul_add_one_le_cube n hn
          have hpowc : 0 < n ^ c := by
            exact pow_pos (by omega) c
          have hcubic : 0 < n ^ 3 := by
            exact pow_pos (by omega) 3
          have hproduct :=
            add_le_mul_add_one_of_pos (n ^ c) (n ^ 3) hpowc hcubic
          change totalClock c n ≤ polyClock (c + 3) n
          unfold totalClock FixedPairParser.clock polyClock
          rw [pow_add]
          omega

theorem totalClockPolynomialDomination_add_three (c : Nat) :
    TotalClockPolynomialDomination c (c + 3) :=
  totalClock_le_polyClock_add_three c

/-- The tempting exponent `c + 2` is impossible for this exact clock family:
at raw length one the sharp clock is `c + 4`, whereas the proposed standard
clock is only `c + 3`. -/
theorem totalClock_not_le_polyClock_add_two_at_one (c : Nat) :
    ¬ totalClock c 1 ≤ polyClock (c + 2) 1 := by
  simp [totalClock, FixedPairParser.clock, polyClock]
  omega

theorem totalClockPolynomialDomination_add_two_fails (c : Nat) :
    ¬ TotalClockPolynomialDomination c (c + 2) := by
  intro h
  exact totalClock_not_le_polyClock_add_two_at_one c (h 1)

theorem combined_decidesWithin_polyClock
    (V : UniformTM) (c d : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    (hdom : TotalClockPolynomialDomination c d)
    {N : Nat} (y : Bitstring N) :
    DecidesWithin (machine V) (polyClock d N) y
      (encodedRelationLanguage R N y) := by
  have hexact := combined_decidesAt V c R hV y
  have hat : DecidesAt (machine V) (polyClock d N)
      (totalClock c N) y (encodedRelationLanguage R N y) :=
    (machine V).decidesAt_budget_mono y
      (encodedRelationLanguage R N y) (Nat.le_refl _) (hdom N) hexact
  cases hanswer : encodedRelationLanguage R N y with
  | false =>
      change RejectsWithin (machine V) (polyClock d N) y
      exact ⟨totalClock c N, hdom N, by
        simpa [DecidesAt, RejectsAt, hanswer] using hat⟩
  | true =>
      change AcceptsWithin (machine V) (polyClock d N) y
      exact ⟨totalClock c N, hdom N, by
        simpa [DecidesAt, AcceptsAt, hanswer] using hat⟩

/-- Exact-deadline form at the larger standard clock.  The reverse direction
of the deadline/within equivalence uses terminal absorption to carry the
literal result from witness time `totalClock c N` to deadline
`polyClock d N`. -/
theorem combined_decidesAt_polyClock
    (V : UniformTM) (c d : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    (hdom : TotalClockPolynomialDomination c d)
    {N : Nat} (y : Bitstring N) :
    DecidesAt (machine V) (polyClock d N) (polyClock d N) y
      (encodedRelationLanguage R N y) := by
  exact (decidesAt_budget_iff_decidesWithin
    (machine V) y (encodedRelationLanguage R N y)).2
      (combined_decidesWithin_polyClock V c d R hV hdom y)

theorem combined_verifiesRelation_of_domination
    (V : UniformTM) (c d : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    (hdom : TotalClockPolynomialDomination c d) :
    VerifiesRelation (machine V) d R := by
  intro N y
  exact combined_decidesWithin_polyClock V c d R hV hdom y

/-- Standard-clock packaging of the sharp combined result.  Its proof still
depends on every preceding constructor, prefix-simulation, and budget theorem
in the imported candidate modules. -/
theorem combined_verifiesRelation
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R) :
    VerifiesRelation (combinedMachine V) (c + 3) R :=
  combined_verifiesRelation_of_domination V c (c + 3) R hV
    (totalClockPolynomialDomination_add_three c)

end FixedParserVerifier
end Pnp3.Complexity.Uniform.V1
