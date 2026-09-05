import Complexity.Uniform.V1.CombinedCorrectness

/-!
Surface checks for P2-3cB3.  Every public theorem in the production module
is repeated below with the same proposition, rather than merely mentioned by
`#check`.  The three public definitions are separately pinned at their exact
types.
-/

namespace Pnp3.Tests.UniformV1CombinedCorrectnessSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedParserVerifier

/-! Exact type pins for all public definitions in the B3 module. -/

#check (combinedMachine : UniformTM → UniformTM)
#check (totalClock : Nat → Nat → Nat)
#check (TotalClockPolynomialDomination : Nat → Nat → Prop)

theorem check_totalClock_eq (c N : Nat) :
    totalClock c N =
      FixedPairParser.clock N + polyClock c N :=
  totalClock_eq c N

theorem check_totalClock_closedForm (c N : Nat) :
    totalClock c N = (2 * N + 1) + (N ^ c + c) :=
  totalClock_closedForm c N

theorem check_parserClock_le_totalClock (c N : Nat) :
    FixedPairParser.clock N ≤ totalClock c N :=
  parserClock_le_totalClock c N

theorem check_verifierClock_le_totalClock (c N : Nat) :
    polyClock c N ≤ totalClock c N :=
  verifierClock_le_totalClock c N

theorem check_total_tapeLength (c N : Nat) :
    tapeLength N (totalClock c N) =
      3 * N + polyClock c N + 2 :=
  total_tapeLength c N

theorem check_verifier_decidesAt_ambient
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    {N : Nat} (y : Bitstring N) :
    DecidesAt V (totalClock c N) (polyClock c N) y
      (encodedRelationLanguage R N y) :=
  verifier_decidesAt_ambient V c R hV y

theorem check_run_total_split (V : UniformTM) (c : Nat)
    {N : Nat} (y : Bitstring N) :
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
      (machine V).run (polyClock c N)
        ((machine V).run (FixedPairParser.clock N)
          (initialConfig (machine V) (totalClock c N) y)) :=
  run_total_split V c y

theorem check_run_total_of_decodePair_some
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (p : DecodedPair) (hdecode : decodePair y = some p) :
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
      embedConfig V
        (V.run (polyClock c N)
          (initialConfig V (totalClock c N) y)) :=
  run_total_of_decodePair_some V c y p hdecode

theorem check_run_total_of_decodePair_none
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (hdecode : decodePair y = none) :
    (machine V).run (totalClock c N)
        (initialConfig (machine V) (totalClock c N) y) =
      { initialConfig (machine V) (totalClock c N) y with
        state := (machine V).reject } :=
  run_total_of_decodePair_none V c y hdecode

theorem check_run_total_empty
    (V : UniformTM) (c : Nat) (y : Bitstring 0) :
    (machine V).run (totalClock c 0)
        (initialConfig (machine V) (totalClock c 0) y) =
      { initialConfig (machine V) (totalClock c 0) y with
        state := (machine V).reject } :=
  run_total_empty V c y

theorem check_malformed_rejectsAt_parserClock
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (hdecode : decodePair y = none) :
    RejectsAt (machine V) (totalClock c N)
      (FixedPairParser.clock N) y :=
  malformed_rejectsAt_parserClock V c y hdecode

theorem check_malformed_rejectsAt_total
    (V : UniformTM) (c : Nat) {N : Nat} (y : Bitstring N)
    (hdecode : decodePair y = none) :
    RejectsAt (machine V) (totalClock c N) (totalClock c N) y :=
  malformed_rejectsAt_total V c y hdecode

theorem check_combined_decidesAt
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    {N : Nat} (y : Bitstring N) :
    DecidesAt (machine V) (totalClock c N) (totalClock c N) y
      (encodedRelationLanguage R N y) :=
  combined_decidesAt V c R hV y

theorem check_combined_decidesWithin
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    {N : Nat} (y : Bitstring N) :
    DecidesWithin (machine V) (totalClock c N) y
      (encodedRelationLanguage R N y) :=
  combined_decidesWithin V c R hV y

theorem check_totalClock_le_polyClock_add_three (c N : Nat) :
    totalClock c N ≤ polyClock (c + 3) N :=
  totalClock_le_polyClock_add_three c N

theorem check_totalClockPolynomialDomination_add_three (c : Nat) :
    TotalClockPolynomialDomination c (c + 3) :=
  totalClockPolynomialDomination_add_three c

theorem check_totalClock_not_le_polyClock_add_two_at_one (c : Nat) :
    ¬ totalClock c 1 ≤ polyClock (c + 2) 1 :=
  totalClock_not_le_polyClock_add_two_at_one c

theorem check_totalClockPolynomialDomination_add_two_fails (c : Nat) :
    ¬ TotalClockPolynomialDomination c (c + 2) :=
  totalClockPolynomialDomination_add_two_fails c

theorem check_combined_decidesWithin_polyClock
    (V : UniformTM) (c d : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    (hdom : TotalClockPolynomialDomination c d)
    {N : Nat} (y : Bitstring N) :
    DecidesWithin (machine V) (polyClock d N) y
      (encodedRelationLanguage R N y) :=
  combined_decidesWithin_polyClock V c d R hV hdom y

theorem check_combined_decidesAt_polyClock
    (V : UniformTM) (c d : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    (hdom : TotalClockPolynomialDomination c d)
    {N : Nat} (y : Bitstring N) :
    DecidesAt (machine V) (polyClock d N) (polyClock d N) y
      (encodedRelationLanguage R N y) :=
  combined_decidesAt_polyClock V c d R hV hdom y

theorem check_combined_verifiesRelation_of_domination
    (V : UniformTM) (c d : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R)
    (hdom : TotalClockPolynomialDomination c d) :
    VerifiesRelation (machine V) d R :=
  combined_verifiesRelation_of_domination V c d R hV hdom

theorem check_combined_verifiesRelation
    (V : UniformTM) (c : Nat) (R : WitnessRelation)
    (hV : VerifiesRelation V c R) :
    VerifiesRelation (combinedMachine V) (c + 3) R :=
  combined_verifiesRelation V c R hV

end Pnp3.Tests.UniformV1CombinedCorrectnessSurfaceTests
