import Complexity.Uniform.V1.CombinedMachine

/-!
# P2-3cB2 combined-machine typed surface

Every declaration below fixes an executable type or restates the complete
proposition of a load-bearing source theorem.  In particular, the handoff and
rejection wrappers retain equality of the entire `Config`; they are not
state-only or existential weakenings.
-/

namespace Pnp3.Tests.UniformV1CombinedMachineSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedParserVerifier

/-! ## Typed definition pins -/

#check (parserWorkCount : Nat)
#check (combinedStateCount : UniformTM → Nat)
#check (combinedReject : ∀ V : UniformTM, Fin (combinedStateCount V))
#check (pStart : Fin parserWorkCount)
#check (pDataF : Fin parserWorkCount)
#check (pTagF : Fin parserWorkCount)
#check (pWitnessF : Fin parserWorkCount)
#check (pWitnessT : Fin parserWorkCount)
#check (pBackAcceptF : Fin parserWorkCount)
#check (pBackAcceptT : Fin parserWorkCount)
#check (pBackRejectF : Fin parserWorkCount)
#check (routeParserState : ∀ V : UniformTM,
  Fin FixedPairParser.machine.stateCount → Fin (combinedStateCount V))
#check (parserRoutedRawStep : ∀ V : UniformTM,
  Fin parserWorkCount → Option Bool →
    Fin (combinedStateCount V) × Option Bool × Move)

/-! ## Constructor, injections, and exact resources -/

def check_machine : UniformTM → UniformTM := machine

def check_combinedRawStep (V : UniformTM) :
    Fin (combinedStateCount V) → Option Bool →
      Fin (combinedStateCount V) × Option Bool × Move :=
  combinedRawStep V

def check_inParser (V : UniformTM) :
    Fin parserWorkCount → Fin (combinedStateCount V) :=
  inParser V

def check_inVerifier (V : UniformTM) :
    Fin V.stateCount → Fin (combinedStateCount V) :=
  inVerifier V

theorem check_parserWorkCount : parserWorkCount = 8 :=
  parserWorkCount_eq

theorem check_inParser_injective (V : UniformTM) :
    Function.Injective (inParser V) :=
  inParser_injective V

theorem check_inVerifier_injective (V : UniformTM) :
    Function.Injective (inVerifier V) :=
  inVerifier_injective V

theorem check_inParser_ne_inVerifier (V : UniformTM)
    (p : Fin parserWorkCount) (q : Fin V.stateCount) :
    inParser V p ≠ inVerifier V q :=
  inParser_ne_inVerifier V p q

theorem check_machine_stateCount (V : UniformTM) :
    (machine V).stateCount = 8 + V.stateCount :=
  machine_stateCount V

theorem check_machine_start (V : UniformTM) :
    (machine V).start = inParser V pStart :=
  machine_start V

theorem check_machine_accept (V : UniformTM) :
    (machine V).accept = inVerifier V V.accept :=
  machine_accept V

theorem check_machine_reject (V : UniformTM) :
    (machine V).reject = inVerifier V V.reject :=
  machine_reject V

theorem check_state_card (V : UniformTM) :
    Fintype.card (Fin (machine V).stateCount) = 8 + V.stateCount :=
  state_card V

theorem check_transitionTable_card (V : UniformTM) :
    Fintype.card (Fin (machine V).stateCount × Option Bool) =
      3 * (8 + V.stateCount) :=
  transitionTable_card V

/-! ## Installed table and exact branch equations -/

theorem check_machine_rawStep (V : UniformTM)
    (q : Fin (combinedStateCount V)) (scanned : Option Bool) :
    (machine V).rawStep q scanned = combinedRawStep V q scanned :=
  machine_rawStep V q scanned

theorem check_routeParserState_accept (V : UniformTM) :
    routeParserState V FixedPairParser.machine.accept =
      inVerifier V V.start :=
  routeParserState_accept V

theorem check_routeParserState_reject (V : UniformTM) :
    routeParserState V FixedPairParser.machine.reject =
      combinedReject V :=
  routeParserState_reject V

theorem check_combinedRawStep_inParser (V : UniformTM)
    (q : Fin parserWorkCount) (scanned : Option Bool) :
    combinedRawStep V (inParser V q) scanned =
      parserRoutedRawStep V q scanned :=
  combinedRawStep_inParser V q scanned

theorem check_step_inParser (V : UniformTM)
    (q : Fin parserWorkCount) (scanned : Option Bool) :
    (machine V).step (inParser V q) scanned =
      parserRoutedRawStep V q scanned :=
  step_inParser V q scanned

theorem check_parser_row_start (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pStart scanned =
      match scanned with
      | none => (combinedReject V, none, .stay)
      | some false => (inParser V pDataF, none, .right)
      | some true => (inParser V pWitnessT, none, .right) :=
  parser_row_start V scanned

theorem check_parser_row_dataF (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pDataF scanned =
      match scanned with
      | none => (inParser V pBackRejectF, none, .left)
      | some b => (inParser V pTagF, some b, .right) :=
  parser_row_dataF V scanned

theorem check_parser_row_tagF (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pTagF scanned =
      match scanned with
      | none => (inParser V pBackRejectF, none, .left)
      | some false => (inParser V pDataF, some false, .right)
      | some true => (inParser V pWitnessF, some true, .right) :=
  parser_row_tagF V scanned

theorem check_parser_row_witnessF (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pWitnessF scanned =
      match scanned with
      | none => (inParser V pBackAcceptF, none, .left)
      | some b => (inParser V pWitnessF, some b, .right) :=
  parser_row_witnessF V scanned

theorem check_parser_row_witnessT (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pWitnessT scanned =
      match scanned with
      | none => (inParser V pBackAcceptT, none, .left)
      | some b => (inParser V pWitnessT, some b, .right) :=
  parser_row_witnessT V scanned

theorem check_parser_row_backAcceptF (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pBackAcceptF scanned =
      match scanned with
      | none => (inVerifier V V.start, some false, .stay)
      | some b => (inParser V pBackAcceptF, some b, .left) :=
  parser_row_backAcceptF V scanned

theorem check_parser_row_backAcceptT (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pBackAcceptT scanned =
      match scanned with
      | none => (inVerifier V V.start, some true, .stay)
      | some b => (inParser V pBackAcceptT, some b, .left) :=
  parser_row_backAcceptT V scanned

theorem check_parser_row_backRejectF (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pBackRejectF scanned =
      match scanned with
      | none => (combinedReject V, some false, .stay)
      | some b => (inParser V pBackRejectF, some b, .left) :=
  parser_row_backRejectF V scanned

theorem check_combinedRawStep_inVerifier (V : UniformTM)
    (q : Fin V.stateCount) (scanned : Option Bool) :
    combinedRawStep V (inVerifier V q) scanned =
      let action := V.step q scanned
      (inVerifier V action.1, action.2.1, action.2.2) :=
  combinedRawStep_inVerifier V q scanned

theorem check_step_inVerifier (V : UniformTM)
    (q : Fin V.stateCount) (scanned : Option Bool) :
    (machine V).step (inVerifier V q) scanned =
      let action := V.step q scanned
      (inVerifier V action.1, action.2.1, action.2.2) :=
  step_inVerifier V q scanned

/-! ## Same-index verifier execution -/

def check_embedConfig (V : UniformTM) {N budget : Nat} :
    Config V.stateCount N budget →
      Config (machine V).stateCount N budget :=
  embedConfig V

theorem check_stepConfig_embed (V : UniformTM) {N budget : Nat}
    (c : Config V.stateCount N budget) :
    (machine V).stepConfig (embedConfig V c) =
      embedConfig V (V.stepConfig c) :=
  stepConfig_embed V c

theorem check_run_embed (V : UniformTM) {N budget : Nat}
    (steps : Nat) (c : Config V.stateCount N budget) :
    (machine V).run steps (embedConfig V c) =
      embedConfig V (V.run steps c) :=
  run_embed V steps c

theorem check_embed_initialConfig (V : UniformTM) {N budget : Nat}
    (y : Bitstring N) :
    embedConfig V (initialConfig V budget y) =
      { initialConfig (machine V) budget y with
        state := inVerifier V V.start } :=
  embed_initialConfig V y

/-! ## Bounded parser prefix and exact full-configuration handoff -/

def check_translateParserConfig (V : UniformTM) {N budget : Nat} :
    Config FixedPairParser.machine.stateCount N budget →
      Config (machine V).stateCount N budget :=
  translateParserConfig V

theorem check_fixedParser_nonwork_is_terminal
    (q : Fin FixedPairParser.machine.stateCount)
    (hwork : ¬ q.val < parserWorkCount) :
    q = FixedPairParser.machine.accept ∨
      q = FixedPairParser.machine.reject :=
  fixedParser_nonwork_is_terminal q hwork

theorem check_stepConfig_translateParser_of_work (V : UniformTM)
    {N budget : Nat}
    (c : Config FixedPairParser.machine.stateCount N budget)
    (hwork : c.state.val < parserWorkCount) :
    (machine V).stepConfig (translateParserConfig V c) =
      translateParserConfig V (FixedPairParser.machine.stepConfig c) :=
  stepConfig_translateParser_of_work V c hwork

theorem check_run_parser_prefix (V : UniformTM) {N budget : Nat}
    (y : Bitstring N) (hbudget : FixedPairParser.clock N ≤ budget)
    (steps : Nat) (hsteps : steps ≤ FixedPairParser.clock N) :
    (machine V).run steps (initialConfig (machine V) budget y) =
      translateParserConfig V
        (FixedPairParser.machine.run steps
          (initialConfig FixedPairParser.machine budget y)) :=
  run_parser_prefix V y hbudget steps hsteps

theorem check_parser_handoff_of_decodePair_some (V : UniformTM)
    {N budget : Nat} (y : Bitstring N)
    (hbudget : FixedPairParser.clock N ≤ budget)
    (p : DecodedPair) (hdecode : decodePair y = some p) :
    (machine V).run (FixedPairParser.clock N)
        (initialConfig (machine V) budget y) =
      embedConfig V (initialConfig V budget y) :=
  parser_handoff_of_decodePair_some V y hbudget p hdecode

theorem check_parser_reject_of_decodePair_none (V : UniformTM)
    {N budget : Nat} (y : Bitstring N)
    (hbudget : FixedPairParser.clock N ≤ budget)
    (hdecode : decodePair y = none) :
    (machine V).run (FixedPairParser.clock N)
        (initialConfig (machine V) budget y) =
      { initialConfig (machine V) budget y with
        state := (machine V).reject } :=
  parser_reject_of_decodePair_none V y hbudget hdecode

theorem check_parser_reject_empty (V : UniformTM) (budget : Nat)
    (y : Bitstring 0) (hbudget : FixedPairParser.clock 0 ≤ budget) :
    (machine V).run (FixedPairParser.clock 0)
        (initialConfig (machine V) budget y) =
      { initialConfig (machine V) budget y with
        state := (machine V).reject } :=
  parser_reject_empty V budget y hbudget

def check_emptyRawWord : Bitstring 0 := emptyRawWord

theorem check_parser_reject_empty_exactBudget (V : UniformTM) :
    (machine V).run (FixedPairParser.clock 0)
        (initialConfig (machine V) (FixedPairParser.clock 0) emptyRawWord) =
      { initialConfig (machine V) (FixedPairParser.clock 0) emptyRawWord with
        state := (machine V).reject } :=
  parser_reject_empty_exactBudget V

end Pnp3.Tests.UniformV1CombinedMachineSurfaceTests
