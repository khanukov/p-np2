import Complexity.Uniform.V1.FixedPairParserCorrectness

/-!
# P2-3b exact fixed-pair-parser theorem surface

Every theorem exported by the two P2-3b production modules has exactly one
namespaced full-proposition wrapper below, and every public definition has an
explicit type pin.  Install this surface before the production modules for the
required vertical RED test, then rerun it after production is added.
-/

namespace Pnp3.Tests.UniformV1FixedPairParserCorrectness

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairParser

/-! ## Typed definition pins -/

#check (machine : UniformTM)
#check (clock : Nat → Nat)
#check (GrammarPhase : Type)
#check (grammarStep : GrammarPhase → Bool → GrammarPhase)
#check (grammarRun : GrammarPhase → List Bool → GrammarPhase)
#check (syntaxOK : List Bool → Bool)
#check (MergedPairGrammar : List Bool → Prop)
#check (indexedBit : ∀ {N : Nat}, Bitstring N → Nat → Bool)
#check (indexedPrefix : ∀ {N : Nat}, Bitstring N → Nat → List Bool)
#check (phaseAt : ∀ {N : Nat}, Bitstring N → Nat → GrammarPhase)
#check (exactInitial : ∀ {N : Nat}, Bitstring N → Config parserStateCount N (clock N))
#check (erasedZeroTape : ∀ {N : Nat}, Bitstring N → Fin (tapeLength N (clock N)) → Option Bool)
#check (forwardState : Bool → GrammarPhase → Fin parserStateCount)
#check (backState : Bool → GrammarPhase → Fin parserStateCount)
#check (verdictState : GrammarPhase → Fin parserStateCount)
#check (ForwardAt : ∀ {N : Nat}, Bitstring N → Nat → Config parserStateCount N (clock N) → Prop)
#check (BackAt : ∀ {N : Nat}, Bitstring N → Nat → Config parserStateCount N (clock N) → Prop)
#check (expectedFinalState : ∀ {N : Nat}, Bitstring N → Fin parserStateCount)

/-! ## Full-proposition theorem wrappers -/

theorem check_grammarRun_append : ∀ (q : GrammarPhase) (left right : List Bool), grammarRun q (left ++ right) = grammarRun (grammarRun q left) right :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.grammarRun_append

theorem check_syntaxOK_iff_grammar : ∀ (l : List Bool), syntaxOK l = true ↔ MergedPairGrammar l :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.syntaxOK_iff_grammar

theorem check_mergedPairGrammar_iff_encodePairList : ∀ (l : List Bool), MergedPairGrammar l ↔ ∃ xs ws, l = encodePairList xs ws :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.mergedPairGrammar_iff_encodePairList

theorem check_syntaxOK_ofFn_eq_decodePair_isSome : ∀ {N : Nat} (y : Bitstring N), syntaxOK (List.ofFn y) = (decodePair y).isSome :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.syntaxOK_ofFn_eq_decodePair_isSome

theorem check_syntaxOK_ofFn_iff_decodePair_some : ∀ {N : Nat} (y : Bitstring N), syntaxOK (List.ofFn y) = true ↔ ∃ p : DecodedPair, decodePair y = some p :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.syntaxOK_ofFn_iff_decodePair_some

theorem check_mergedPairGrammar_ofFn_iff_decodePair_some : ∀ {N : Nat} (y : Bitstring N), MergedPairGrammar (List.ofFn y) ↔ ∃ p : DecodedPair, decodePair y = some p :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.mergedPairGrammar_ofFn_iff_decodePair_some

theorem check_restore_erasedZeroTape : ∀ {N : Nat} (y : Bitstring N) (_hN : 0 < N), (fun i : Fin (tapeLength N (clock N)) => if i.val = 0 then some (indexedBit y 0) else erasedZeroTape y i) = (exactInitial y).tape :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.restore_erasedZeroTape

theorem check_run_forward : ∀ {N : Nat} (y : Bitstring N) (r : Nat), r + 1 ≤ N → ForwardAt y (r + 1) (machine.run (r + 1) (exactInitial y)) :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.run_forward

theorem check_run_back : ∀ {N : Nat} (y : Bitstring N) (_hN : 0 < N) (j : Nat), j < N → BackAt y j (machine.run (N + 1 + j) (exactInitial y)) :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.run_back

theorem check_rewind_reaches_zero_marker : ∀ {N : Nat} (y : Bitstring N) (_hN : 0 < N), let c := machine.run (2 * N) (exactInitial y); BackAt y (N - 1) c ∧ c.head.val = 0 ∧ c.tape c.head = none :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.rewind_reaches_zero_marker

theorem check_verdictState_phaseAt_eq_expected : ∀ {N : Nat} (y : Bitstring N), verdictState (phaseAt y N) = expectedFinalState y :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.verdictState_phaseAt_eq_expected

theorem check_run_empty_at_clock : ∀ (y : Bitstring 0), let c₀ := initialConfig machine (clock 0) y; let cF := machine.run (clock 0) c₀; cF.state = qReject ∧ cF.head.val = 0 ∧ cF.tape = c₀.tape :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.run_empty_at_clock

theorem check_run_initialConfig_fields : ∀ {N : Nat} (y : Bitstring N), let c₀ := exactInitial y; let cF := machine.run (clock N) c₀; cF.state = expectedFinalState y ∧ cF.head.val = 0 ∧ cF.tape = c₀.tape :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.run_initialConfig_fields

theorem check_run_initialConfig_exact : ∀ {N : Nat} (y : Bitstring N), machine.run (clock N) (initialConfig machine (clock N) y) = { initialConfig machine (clock N) y with state := expectedFinalState y } :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.run_initialConfig_exact

theorem check_noEarlyTerminal_initialConfig : ∀ {N : Nat} (y : Bitstring N) (steps : Nat) (_hsteps : steps < clock N), let c := machine.run steps (initialConfig machine (clock N) y); c.state ≠ machine.accept ∧ c.state ≠ machine.reject :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.noEarlyTerminal_initialConfig

theorem check_no_public_terminal_before_clock : ∀ {N : Nat} (y : Bitstring N) (steps : Nat) (_hsteps : steps < clock N), ¬ AcceptsAt machine (clock N) steps y ∧ ¬ RejectsAt machine (clock N) steps y :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.no_public_terminal_before_clock

theorem check_head_zero_at_clock : ∀ {N : Nat} (y : Bitstring N), (machine.run (clock N) (initialConfig machine (clock N) y)).head.val = 0 :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.head_zero_at_clock

theorem check_tape_restored_at_clock : ∀ {N : Nat} (y : Bitstring N), (machine.run (clock N) (initialConfig machine (clock N) y)).tape = (initialConfig machine (clock N) y).tape :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.tape_restored_at_clock

theorem check_final_state_at_clock : ∀ {N : Nat} (y : Bitstring N), (machine.run (clock N) (initialConfig machine (clock N) y)).state = expectedFinalState y :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.final_state_at_clock

theorem check_final_state_at_clock_syntax : ∀ {N : Nat} (y : Bitstring N), (machine.run (clock N) (initialConfig machine (clock N) y)).state = if syntaxOK (List.ofFn y) then qAccept else qReject :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.final_state_at_clock_syntax

theorem check_acceptsAt_clock_iff_decodePair_some : ∀ {N : Nat} (y : Bitstring N), AcceptsAt machine (clock N) (clock N) y ↔ ∃ p : DecodedPair, decodePair y = some p :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.acceptsAt_clock_iff_decodePair_some

theorem check_rejectsAt_clock_iff_decodePair_none : ∀ {N : Nat} (y : Bitstring N), RejectsAt machine (clock N) (clock N) y ↔ decodePair y = none :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.rejectsAt_clock_iff_decodePair_none

theorem check_decidesAt_clock : ∀ {N : Nat} (y : Bitstring N), DecidesAt machine (clock N) (clock N) y (decodePair y).isSome :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.decidesAt_clock

theorem check_decidesAt_clock_syntax : ∀ {N : Nat} (y : Bitstring N), DecidesAt machine (clock N) (clock N) y (syntaxOK (List.ofFn y)) :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.decidesAt_clock_syntax

theorem check_decidesWithin_clock : ∀ {N : Nat} (y : Bitstring N), DecidesWithin machine (clock N) y (decodePair y).isSome :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.decidesWithin_clock

theorem check_exact_execution_initialConfig : ∀ {N : Nat} (y : Bitstring N), let c₀ := initialConfig machine (clock N) y; let cF := machine.run (clock N) c₀; (cF = { c₀ with state := expectedFinalState y }) ∧ (∀ steps, steps < clock N → let c := machine.run steps c₀; c.state ≠ machine.accept ∧ c.state ≠ machine.reject) ∧ cF.head.val = 0 ∧ cF.tape = c₀.tape ∧ ((cF.state = machine.accept) ↔ ∃ p : DecodedPair, decodePair y = some p) ∧ ((cF.state = machine.reject) ↔ decodePair y = none) ∧ (AcceptsAt machine (clock N) (clock N) y ↔ ∃ p : DecodedPair, decodePair y = some p) ∧ (RejectsAt machine (clock N) (clock N) y ↔ decodePair y = none) ∧ DecidesAt machine (clock N) (clock N) y (decodePair y).isSome ∧ DecidesWithin machine (clock N) y (decodePair y).isSome :=
  @Pnp3.Complexity.Uniform.V1.FixedPairParser.exact_execution_initialConfig

end Pnp3.Tests.UniformV1FixedPairParserCorrectness
