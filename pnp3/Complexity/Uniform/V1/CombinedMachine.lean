import Mathlib.Tactic
import Complexity.Uniform.V1.BudgetTransport

/-!
# P2-3cB2 routed fixed-parser / verifier machine

This B2 slice uses the merged ambient-parser and generic budget-transport APIs.
The finite control contains exactly the eight nonterminal controls of the
fixed pair parser followed by every control of `V`.  The old parser verdict
controls are not controls of this machine.  A fixed-parser edge whose target
is parser accept is routed to `V.start`; every other non-work target is routed
to `V.reject`.

Calling `FixedPairParser.machine.step` below constructs a row of a finite
transition table.  It is not a run, a configuration restart, or a source of
input-dependent data.
-/

namespace Pnp3.Complexity.Uniform.V1
namespace FixedParserVerifier

open PairEncoding

abbrev parserWorkCount : Nat := 8

@[simp] theorem parserWorkCount_eq : parserWorkCount = 8 := rfl

def combinedStateCount (V : UniformTM) : Nat :=
  parserWorkCount + V.stateCount

def inParser (V : UniformTM) (q : Fin parserWorkCount) :
    Fin (combinedStateCount V) :=
  ⟨q.val, by
    simp only [combinedStateCount]
    omega⟩

def inVerifier (V : UniformTM) (q : Fin V.stateCount) :
    Fin (combinedStateCount V) :=
  ⟨parserWorkCount + q.val, by
    simp only [combinedStateCount]
    omega⟩

theorem inParser_injective (V : UniformTM) :
    Function.Injective (inParser V) := by
  intro a b h
  apply Fin.ext
  exact congrArg
    (fun q : Fin (combinedStateCount V) => q.val) h

theorem inVerifier_injective (V : UniformTM) :
    Function.Injective (inVerifier V) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [inVerifier] at hv
  omega

theorem inParser_ne_inVerifier (V : UniformTM)
    (p : Fin parserWorkCount) (q : Fin V.stateCount) :
    inParser V p ≠ inVerifier V q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [inParser, inVerifier] at hv
  omega

private def verifierOfRight (V : UniformTM) (q : Fin (combinedStateCount V))
    (hq : parserWorkCount ≤ q.val) : Fin V.stateCount :=
  ⟨q.val - parserWorkCount, by
    have hlt := q.isLt
    simp only [combinedStateCount] at hlt
    omega⟩

@[simp] private theorem verifierOfRight_inVerifier (V : UniformTM)
    (q : Fin V.stateCount) :
    verifierOfRight V (inVerifier V q) (by simp [inVerifier]) = q := by
  apply Fin.ext
  simp [verifierOfRight, inVerifier]

def pStart : Fin parserWorkCount := ⟨0, by decide⟩
def pDataF : Fin parserWorkCount := ⟨1, by decide⟩
def pTagF : Fin parserWorkCount := ⟨2, by decide⟩
def pWitnessF : Fin parserWorkCount := ⟨3, by decide⟩
def pWitnessT : Fin parserWorkCount := ⟨4, by decide⟩
def pBackAcceptF : Fin parserWorkCount := ⟨5, by decide⟩
def pBackAcceptT : Fin parserWorkCount := ⟨6, by decide⟩
def pBackRejectF : Fin parserWorkCount := ⟨7, by decide⟩

/-! `inFixedParser` is used only while constructing the eight fixed rows. -/

private def inFixedParser (q : Fin parserWorkCount) :
    Fin FixedPairParser.machine.stateCount :=
  ⟨q.val, by
    have hq : q.val < 8 := q.isLt
    change q.val < 10
    omega⟩

@[simp] private theorem inFixedParser_val (q : Fin parserWorkCount) :
    (inFixedParser q).val = q.val := rfl

private theorem fixedParser_accept_val :
    FixedPairParser.machine.accept.val = 8 := rfl

private theorem fixedParser_reject_val :
    FixedPairParser.machine.reject.val = 9 := rfl

private theorem fixedParser_start_val :
    FixedPairParser.machine.start.val = 0 := rfl

private def combinedAccept (V : UniformTM) : Fin (combinedStateCount V) :=
  inVerifier V V.accept

def combinedReject (V : UniformTM) : Fin (combinedStateCount V) :=
  inVerifier V V.reject

/-!
Map a target of a fixed-parser work row into combined control.  The first
branch retains work controls.  Parser accept becomes verifier start in the
same transition.  The only other reachable non-work target is parser reject;
the conservative final branch maps it to literal combined reject.
-/
def routeParserState (V : UniformTM)
    (q : Fin FixedPairParser.machine.stateCount) :
    Fin (combinedStateCount V) :=
  if hwork : q.val < parserWorkCount then
    inParser V ⟨q.val, hwork⟩
  else if q = FixedPairParser.machine.accept then
    inVerifier V V.start
  else
    combinedReject V

private theorem routeParserState_of_work (V : UniformTM)
    (q : Fin FixedPairParser.machine.stateCount)
    (hwork : q.val < parserWorkCount) :
    routeParserState V q = inParser V ⟨q.val, hwork⟩ := by
  simp [routeParserState, hwork]

@[simp] private theorem routeParserState_inFixedParser (V : UniformTM)
    (q : Fin parserWorkCount) :
    routeParserState V (inFixedParser q) = inParser V q := by
  have hwork : (inFixedParser q).val < parserWorkCount := q.isLt
  calc
    routeParserState V (inFixedParser q) =
        inParser V
          (⟨(inFixedParser q).val, hwork⟩ : Fin parserWorkCount) :=
      routeParserState_of_work V (inFixedParser q) hwork
    _ = inParser V q := by
      apply congrArg (inParser V)
      apply Fin.ext
      rfl

@[simp] theorem routeParserState_accept (V : UniformTM) :
    routeParserState V FixedPairParser.machine.accept =
      inVerifier V V.start := by
  simp [routeParserState, fixedParser_accept_val]

@[simp] theorem routeParserState_reject (V : UniformTM) :
    routeParserState V FixedPairParser.machine.reject =
      combinedReject V := by
  have hne : FixedPairParser.machine.reject ≠
      FixedPairParser.machine.accept :=
    FixedPairParser.machine.accept_ne_reject.symm
  simp [routeParserState, fixedParser_reject_val, hne]

def parserRoutedRawStep (V : UniformTM)
    (q : Fin parserWorkCount) (scanned : Option Bool) :
    Fin (combinedStateCount V) × Option Bool × Move :=
  let action := FixedPairParser.machine.step (inFixedParser q) scanned
  (routeParserState V action.1, action.2.1, action.2.2)

def combinedRawStep (V : UniformTM)
    (q : Fin (combinedStateCount V)) (scanned : Option Bool) :
    Fin (combinedStateCount V) × Option Bool × Move :=
  if hp : q.val < parserWorkCount then
    parserRoutedRawStep V ⟨q.val, hp⟩ scanned
  else
    let vq := verifierOfRight V q (Nat.le_of_not_gt hp)
    let action := V.step vq scanned
    (inVerifier V action.1, action.2.1, action.2.2)

def machine (V : UniformTM) : UniformTM where
  stateCount := combinedStateCount V
  start := inParser V pStart
  accept := combinedAccept V
  reject := combinedReject V
  accept_ne_reject := by
    intro h
    exact V.accept_ne_reject (inVerifier_injective V h)
  rawStep := combinedRawStep V

@[simp] theorem machine_stateCount (V : UniformTM) :
    (machine V).stateCount = 8 + V.stateCount := rfl

@[simp] theorem machine_start (V : UniformTM) :
    (machine V).start = inParser V pStart := rfl

@[simp] theorem machine_accept (V : UniformTM) :
    (machine V).accept = inVerifier V V.accept := rfl

@[simp] theorem machine_reject (V : UniformTM) :
    (machine V).reject = inVerifier V V.reject := rfl

/-- The displayed combined raw table is exactly the table installed in the
combined machine.  Public terminal absorption remains the wrapper supplied by
`UniformTM.step`; it is pinned separately below. -/
@[simp] theorem machine_rawStep (V : UniformTM)
    (q : Fin (combinedStateCount V)) (scanned : Option Bool) :
    (machine V).rawStep q scanned = combinedRawStep V q scanned := rfl

/-- Exact cardinality of the combined finite-control type. -/
theorem state_card (V : UniformTM) :
    Fintype.card (Fin (machine V).stateCount) = 8 + V.stateCount := by
  simp [machine, combinedStateCount]

/-- Exact number of state/symbol entries in the combined raw table. -/
theorem transitionTable_card (V : UniformTM) :
    Fintype.card (Fin (machine V).stateCount × Option Bool) =
      3 * (8 + V.stateCount) := by
  simp [machine, combinedStateCount]
  omega

private theorem parser_not_terminal (V : UniformTM) (p : Fin parserWorkCount) :
    inParser V p ≠ (machine V).accept ∧
      inParser V p ≠ (machine V).reject := by
  exact ⟨inParser_ne_inVerifier V p V.accept,
    inParser_ne_inVerifier V p V.reject⟩

theorem combinedRawStep_inParser (V : UniformTM)
    (q : Fin parserWorkCount) (scanned : Option Bool) :
    combinedRawStep V (inParser V q) scanned =
      parserRoutedRawStep V q scanned := by
  have hp : (inParser V q).val < parserWorkCount := q.isLt
  calc
    combinedRawStep V (inParser V q) scanned =
        parserRoutedRawStep V
          (⟨(inParser V q).val, hp⟩ : Fin parserWorkCount) scanned := by
      simp only [combinedRawStep, dif_pos hp]
    _ = parserRoutedRawStep V q scanned := by
      apply congrArg (fun p => parserRoutedRawStep V p scanned)
      apply Fin.ext
      rfl

theorem step_inParser (V : UniformTM)
    (q : Fin parserWorkCount) (scanned : Option Bool) :
    (machine V).step (inParser V q) scanned =
      parserRoutedRawStep V q scanned := by
  have ha := (parser_not_terminal V q).1
  have hr := (parser_not_terminal V q).2
  unfold UniformTM.step
  rw [if_neg ha, if_neg hr]
  change combinedRawStep V (inParser V q) scanned = _
  exact combinedRawStep_inParser V q scanned

/-!
These eight normalization theorems pin the intended fixed-parser rows.  Thus
a change to the upstream numeric layout or row semantics makes this module
fail rather than silently changing the combined parser.
-/

theorem parser_row_start (V : UniformTM) (scanned : Option Bool) :
    parserRoutedRawStep V pStart scanned =
      match scanned with
      | none => (combinedReject V, none, .stay)
      | some false => (inParser V pDataF, none, .right)
      | some true => (inParser V pWitnessT, none, .right) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

theorem parser_row_dataF (V : UniformTM) (scanned : Option Bool) :
    parserRoutedRawStep V pDataF scanned =
      match scanned with
      | none => (inParser V pBackRejectF, none, .left)
      | some b => (inParser V pTagF, some b, .right) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

theorem parser_row_tagF (V : UniformTM) (scanned : Option Bool) :
    parserRoutedRawStep V pTagF scanned =
      match scanned with
      | none => (inParser V pBackRejectF, none, .left)
      | some false => (inParser V pDataF, some false, .right)
      | some true => (inParser V pWitnessF, some true, .right) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

theorem parser_row_witnessF (V : UniformTM) (scanned : Option Bool) :
    parserRoutedRawStep V pWitnessF scanned =
      match scanned with
      | none => (inParser V pBackAcceptF, none, .left)
      | some b => (inParser V pWitnessF, some b, .right) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

theorem parser_row_witnessT (V : UniformTM) (scanned : Option Bool) :
    parserRoutedRawStep V pWitnessT scanned =
      match scanned with
      | none => (inParser V pBackAcceptT, none, .left)
      | some b => (inParser V pWitnessT, some b, .right) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

theorem parser_row_backAcceptF (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pBackAcceptF scanned =
      match scanned with
      | none => (inVerifier V V.start, some false, .stay)
      | some b => (inParser V pBackAcceptF, some b, .left) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

theorem parser_row_backAcceptT (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pBackAcceptT scanned =
      match scanned with
      | none => (inVerifier V V.start, some true, .stay)
      | some b => (inParser V pBackAcceptT, some b, .left) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

theorem parser_row_backRejectF (V : UniformTM)
    (scanned : Option Bool) :
    parserRoutedRawStep V pBackRejectF scanned =
      match scanned with
      | none => (combinedReject V, some false, .stay)
      | some b => (inParser V pBackRejectF, some b, .left) := by
  cases scanned with
  | none => rfl
  | some b => cases b <;> rfl

/-! ## Same-budget verifier embedding -/

theorem combinedRawStep_inVerifier (V : UniformTM)
    (q : Fin V.stateCount) (scanned : Option Bool) :
    combinedRawStep V (inVerifier V q) scanned =
      let action := V.step q scanned
      (inVerifier V action.1, action.2.1, action.2.2) := by
  have hp : ¬ (inVerifier V q).val < parserWorkCount := by
    simp [inVerifier]
  simp only [combinedRawStep, dif_neg hp]
  rw [verifierOfRight_inVerifier]

theorem step_inVerifier (V : UniformTM)
    (q : Fin V.stateCount) (scanned : Option Bool) :
    (machine V).step (inVerifier V q) scanned =
      let action := V.step q scanned
      (inVerifier V action.1, action.2.1, action.2.2) := by
  by_cases ha : q = V.accept
  · subst q
    simp [UniformTM.step, machine, combinedAccept]
  · by_cases hr : q = V.reject
    · subst q
      simp [UniformTM.step, machine, combinedReject, ha]
    · have hia : inVerifier V q ≠ (machine V).accept := by
        intro h
        apply ha
        exact inVerifier_injective V h
      have hir : inVerifier V q ≠ (machine V).reject := by
        intro h
        apply hr
        exact inVerifier_injective V h
      simp only [UniformTM.step, hia, hir, if_false]
      rw [show (machine V).rawStep (inVerifier V q) scanned =
          combinedRawStep V (inVerifier V q) scanned by rfl]
      rw [combinedRawStep_inVerifier]
      simp [UniformTM.step, ha, hr]

def embedConfig (V : UniformTM) {N budget : Nat}
    (c : Config V.stateCount N budget) :
    Config (machine V).stateCount N budget where
  state := inVerifier V c.state
  head := c.head
  tape := c.tape

theorem stepConfig_embed (V : UniformTM) {N budget : Nat}
    (c : Config V.stateCount N budget) :
    (machine V).stepConfig (embedConfig V c) =
      embedConfig V (V.stepConfig c) := by
  cases c with
  | mk state head tape =>
      simp only [UniformTM.stepConfig, embedConfig]
      rw [step_inVerifier]

theorem run_embed (V : UniformTM) {N budget : Nat} (steps : Nat)
    (c : Config V.stateCount N budget) :
    (machine V).run steps (embedConfig V c) =
      embedConfig V (V.run steps c) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [UniformTM.run, ih, stepConfig_embed, UniformTM.run]

theorem embed_initialConfig (V : UniformTM) {N budget : Nat}
    (y : Bitstring N) :
    embedConfig V (initialConfig V budget y) =
      { initialConfig (machine V) budget y with
        state := inVerifier V V.start } := by
  rfl

/-! ## Fixed-parser prefix simulation on one ambient configuration type -/

/-- Forward translation used only through the parser deadline.  It is not an
embedding: when `V.start = V.reject`, the two old parser verdicts have the
same image. -/
def translateParserConfig (V : UniformTM) {N budget : Nat}
    (c : Config FixedPairParser.machine.stateCount N budget) :
    Config (machine V).stateCount N budget where
  state := routeParserState V c.state
  head := c.head
  tape := c.tape

private theorem translateParser_initialConfig (V : UniformTM) {N budget : Nat}
    (y : Bitstring N) :
    translateParserConfig V (initialConfig FixedPairParser.machine budget y) =
      initialConfig (machine V) budget y := by
  rfl

private theorem fixedParser_work_of_not_terminal
    (q : Fin FixedPairParser.machine.stateCount)
    (ha : q ≠ FixedPairParser.machine.accept)
    (hr : q ≠ FixedPairParser.machine.reject) :
    q.val < parserWorkCount := by
  have hlt := q.isLt
  change q.val < 10 at hlt
  by_contra hn
  have hge : 8 ≤ q.val := Nat.le_of_not_gt hn
  have hcases : q.val = 8 ∨ q.val = 9 := by omega
  rcases hcases with h8 | h9
  · apply ha
    apply Fin.ext
    exact h8.trans fixedParser_accept_val.symm
  · apply hr
    apply Fin.ext
    exact h9.trans fixedParser_reject_val.symm

theorem fixedParser_nonwork_is_terminal
    (q : Fin FixedPairParser.machine.stateCount)
    (hwork : ¬ q.val < parserWorkCount) :
    q = FixedPairParser.machine.accept ∨
      q = FixedPairParser.machine.reject := by
  by_cases ha : q = FixedPairParser.machine.accept
  · exact Or.inl ha
  · by_cases hr : q = FixedPairParser.machine.reject
    · exact Or.inr hr
    · exact False.elim
        (hwork (fixedParser_work_of_not_terminal q ha hr))

private theorem inFixedParser_of_parser_work
    (q : Fin FixedPairParser.machine.stateCount)
    (hwork : q.val < parserWorkCount) :
    inFixedParser (⟨q.val, hwork⟩ : Fin parserWorkCount) = q := by
  apply Fin.ext
  rfl

theorem stepConfig_translateParser_of_work (V : UniformTM)
    {N budget : Nat}
    (c : Config FixedPairParser.machine.stateCount N budget)
    (hwork : c.state.val < parserWorkCount) :
    (machine V).stepConfig (translateParserConfig V c) =
      translateParserConfig V (FixedPairParser.machine.stepConfig c) := by
  cases c with
  | mk q head tape =>
      have hroute : routeParserState V q =
          inParser V (⟨q.val, hwork⟩ : Fin parserWorkCount) :=
        routeParserState_of_work V q hwork
      have hback :
          inFixedParser (⟨q.val, hwork⟩ : Fin parserWorkCount) = q :=
        inFixedParser_of_parser_work q hwork
      simp only [UniformTM.stepConfig, translateParserConfig]
      rw [hroute, step_inParser]
      simp only [parserRoutedRawStep, hback]

theorem run_parser_prefix (V : UniformTM) {N budget : Nat}
    (y : Bitstring N) (hbudget : FixedPairParser.clock N ≤ budget)
    (steps : Nat) (hsteps : steps ≤ FixedPairParser.clock N) :
    (machine V).run steps (initialConfig (machine V) budget y) =
      translateParserConfig V
        (FixedPairParser.machine.run steps
          (initialConfig FixedPairParser.machine budget y)) := by
  revert hsteps
  induction steps with
  | zero =>
      intro _hsteps
      simpa [UniformTM.run] using (translateParser_initialConfig V y).symm
  | succ steps ih =>
      intro hsteps
      have hprev : steps ≤ FixedPairParser.clock N := by omega
      have hstrict : steps < FixedPairParser.clock N := by omega
      have hno := FixedPairParser.ambient_no_public_terminal_before_clock
        y hbudget steps hstrict
      have ha :
          (FixedPairParser.machine.run steps
            (initialConfig FixedPairParser.machine budget y)).state ≠
              FixedPairParser.machine.accept := by
        simpa only [AcceptsAt] using hno.1
      have hr :
          (FixedPairParser.machine.run steps
            (initialConfig FixedPairParser.machine budget y)).state ≠
              FixedPairParser.machine.reject := by
        simpa only [RejectsAt] using hno.2
      have hwork := fixedParser_work_of_not_terminal
        (FixedPairParser.machine.run steps
          (initialConfig FixedPairParser.machine budget y)).state ha hr
      rw [UniformTM.run, ih hprev]
      exact stepConfig_translateParser_of_work V _ hwork

private theorem translateParser_accept_initial (V : UniformTM) {N budget : Nat}
    (y : Bitstring N) :
    translateParserConfig V
        { initialConfig FixedPairParser.machine budget y with
          state := FixedPairParser.machine.accept } =
      embedConfig V (initialConfig V budget y) := by
  simp [translateParserConfig, embedConfig, initialConfig]

private theorem translateParser_reject_initial (V : UniformTM) {N budget : Nat}
    (y : Bitstring N) :
    translateParserConfig V
        { initialConfig FixedPairParser.machine budget y with
          state := FixedPairParser.machine.reject } =
      { initialConfig (machine V) budget y with
        state := (machine V).reject } := by
  simp [translateParserConfig, initialConfig, combinedReject]

theorem parser_handoff_of_decodePair_some (V : UniformTM)
    {N budget : Nat} (y : Bitstring N)
    (hbudget : FixedPairParser.clock N ≤ budget)
    (p : DecodedPair) (hdecode : decodePair y = some p) :
    (machine V).run (FixedPairParser.clock N)
        (initialConfig (machine V) budget y) =
      embedConfig V (initialConfig V budget y) := by
  calc
    (machine V).run (FixedPairParser.clock N)
        (initialConfig (machine V) budget y) =
        translateParserConfig V
          (FixedPairParser.machine.run (FixedPairParser.clock N)
            (initialConfig FixedPairParser.machine budget y)) :=
      run_parser_prefix V y hbudget (FixedPairParser.clock N)
        (Nat.le_refl _)
    _ = translateParserConfig V
          { initialConfig FixedPairParser.machine budget y with
            state := FixedPairParser.machine.accept } := by
      rw [FixedPairParser.ambient_run_initialConfig_accept
        y hbudget p hdecode]
      rfl
    _ = embedConfig V (initialConfig V budget y) :=
      translateParser_accept_initial V y

theorem parser_reject_of_decodePair_none (V : UniformTM)
    {N budget : Nat} (y : Bitstring N)
    (hbudget : FixedPairParser.clock N ≤ budget)
    (hdecode : decodePair y = none) :
    (machine V).run (FixedPairParser.clock N)
        (initialConfig (machine V) budget y) =
      { initialConfig (machine V) budget y with
        state := (machine V).reject } := by
  calc
    (machine V).run (FixedPairParser.clock N)
        (initialConfig (machine V) budget y) =
        translateParserConfig V
          (FixedPairParser.machine.run (FixedPairParser.clock N)
            (initialConfig FixedPairParser.machine budget y)) :=
      run_parser_prefix V y hbudget (FixedPairParser.clock N)
        (Nat.le_refl _)
    _ = translateParserConfig V
          { initialConfig FixedPairParser.machine budget y with
            state := FixedPairParser.machine.reject } := by
      rw [FixedPairParser.ambient_run_initialConfig_reject
        y hbudget hdecode]
      rfl
    _ = { initialConfig (machine V) budget y with
          state := (machine V).reject } :=
      translateParser_reject_initial V y

/-- The raw empty word is malformed.  At its one-step parser deadline the full
combined configuration is the literal combined reject configuration. -/
theorem parser_reject_empty (V : UniformTM) (budget : Nat)
    (y : Bitstring 0) (hbudget : FixedPairParser.clock 0 ≤ budget) :
    (machine V).run (FixedPairParser.clock 0)
        (initialConfig (machine V) budget y) =
      { initialConfig (machine V) budget y with
        state := (machine V).reject } := by
  apply parser_reject_of_decodePair_none V y hbudget
  simp [decodePair, decodePairList]

/-- A closed, nonvacuous raw-empty regression at the exact parser allocation. -/
def emptyRawWord : Bitstring 0 := fun i => Fin.elim0 i

theorem parser_reject_empty_exactBudget (V : UniformTM) :
    (machine V).run (FixedPairParser.clock 0)
        (initialConfig (machine V) (FixedPairParser.clock 0) emptyRawWord) =
      { initialConfig (machine V) (FixedPairParser.clock 0) emptyRawWord with
        state := (machine V).reject } := by
  exact parser_reject_empty V (FixedPairParser.clock 0) emptyRawWord
    (Nat.le_refl _)

end FixedParserVerifier
end Pnp3.Complexity.Uniform.V1
