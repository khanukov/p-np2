import Complexity.Uniform.V1.Examples

/-!
# Uniform P V1 surface tests

This file pins the P1a executable machine, same-budget semantics, polynomial
clock, complement, and executable regression API.  Every authored public theorem
has an explicit full-proposition wrapper here; theorem axiom output lives only
in the central `Tests/AxiomsAudit.lean`.
-/

namespace Pnp3.Tests.UniformV1

open Pnp3.Complexity.Uniform.V1

#check Bitstring
#check Language
#check Move
#check Move.left
#check Move.stay
#check Move.right
#check tapeLength
#check UniformTM
#check UniformTM.mk
#check Config
#check Config.mk
#check UniformTM.step
#check moveHead
#check initialConfig
#check UniformTM.stepConfig
#check UniformTM.run
#check AcceptsAt
#check RejectsAt
#check AcceptsWithin
#check RejectsWithin
#check DecidesAt
#check DecidesWithin
#check polyClock
#check UniformP
#check UniformTM.swap
#check complement
#check constTrue
#check constFalse
#check firstBit
#check lengthParityLanguage
#check allAcceptMachine
#check allRejectMachine
#check firstBitMachine
#check lengthParityMachine
#check nonterminalMachine

#synth DecidableEq Move

/-- Regression pin: `UniformTM.mk` has exactly the finite P1a fields, with an
`Option Bool` transition alphabet and no `Nat → Nat` or runtime field. -/
def constructorShapeRegression : UniformTM :=
  UniformTM.mk
    2
    (⟨0, by decide⟩)
    (⟨0, by decide⟩)
    (⟨1, by decide⟩)
    (by decide)
    (fun q (symbol : Option Bool) => (q, symbol, Move.stay))

def check_step_accept (M : UniformTM) (symbol : Option Bool) :
    M.step M.accept symbol = (M.accept, symbol, Move.stay) :=
  M.step_accept symbol

def check_step_reject (M : UniformTM) (symbol : Option Bool) :
    M.step M.reject symbol = (M.reject, symbol, Move.stay) :=
  M.step_reject symbol

def check_moveHead_left_zero (length : Nat) :
    moveHead (⟨0, Nat.zero_lt_succ length⟩ : Fin (length + 1)) Move.left =
      ⟨0, Nat.zero_lt_succ length⟩ :=
  moveHead_left_zero length

def check_moveHead_right_last (length : Nat) :
    moveHead (Fin.last length) Move.right = Fin.last length :=
  moveHead_right_last length

def check_stepConfig_accept (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.accept) :
    M.stepConfig c = c :=
  M.stepConfig_accept c h

def check_stepConfig_reject (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.reject) :
    M.stepConfig c = c :=
  M.stepConfig_reject c h

def check_run_add (M : UniformTM) {n budget : Nat} (a b : Nat)
    (c : Config M.stateCount n budget) :
    M.run (a + b) c = M.run b (M.run a c) :=
  M.run_add a b c

def check_run_accept (M : UniformTM) {n budget steps : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.accept) :
    M.run steps c = c :=
  M.run_accept c h steps

def check_run_reject (M : UniformTM) {n budget steps : Nat}
    (c : Config M.stateCount n budget) (h : c.state = M.reject) :
    M.run steps c = c :=
  M.run_reject c h steps

def check_initialConfig_tape_input (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) (i : Fin n) :
    (initialConfig M budget x).tape
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n (budget + 1))⟩ =
        some (x i) :=
  initialConfig_tape_input M (budget := budget) x i

def check_initialConfig_tape_padding (M : UniformTM) {n budget : Nat}
    (x : Bitstring n) (i : Fin (tapeLength n budget)) (h : n ≤ i.val) :
    (initialConfig M budget x).tape i = none :=
  initialConfig_tape_padding M (budget := budget) x i h

def check_acceptsAt_budget_iff_acceptsWithin (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) :
    AcceptsAt M budget budget x ↔ AcceptsWithin M budget x :=
  acceptsAt_budget_iff_acceptsWithin M x

def check_rejectsAt_budget_iff_rejectsWithin (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) :
    RejectsAt M budget budget x ↔ RejectsWithin M budget x :=
  rejectsAt_budget_iff_rejectsWithin M x

def check_not_acceptsAt_and_rejectsAt (M : UniformTM)
    {n budget steps : Nat} (x : Bitstring n) :
    ¬ (AcceptsAt M budget steps x ∧ RejectsAt M budget steps x) :=
  not_acceptsAt_and_rejectsAt M x

def check_not_acceptsWithin_and_rejectsWithin (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) :
    ¬ (AcceptsWithin M budget x ∧ RejectsWithin M budget x) :=
  not_acceptsWithin_and_rejectsWithin M x

def check_decidesAt_budget_iff_decidesWithin (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) (answer : Bool) :
    DecidesAt M budget budget x answer ↔ DecidesWithin M budget x answer :=
  decidesAt_budget_iff_decidesWithin M x answer

def check_not_decidesAt_true_and_false (M : UniformTM)
    {n budget steps : Nat} (x : Bitstring n) :
    ¬ (DecidesAt M budget steps x true ∧ DecidesAt M budget steps x false) :=
  not_decidesAt_true_and_false M x

def check_not_decidesWithin_true_and_false (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) :
    ¬ (DecidesWithin M budget x true ∧ DecidesWithin M budget x false) :=
  not_decidesWithin_true_and_false M x

def check_polyClock_exponent_zero (n : Nat) : polyClock 0 n = 1 :=
  polyClock_exponent_zero n

def check_polyClock_zero_zero : polyClock 0 0 = 1 :=
  polyClock_zero_zero

def check_polyClock_input_zero (c : Nat) :
    polyClock c 0 = if c = 0 then 1 else c :=
  polyClock_input_zero c

def check_polyClock_exponent_one (n : Nat) : polyClock 1 n = n + 1 :=
  polyClock_exponent_one n

def check_polyClock_pos (c n : Nat) : 0 < polyClock c n :=
  polyClock_pos c n

def check_uniformP_iff_exists_decidesAt (L : Language) :
    UniformP L ↔
      ∃ M c, ∀ n (x : Bitstring n),
        DecidesAt M (polyClock c n) (polyClock c n) x (L n x) :=
  uniformP_iff_exists_decidesAt L

def check_swap_step (M : UniformTM) (q : Fin M.stateCount)
    (symbol : Option Bool) :
    M.swap.step q symbol = M.step q symbol :=
  M.swap_step q symbol

def check_swap_stepConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    M.swap.stepConfig c = M.stepConfig c :=
  M.swap_stepConfig c

def check_swap_run (M : UniformTM) {n budget steps : Nat}
    (c : Config M.stateCount n budget) :
    M.swap.run steps c = M.run steps c :=
  M.swap_run steps c

def check_swap_acceptsAt_iff_rejectsAt (M : UniformTM)
    {n budget steps : Nat} (x : Bitstring n) :
    AcceptsAt M.swap budget steps x ↔ RejectsAt M budget steps x :=
  M.swap_acceptsAt_iff_rejectsAt x

def check_swap_rejectsAt_iff_acceptsAt (M : UniformTM)
    {n budget steps : Nat} (x : Bitstring n) :
    RejectsAt M.swap budget steps x ↔ AcceptsAt M budget steps x :=
  M.swap_rejectsAt_iff_acceptsAt x

def check_swap_decidesWithin (M : UniformTM)
    {n budget : Nat} (x : Bitstring n) (answer : Bool) :
    DecidesWithin M.swap budget x (!answer) ↔ DecidesWithin M budget x answer :=
  M.swap_decidesWithin x answer

def check_uniformP_complement (L : Language) (h : UniformP L) :
    UniformP (complement L) :=
  uniformP_complement L h

def check_allAccept_acceptsAt {n budget steps : Nat} (x : Bitstring n) :
    AcceptsAt allAcceptMachine budget steps x :=
  allAccept_acceptsAt x

def check_allAccept_acceptsWithin {n budget : Nat} (x : Bitstring n) :
    AcceptsWithin allAcceptMachine budget x :=
  allAccept_acceptsWithin x

def check_allReject_rejectsAt {n budget steps : Nat} (x : Bitstring n) :
    RejectsAt allRejectMachine budget steps x :=
  allReject_rejectsAt x

def check_allReject_rejectsWithin {n budget : Nat} (x : Bitstring n) :
    RejectsWithin allRejectMachine budget x :=
  allReject_rejectsWithin x

def check_firstBit_acceptsAt_iff {n budget steps : Nat} (x : Bitstring n)
    (h : 1 ≤ steps) :
    AcceptsAt firstBitMachine budget steps x ↔ firstBit n x = true :=
  firstBit_acceptsAt_iff x h

def check_firstBit_rejectsAt_iff {n budget steps : Nat} (x : Bitstring n)
    (h : 1 ≤ steps) :
    RejectsAt firstBitMachine budget steps x ↔ firstBit n x = false :=
  firstBit_rejectsAt_iff x h

def check_firstBit_acceptsWithin_iff {n budget : Nat} (x : Bitstring n)
    (h : 1 ≤ budget) :
    AcceptsWithin firstBitMachine budget x ↔ firstBit n x = true :=
  firstBit_acceptsWithin_iff x h

def check_firstBit_rejectsWithin_iff {n budget : Nat} (x : Bitstring n)
    (h : 1 ≤ budget) :
    RejectsWithin firstBitMachine budget x ↔ firstBit n x = false :=
  firstBit_rejectsWithin_iff x h

def check_firstBit_decidesAt {n budget steps : Nat} (x : Bitstring n)
    (h : 1 ≤ steps) :
    DecidesAt firstBitMachine budget steps x (firstBit n x) :=
  firstBit_decidesAt x h

def check_firstBit_decidesWithin {n budget : Nat} (x : Bitstring n)
    (h : 1 ≤ budget) :
    DecidesWithin firstBitMachine budget x (firstBit n x) :=
  firstBit_decidesWithin x h

def check_firstBit_true_verdict :
    DecidesWithin firstBitMachine 1 (fun _ : Fin 1 => true) true :=
  firstBit_true_verdict

def check_firstBit_false_verdict :
    DecidesWithin firstBitMachine 1 (fun _ : Fin 0 => true) false :=
  firstBit_false_verdict

def check_lengthParity_decidesAt {n budget : Nat} (x : Bitstring n) :
    DecidesAt lengthParityMachine budget (n + 1) x
      (lengthParityLanguage n x) :=
  lengthParity_decidesAt x

def check_lengthParity_decidesWithin {n : Nat} (x : Bitstring n) :
    DecidesWithin lengthParityMachine (n + 1) x
      (lengthParityLanguage n x) :=
  lengthParity_decidesWithin x

def check_lengthParity_empty_verdict :
    DecidesWithin lengthParityMachine 1 (fun _ : Fin 0 => false) true :=
  lengthParity_empty_verdict

def check_lengthParity_one_verdict (bit : Bool) :
    DecidesWithin lengthParityMachine 2 (fun _ : Fin 1 => bit) false :=
  lengthParity_one_verdict bit

def check_lengthParity_two_verdict (x : Bitstring 2) :
    DecidesWithin lengthParityMachine 3 x true :=
  lengthParity_two_verdict x

def check_nonterminal_run_state {n budget steps : Nat} (x : Bitstring n) :
    (nonterminalMachine.run steps (initialConfig nonterminalMachine budget x)).state =
      nonterminalMachine.start :=
  nonterminal_run_state x steps

def check_nonterminal_acceptFlag_false {n budget : Nat} (x : Bitstring n) :
    ((nonterminalMachine.run budget
      (initialConfig nonterminalMachine budget x)).state ==
        nonterminalMachine.accept) = false :=
  nonterminal_acceptFlag_false x

def check_nonterminal_not_rejectsWithin {n budget : Nat} (x : Bitstring n) :
    ¬ RejectsWithin nonterminalMachine budget x :=
  nonterminal_not_rejectsWithin x

def check_nonterminal_not_acceptsWithin {n budget : Nat} (x : Bitstring n) :
    ¬ AcceptsWithin nonterminalMachine budget x :=
  nonterminal_not_acceptsWithin x

def check_nonterminal_not_decidesWithin_false {n budget : Nat} (x : Bitstring n) :
    ¬ DecidesWithin nonterminalMachine budget x false :=
  nonterminal_not_decidesWithin_false x

def check_nonterminal_not_decidesWithin_true {n budget : Nat} (x : Bitstring n) :
    ¬ DecidesWithin nonterminalMachine budget x true :=
  nonterminal_not_decidesWithin_true x

def check_nonterminal_timeout_counterexample {n budget : Nat} (x : Bitstring n) :
    ((nonterminalMachine.run budget
        (initialConfig nonterminalMachine budget x)).state ==
          nonterminalMachine.accept) = false ∧
      ¬ AcceptsWithin nonterminalMachine budget x ∧
      ¬ RejectsWithin nonterminalMachine budget x ∧
      ¬ DecidesWithin nonterminalMachine budget x true ∧
      ¬ DecidesWithin nonterminalMachine budget x false :=
  nonterminal_timeout_counterexample x

def check_uniformP_constTrue : UniformP constTrue := uniformP_constTrue
def check_uniformP_constFalse : UniformP constFalse := uniformP_constFalse
def check_uniformP_firstBit : UniformP firstBit := uniformP_firstBit
def check_uniformP_lengthParity : UniformP lengthParityLanguage :=
  uniformP_lengthParity

end Pnp3.Tests.UniformV1
