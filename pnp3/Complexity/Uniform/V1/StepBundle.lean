import Complexity.Uniform.V1.StepKernel
/-!
# Direct shared step bundle for Uniform V1
This P1b-3 feasibility slice compiles scanning, canonical symbol selection,
state/symbol rows, and transition actions into one shared `DagBundle`.  Every
new layer is built over already-materialized outputs and the predecessor graph
is substituted exactly once.
-/
namespace Pnp3.Complexity.Uniform.V1.Circuit
open scoped BigOperators
open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
@[simp] private theorem inputProj_gates {N : Nat} (i : Fin N) :
    (inputProj i).gates = 0 := rfl
private def andInputs {N : Nat} (a b : Fin N) : DagCircuit N :=
  substInputs andCircuit ![inputProj a, inputProj b]
@[simp] private theorem andInputs_gates {N : Nat} (a b : Fin N) :
    (andInputs a b).gates = 1 := rfl
@[simp] private theorem eval_andInputs {N : Nat} (a b : Fin N)
    (v : Bitstring N) : eval (andInputs a b) v = (v a && v b) := by
  simp [andInputs]
private def notInput {N : Nat} (a : Fin N) : DagCircuit N :=
  substInputs notCircuit ![inputProj a]
@[simp] private theorem notInput_gates {N : Nat} (a : Fin N) :
    (notInput a).gates = 1 := rfl
@[simp] private theorem eval_notInput {N : Nat} (a : Fin N)
    (v : Bitstring N) : eval (notInput a) v = !v a := by
  simp [notInput]
/-- Number of public action rails: next state, three moves, and two write
rails. -/
def actionWidth (M : UniformTM) : Nat := M.stateCount + 5
/-- Compile-time alphabet index in blank/false/true order. -/
def indexedSymbol : Fin 3 → Option Bool
  | ⟨0, _⟩ => none
  | ⟨1, _⟩ => some false
  | ⟨2, _⟩ => some true
/-- Symbol-major row offset: all states for blank, then false, then true. -/
def rowIndex (M : UniformTM) (q : Fin M.stateCount) (s : Fin 3) :
    Fin (M.stateCount * 3) :=
  ⟨s.val * M.stateCount + q.val, by
    calc
      s.val * M.stateCount + q.val < s.val * M.stateCount + M.stateCount :=
        Nat.add_lt_add_left q.isLt _
      _ = (s.val + 1) * M.stateCount := by rw [Nat.add_mul]; simp
      _ ≤ 3 * M.stateCount := Nat.mul_le_mul_right _ s.isLt
      _ = M.stateCount * 3 := Nat.mul_comm _ _⟩
/-- Next-state rail inside the action block. -/
def nextStateActionIndex (M : UniformTM) (q : Fin M.stateCount) :
    Fin (actionWidth M) :=
  ⟨q.val, by simp [actionWidth]; omega⟩
/-- Move rail inside the action block, in left/stay/right order. -/
def moveActionIndex (M : UniformTM) : Move → Fin (actionWidth M)
  | .left => ⟨M.stateCount, by simp [actionWidth]⟩
  | .stay => ⟨M.stateCount + 1, by simp [actionWidth]⟩
  | .right => ⟨M.stateCount + 2, by simp [actionWidth]⟩
/-- Write-presence rail inside the action block. -/
def writePresentActionIndex (M : UniformTM) : Fin (actionWidth M) :=
  ⟨M.stateCount + 3, by simp [actionWidth]⟩
/-- Write-value rail inside the action block. -/
def writeValueActionIndex (M : UniformTM) : Fin (actionWidth M) :=
  ⟨M.stateCount + 4, by simp [actionWidth]⟩
private def scanInputIndex (M : UniformTM) (n budget : Nat) (rail : Bool)
    (i : Fin (tapeLength n budget)) : Fin (configWidth M n budget) :=
  if rail then tapeValueIndex M n budget i else tapePresentIndex M n budget i
private def scanCircuit (M : UniformTM) (n budget : Nat) (rail : Bool) :
    DagCircuit (configWidth M n budget) :=
  bigOrCircuit ((List.finRange (tapeLength n budget)).map fun i =>
    andInputs (headIndex M n budget i) (scanInputIndex M n budget rail i))
private def rawScanBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget) 2 :=
  bundleOfFamily 2 ![scanCircuit M n budget false, scanCircuit M n budget true]
private def scanBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget) (configWidth M n budget + 2) :=
  passthroughBundle (rawScanBundle M n budget)
private def scanPresentIndex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget + 2) := Fin.natAdd _ (0 : Fin 2)
private def scanValueIndex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget + 2) := Fin.natAdd _ (1 : Fin 2)
private theorem scanCircuit_eval (M : UniformTM) (n budget : Nat)
    (rail : Bool) (v : Bitstring (configWidth M n budget)) :
    eval (scanCircuit M n budget rail) v =
      if rail then scanValue M n budget v else scanPresent M n budget v := by
  cases rail <;>
    simp [scanCircuit, scanInputIndex, scanValue, scanPresent, headBit,
      presentBit, valueBit, Function.comp_def]
private theorem rawScanBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawScanBundle M n budget).gates = 4 * tapeLength n budget + 2 := by
  rw [rawScanBundle, bundleOfFamily_gates]
  simp [scanCircuit, Function.comp_def]
  omega
private theorem scanBundle_old (M : UniformTM) (n budget : Nat)
    (i : Fin (configWidth M n budget)) (v : Bitstring (configWidth M n budget)) :
    (scanBundle M n budget).evalOutput (Fin.castAdd 2 i) v = v i := by
  simp [scanBundle]
private theorem scanBundle_present (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (scanBundle M n budget).evalOutput (scanPresentIndex M n budget) v =
      scanPresent M n budget v := by
  simp [scanBundle, scanPresentIndex, rawScanBundle, scanCircuit_eval]
private theorem scanBundle_value (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (scanBundle M n budget).evalOutput (scanValueIndex M n budget) v =
      scanValue M n budget v := by
  simp [scanBundle, scanValueIndex, rawScanBundle, scanCircuit_eval]
private def rawComplementBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + 2) 2 :=
  bundleOfFamily 2 ![
    notInput (scanPresentIndex M n budget),
    notInput (scanValueIndex M n budget)]
private theorem rawComplementBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawComplementBundle M n budget).gates = 2 := by
  rw [rawComplementBundle, bundleOfFamily_gates]
  simp
private def complementBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget) (configWidth M n budget + 2 + 2) :=
  substBundle (passthroughBundle (rawComplementBundle M n budget))
    (scanBundle M n budget)
private def notPresentIndex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget + 2 + 2) := Fin.natAdd _ (0 : Fin 2)
private def notValueIndex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget + 2 + 2) := Fin.natAdd _ (1 : Fin 2)
private def liftedScanPresentIndex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget + 2 + 2) := Fin.castAdd 2 (scanPresentIndex M n budget)
private def liftedScanValueIndex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget + 2 + 2) := Fin.castAdd 2 (scanValueIndex M n budget)
private theorem complementBundle_gates (M : UniformTM) (n budget : Nat) :
    (complementBundle M n budget).gates = 4 * tapeLength n budget + 4 := by
  rw [complementBundle, substBundle_gates, passthroughBundle_gates,
    rawComplementBundle_gates]
  change (rawScanBundle M n budget).gates + 2 = _
  rw [rawScanBundle_gates]
private theorem complementBundle_scanPresent (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (complementBundle M n budget).evalOutput
        (liftedScanPresentIndex M n budget) v = scanPresent M n budget v := by
  simp [complementBundle, liftedScanPresentIndex, scanBundle_present]
private theorem complementBundle_scanValue (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (complementBundle M n budget).evalOutput
        (liftedScanValueIndex M n budget) v = scanValue M n budget v := by
  simp [complementBundle, liftedScanValueIndex, scanBundle_value]
private theorem complementBundle_notPresent (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (complementBundle M n budget).evalOutput (notPresentIndex M n budget) v =
      !scanPresent M n budget v := by
  simp [complementBundle, notPresentIndex, rawComplementBundle, scanBundle_present]
private theorem complementBundle_notValue (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (complementBundle M n budget).evalOutput (notValueIndex M n budget) v =
      !scanValue M n budget v := by
  simp [complementBundle, notValueIndex, rawComplementBundle, scanBundle_value]
private theorem complementBundle_old (M : UniformTM) (n budget : Nat)
    (i : Fin (configWidth M n budget)) (v : Bitstring (configWidth M n budget)) :
    (complementBundle M n budget).evalOutput ⟨i.val, by
      have := i.isLt; omega⟩ v = v i := by
  rw [complementBundle, evalOutput_substBundle]
  rw [show (⟨i.val, by have := i.isLt; omega⟩ :
      Fin (configWidth M n budget + 2 + 2)) =
      Fin.castAdd 2 (Fin.castAdd 2 i) by apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, scanBundle_old]
private def selectorCircuit (M : UniformTM) (n budget : Nat) :
    Fin 3 → DagCircuit (configWidth M n budget + 2 + 2)
  | ⟨0, _⟩ => andInputs
      (notPresentIndex M n budget) (notValueIndex M n budget)
  | ⟨1, _⟩ => andInputs
      (liftedScanPresentIndex M n budget) (notValueIndex M n budget)
  | ⟨2, _⟩ => andInputs
      (liftedScanPresentIndex M n budget) (liftedScanValueIndex M n budget)
@[simp] private theorem selectorCircuit_gates (M : UniformTM) (n budget : Nat)
    (s : Fin 3) : (selectorCircuit M n budget s).gates = 1 := by
  fin_cases s <;> rfl
private def rawSelectorBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + 2 + 2) 3 :=
  bundleOfFamily 3 (selectorCircuit M n budget)
private theorem rawSelectorBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawSelectorBundle M n budget).gates = 3 := by
  rw [rawSelectorBundle, bundleOfFamily_gates]
  simp
private def selectorBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget) (configWidth M n budget + 2 + 2 + 3) :=
  substBundle (passthroughBundle (rawSelectorBundle M n budget))
    (complementBundle M n budget)
private def selectorIndex (M : UniformTM) (n budget : Nat) (s : Fin 3) :
    Fin (configWidth M n budget + 2 + 2 + 3) := Fin.natAdd _ s
private theorem selectorBundle_gates (M : UniformTM) (n budget : Nat) :
    (selectorBundle M n budget).gates = 4 * tapeLength n budget + 7 := by
  rw [selectorBundle, substBundle_gates, passthroughBundle_gates,
    rawSelectorBundle_gates, complementBundle_gates]
private theorem selectorBundle_eval (M : UniformTM) (n budget : Nat)
    (s : Fin 3) (v : Bitstring (configWidth M n budget)) :
    (selectorBundle M n budget).evalOutput (selectorIndex M n budget s) v =
      symbolGuard M n budget v (indexedSymbol s) := by
  fin_cases s <;>
    simp [selectorBundle, selectorIndex, rawSelectorBundle, selectorCircuit,
      complementBundle_notPresent, complementBundle_notValue,
      complementBundle_scanPresent, complementBundle_scanValue,
      symbolGuard, indexedSymbol, symbolPresent, symbolValue]
private theorem selectorBundle_old (M : UniformTM) (n budget : Nat)
    (i : Fin (configWidth M n budget)) (v : Bitstring (configWidth M n budget)) :
    (selectorBundle M n budget).evalOutput ⟨i.val, by
      have := i.isLt; omega⟩ v = v i := by
  rw [selectorBundle, evalOutput_substBundle]
  rw [show (⟨i.val, by have := i.isLt; omega⟩ :
      Fin (configWidth M n budget + 2 + 2 + 3)) =
      Fin.castAdd 3 ⟨i.val, by have := i.isLt; omega⟩ by apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, complementBundle_old]
private def rowState (M : UniformTM) (o : Fin (M.stateCount * 3)) :
    Fin M.stateCount :=
  ⟨o.val % M.stateCount, Nat.mod_lt _ (Nat.zero_lt_of_lt M.accept.isLt)⟩
private def rowSymbol (M : UniformTM) (o : Fin (M.stateCount * 3)) : Fin 3 :=
  ⟨o.val / M.stateCount, by
    apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt M.accept.isLt)).2
    simpa only [Nat.mul_comm] using o.isLt⟩
private theorem rowState_rowIndex (M : UniformTM) (q : Fin M.stateCount) (s : Fin 3) :
    rowState M (rowIndex M q s) = q := by
  apply Fin.ext
  simp [rowState, rowIndex, Nat.add_mod, Nat.mod_eq_of_lt q.isLt]
private theorem rowSymbol_rowIndex (M : UniformTM) (q : Fin M.stateCount) (s : Fin 3) :
    rowSymbol M (rowIndex M q s) = s := by
  apply Fin.ext
  change (s.val * M.stateCount + q.val) / M.stateCount = s.val
  rw [Nat.mul_comm s.val M.stateCount,
    Nat.mul_add_div (Nat.zero_lt_of_lt M.accept.isLt)]
  simp [Nat.div_eq_of_lt q.isLt]
private def rowCircuit (M : UniformTM) (n budget : Nat)
    (o : Fin (M.stateCount * 3)) :
    DagCircuit (configWidth M n budget + 2 + 2 + 3) :=
  andInputs (Fin.castAdd 7 (stateIndex M n budget (rowState M o)))
    (selectorIndex M n budget (rowSymbol M o))
@[simp] private theorem rowCircuit_gates (M : UniformTM) (n budget : Nat)
    (o : Fin (M.stateCount * 3)) : (rowCircuit M n budget o).gates = 1 := rfl
private def rawRowBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + 2 + 2 + 3) (M.stateCount * 3) :=
  bundleOfFamily _ (rowCircuit M n budget)
private theorem rawRowBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawRowBundle M n budget).gates = M.stateCount * 3 := by
  rw [rawRowBundle, bundleOfFamily_gates]
  simp
private def rowBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget)
      (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3) :=
  substBundle (passthroughBundle (rawRowBundle M n budget))
    (selectorBundle M n budget)
private def materializedRowIndex (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (s : Fin 3) :
    Fin (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3) :=
  Fin.natAdd _ (rowIndex M q s)
private theorem rowBundle_gates (M : UniformTM) (n budget : Nat) :
    (rowBundle M n budget).gates =
      4 * tapeLength n budget + 7 + M.stateCount * 3 := by
  rw [rowBundle, substBundle_gates, passthroughBundle_gates,
    rawRowBundle_gates, selectorBundle_gates]
private theorem rowBundle_old (M : UniformTM) (n budget : Nat)
    (i : Fin (configWidth M n budget)) (v : Bitstring (configWidth M n budget)) :
    (rowBundle M n budget).evalOutput
        ⟨i.val, by have := i.isLt; omega⟩ v = v i := by
  rw [rowBundle, evalOutput_substBundle]
  rw [show (⟨i.val, by have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3)) =
      Fin.castAdd (M.stateCount * 3) ⟨i.val, by
        have := i.isLt; omega⟩ by apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, selectorBundle_old]
private theorem rowBundle_eval (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (s : Fin 3)
    (v : Bitstring (configWidth M n budget)) :
    (rowBundle M n budget).evalOutput (materializedRowIndex M n budget q s) v =
      branch M n budget v q (indexedSymbol s) := by
  rw [rowBundle, evalOutput_substBundle]
  rw [show materializedRowIndex M n budget q s =
      Fin.natAdd (configWidth M n budget + 2 + 2 + 3) (rowIndex M q s) by
        apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_output, rawRowBundle,
    evalOutput_bundleOfFamily, rowCircuit, eval_andInputs,
    rowState_rowIndex, rowSymbol_rowIndex]
  have hold := selectorBundle_old M n budget (stateIndex M n budget q) v
  have hselector := selectorBundle_eval M n budget s v
  rw [show (selectorBundle M n budget).evalOutput
      (Fin.castAdd 7 (stateIndex M n budget q)) v = v (stateIndex M n budget q) by
        convert hold using 1]
  rw [hselector]
  rfl
private def transitionRows (M : UniformTM) : List (Fin M.stateCount × Fin 3) :=
  (List.finRange M.stateCount).flatMap fun q =>
    (List.finRange 3).map fun s => (q, s)
/-- Number of public transition rows whose fixed action satisfies `predicate`.
This is exposed only to state the exact shared gate accounting. -/
def actionSupportCount (M : UniformTM)
    (predicate : (Fin M.stateCount × Option Bool × Move) → Bool) : Nat :=
  ((transitionRows M).filter fun r => predicate (M.step r.1 (indexedSymbol r.2))).length
private def moveCode : Move → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2
private def indexedMove : Fin 3 → Move
  | ⟨0, _⟩ => .left
  | ⟨1, _⟩ => .stay
  | ⟨2, _⟩ => .right
private theorem movePredicate_eq (i : Fin 3) (move : Move) :
    decide (i = moveCode move) = decide (indexedMove i = move) := by
  fin_cases i <;> cases move <;> rfl
/-- Meaning of one rail inside the action block. -/
def actionPredicate (M : UniformTM) (o : Fin (actionWidth M))
    (action : Fin M.stateCount × Option Bool × Move) : Bool :=
  if h : o.val < M.stateCount then decide (⟨o.val, h⟩ = action.1)
  else if o.val = M.stateCount then decide (Move.left = action.2.2)
  else if o.val = M.stateCount + 1 then decide (Move.stay = action.2.2)
  else if o.val = M.stateCount + 2 then decide (Move.right = action.2.2)
  else if o.val = M.stateCount + 3 then symbolPresent action.2.1
  else symbolValue action.2.1
@[simp] private theorem actionPredicate_moveActionIndex (M : UniformTM)
    (move : Move) (action : Fin M.stateCount × Option Bool × Move) :
    actionPredicate M (moveActionIndex M move) action =
      decide (move = action.2.2) := by
  cases move <;> simp [actionPredicate, moveActionIndex]
private def selectedRows (M : UniformTM) (o : Fin (actionWidth M)) :=
  (transitionRows M).filter fun r =>
    actionPredicate M o (M.step r.1 (indexedSymbol r.2))
private def actionCircuit (M : UniformTM) (n budget : Nat)
    (o : Fin (actionWidth M)) :
    DagCircuit (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3) :=
  bigOrCircuit ((selectedRows M o).map fun r =>
    inputProj (materializedRowIndex M n budget r.1 r.2))
private def rawActionBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3)
      (actionWidth M) :=
  bundleOfFamily _ (actionCircuit M n budget)
private def internalActionBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget)
      (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + actionWidth M) :=
  substBundle (passthroughBundle (rawActionBundle M n budget))
    (rowBundle M n budget)
private def publicActionReindex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget + actionWidth M) →
      Fin (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + actionWidth M) :=
  Fin.addCases
    (fun i => ⟨i.val, by
      have hi := i.isLt
      simp only [configWidth, actionWidth] at hi ⊢
      omega⟩)
    (fun a => ⟨configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + a.val, by
      have ha := a.isLt
      omega⟩)
/-- Direct shared action compiler.  The first `W` outputs are the original
configuration rails; the final `Q+5` outputs are action rails. -/
def actionBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget) (configWidth M n budget + actionWidth M) :=
  reindexOutputs (internalActionBundle M n budget) (publicActionReindex M n budget)
private theorem any_filter_eq {α : Type} (xs : List α) (p f : α → Bool) :
    (xs.filter p).any f = xs.any fun x => f x && p x := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases p a <;> cases f a <;> simp [Bool.and_comm]
private theorem finRange_three_any (f : Fin 3 → Bool) :
    (List.finRange 3).any f = (f 0 || (f 1 || f 2)) := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;>
    simp [List.finRange, h0, h1, h2]
private theorem actionCircuit_eval (M : UniformTM) (n budget : Nat)
    (o : Fin (actionWidth M)) (v : Bitstring (configWidth M n budget)) :
    eval (actionCircuit M n budget o)
      (fun j => (rowBundle M n budget).evalOutput j v) =
      actionOr M n budget v (actionPredicate M o) := by
  rw [actionCircuit, eval_bigOrCircuit_map]
  simp only [eval_inputProj, rowBundle_eval]
  simp only [selectedRows]
  rw [any_filter_eq]
  simp only [transitionRows, List.any_flatMap, List.any_map, actionOr]
  apply congrArg (List.any (List.finRange M.stateCount))
  funext q
  simp only [Function.comp_def, symbols, List.any_cons, List.any_nil]
  simpa only [Bool.or_false] using finRange_three_any (fun s =>
    branch M n budget v q (indexedSymbol s) &&
      actionPredicate M o (M.step q (indexedSymbol s)))
private theorem internalActionBundle_old (M : UniformTM) (n budget : Nat)
    (i : Fin (configWidth M n budget)) (v : Bitstring (configWidth M n budget)) :
    (internalActionBundle M n budget).evalOutput
        ⟨i.val, by have := i.isLt; omega⟩ v = v i := by
  rw [internalActionBundle, evalOutput_substBundle]
  rw [show (⟨i.val, by have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + actionWidth M)) =
      Fin.castAdd (actionWidth M) ⟨i.val, by
        have := i.isLt; omega⟩ by apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, rowBundle_old]
private theorem internalActionBundle_action (M : UniformTM) (n budget : Nat)
    (a : Fin (actionWidth M)) (v : Bitstring (configWidth M n budget)) :
    (internalActionBundle M n budget).evalOutput
        ⟨configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + a.val,
          by have := a.isLt; omega⟩ v =
      actionOr M n budget v (actionPredicate M a) := by
  rw [internalActionBundle, evalOutput_substBundle]
  rw [show (⟨configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + a.val,
      by have := a.isLt; omega⟩ : Fin
      (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + actionWidth M)) =
      Fin.natAdd (configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3) a by
        apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_output, rawActionBundle,
    evalOutput_bundleOfFamily, actionCircuit_eval]
/-- Full all-vector action semantics, including malformed symbol rails. -/
def actionEncoding (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    Bitstring (configWidth M n budget + actionWidth M) :=
  Fin.addCases v (fun o => actionOr M n budget v (actionPredicate M o))
/-- Every coordinate of the direct bundle has its exact all-vector meaning. -/
theorem actionBundle_evalFun (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (actionBundle M n budget).evalFun v = actionEncoding M n budget v := by
  funext o
  refine Fin.addCases (motive := fun o =>
    (actionBundle M n budget).evalFun v o = actionEncoding M n budget v o) ?_ ?_ o
  · intro i
    rw [DagBundle.evalFun_apply]
    simp only [actionBundle, evalOutput_reindexOutputs]
    rw [show publicActionReindex M n budget (Fin.castAdd (actionWidth M) i) =
      ⟨i.val, by have := i.isLt; omega⟩ by
        apply Fin.ext; simp [publicActionReindex]]
    rw [internalActionBundle_old]
    simp [actionEncoding]
  · intro a
    rw [DagBundle.evalFun_apply]
    simp only [actionBundle, evalOutput_reindexOutputs]
    rw [show publicActionReindex M n budget
        (Fin.natAdd (configWidth M n budget) a) =
      ⟨configWidth M n budget + 2 + 2 + 3 + M.stateCount * 3 + a.val,
        by have := a.isLt; omega⟩ by
          apply Fin.ext; simp [publicActionReindex]]
    rw [internalActionBundle_action]
    simp [actionEncoding]
@[simp] private theorem actionBundle_old (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (i : Fin (configWidth M n budget)) :
    (actionBundle M n budget).evalOutput (Fin.castAdd (actionWidth M) i) v = v i := by
  have h := congrFun (actionBundle_evalFun M n budget v)
    (Fin.castAdd (actionWidth M) i)
  simpa [actionEncoding] using h
@[simp] theorem actionBundle_nextState (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (q : Fin M.stateCount) :
    (actionBundle M n budget).evalOutput
        (Fin.natAdd (configWidth M n budget) (nextStateActionIndex M q)) v =
      nextStateBit M n budget v q := by
  have h := congrFun (actionBundle_evalFun M n budget v)
    (Fin.natAdd (configWidth M n budget) (nextStateActionIndex M q))
  rw [DagBundle.evalFun_apply] at h
  simp only [actionEncoding, Fin.addCases_right] at h
  rw [h]
  rw [nextStateBit]
  apply congrArg (actionOr M n budget v)
  funext action
  simp [actionPredicate, nextStateActionIndex, Fin.ext_iff]
@[simp] theorem actionBundle_move (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (move : Move) :
    (actionBundle M n budget).evalOutput
        (Fin.natAdd (configWidth M n budget) (moveActionIndex M move)) v =
      moveBit M n budget v move := by
  have h := congrFun (actionBundle_evalFun M n budget v)
    (Fin.natAdd (configWidth M n budget) (moveActionIndex M move))
  rw [DagBundle.evalFun_apply] at h
  simp only [actionEncoding, Fin.addCases_right] at h
  rw [h]
  rw [moveBit]
  apply congrArg (actionOr M n budget v)
  funext action
  cases move <;> simp [actionPredicate, moveActionIndex]
@[simp] theorem actionBundle_writePresent (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (actionBundle M n budget).evalOutput
        (Fin.natAdd (configWidth M n budget) (writePresentActionIndex M)) v =
      writePresent M n budget v := by
  have h := congrFun (actionBundle_evalFun M n budget v)
    (Fin.natAdd (configWidth M n budget) (writePresentActionIndex M))
  rw [DagBundle.evalFun_apply] at h
  simp only [actionEncoding, Fin.addCases_right] at h
  rw [h]
  rw [writePresent]
  apply congrArg (actionOr M n budget v)
  funext action
  simp [actionPredicate, writePresentActionIndex]
@[simp] theorem actionBundle_writeValue (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (actionBundle M n budget).evalOutput
        (Fin.natAdd (configWidth M n budget) (writeValueActionIndex M)) v =
      writeValue M n budget v := by
  have h := congrFun (actionBundle_evalFun M n budget v)
    (Fin.natAdd (configWidth M n budget) (writeValueActionIndex M))
  rw [DagBundle.evalFun_apply] at h
  simp only [actionEncoding, Fin.addCases_right] at h
  rw [h]
  rw [writeValue]
  apply congrArg (actionOr M n budget v)
  funext action
  simp [actionPredicate, writeValueActionIndex]
/-- Canonical inputs select exactly the fixed public transition action. -/
theorem actionBundle_eval_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    (actionBundle M n budget).evalFun (encodeConfig M c) =
      Fin.addCases (encodeConfig M c)
        (fun o => actionPredicate M o (M.step c.state (c.tape c.head))) := by
  rw [actionBundle_evalFun]
  funext o
  refine Fin.addCases ?_ ?_ o <;> intro i
  · simp [actionEncoding]
  · simp [actionEncoding]
private theorem transitionRows_length (M : UniformTM) :
    (transitionRows M).length = M.stateCount * 3 := by
  simp [transitionRows]
private theorem sum_filter_length_eq {α : Type} {k : Nat}
    (xs : List α) (f : α → Fin k) :
    (∑ i : Fin k, (xs.filter fun x => i = f x).length) = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      classical
      calc
        (∑ i : Fin k, ((a :: xs).filter fun x => i = f x).length) =
            ∑ i : Fin k, ((if i = f a then 1 else 0) +
              (xs.filter fun x => i = f x).length) := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases h : i = f a <;> simp [h, Nat.add_comm]
        _ = (∑ i : Fin k, if i = f a then 1 else 0) +
            ∑ i : Fin k, (xs.filter fun x => i = f x).length := by
              rw [Finset.sum_add_distrib]
        _ = 1 + xs.length := by rw [ih]; simp
        _ = xs.length + 1 := by omega
private theorem actionSupport_sum (M : UniformTM) :
    (∑ o : Fin (actionWidth M), (selectedRows M o).length) =
      2 * (M.stateCount * 3) +
        actionSupportCount M (fun a => symbolPresent a.2.1) +
        actionSupportCount M (fun a => symbolValue a.2.1) := by
  simp only [actionWidth]
  rw [Fin.sum_univ_add]
  have hstate := sum_filter_length_eq (transitionRows M)
    (fun r => (M.step r.1 (indexedSymbol r.2)).1)
  have hmove := sum_filter_length_eq (transitionRows M)
    (fun r => moveCode (M.step r.1 (indexedSymbol r.2)).2.2)
  have hmove' :
      ((transitionRows M).filter fun r =>
          decide (Move.left = (M.step r.1 (indexedSymbol r.2)).2.2)).length +
        ((transitionRows M).filter fun r =>
          decide (Move.stay = (M.step r.1 (indexedSymbol r.2)).2.2)).length +
        ((transitionRows M).filter fun r =>
          decide (Move.right = (M.step r.1 (indexedSymbol r.2)).2.2)).length =
        (transitionRows M).length := by
    have hx :
        ((transitionRows M).filter fun r =>
            decide (Move.left = (M.step r.1 (indexedSymbol r.2)).2.2)).length +
          (((transitionRows M).filter fun r =>
            decide (Move.stay = (M.step r.1 (indexedSymbol r.2)).2.2)).length +
          ((transitionRows M).filter fun r =>
            decide (Move.right = (M.step r.1 (indexedSymbol r.2)).2.2)).length) =
          (transitionRows M).length := by
      simpa [Fin.sum_univ_succ, movePredicate_eq, indexedMove] using hmove
    omega
  simp only [selectedRows]
  simp [Fin.sum_univ_succ, actionPredicate, actionSupportCount,
    transitionRows_length] at hstate hmove' ⊢
  omega
private theorem rawActionBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawActionBundle M n budget).gates =
      actionWidth M + 2 * (M.stateCount * 3) +
        actionSupportCount M (fun a => symbolPresent a.2.1) +
        actionSupportCount M (fun a => symbolValue a.2.1) := by
  rw [rawActionBundle, bundleOfFamily_gates]
  simp only [actionCircuit, bigOrCircuit_gates]
  simp only [List.map_map]
  simp only [Function.comp_def, inputProj_gates, zero_add]
  have sum_map_one {α : Type} (xs : List α) :
      (xs.map fun _ => 1).sum = xs.length := by
    induction xs with
    | nil => rfl
    | cons _ xs ih => simp [Nat.add_comm]
  simp_rw [sum_map_one]
  calc
    (∑ x, (1 + (selectedRows M x).length)) =
        (∑ _x : Fin (actionWidth M), 1) +
          ∑ x, (selectedRows M x).length := by
            rw [Finset.sum_add_distrib]
    _ = actionWidth M + 2 * (M.stateCount * 3) +
          actionSupportCount M (fun a => symbolPresent a.2.1) +
          actionSupportCount M (fun a => symbolValue a.2.1) := by
            rw [actionSupport_sum]
            simp
            omega
/-- Exact accounting: `4T+2` scan gates, two shared complements, three
selectors, `3Q` row gates, action seeds/selected projections, and no gates for
the final reindexing. -/
theorem actionBundle_gates (M : UniformTM) (n budget : Nat) :
    (actionBundle M n budget).gates =
      4 * tapeLength n budget + 10 * M.stateCount + 12 +
        actionSupportCount M (fun a => symbolPresent a.2.1) +
        actionSupportCount M (fun a => symbolValue a.2.1) := by
  simp [actionBundle, internalActionBundle, rowBundle_gates,
    rawActionBundle_gates, actionWidth]
  omega
/-- Honest linear gate cap for the complete action slice. -/
theorem actionBundle_gates_le (M : UniformTM) (n budget : Nat) :
    (actionBundle M n budget).gates ≤
      4 * tapeLength n budget + 16 * M.stateCount + 12 := by
  rw [actionBundle_gates]
  have hp := List.length_filter_le
    (fun r => symbolPresent (M.step r.1 (indexedSymbol r.2)).2.1)
    (transitionRows M)
  have hv := List.length_filter_le
    (fun r => symbolValue (M.step r.1 (indexedSymbol r.2)).2.1)
    (transitionRows M)
  change actionSupportCount M (fun a => symbolPresent a.2.1) ≤ _ at hp
  change actionSupportCount M (fun a => symbolValue a.2.1) ≤ _ at hv
  rw [transitionRows_length] at hp hv
  omega
/-- Requested presentation of the action cap; positivity of `stateCount` makes
this a direct corollary of the sharper bound above. -/
theorem actionBundle_gates_le_target (M : UniformTM) (n budget : Nat) :
    (actionBundle M n budget).gates ≤
      4 * tapeLength n budget + 22 * M.stateCount + 7 := by
  have h := actionBundle_gates_le M n budget
  have hQ := Nat.zero_lt_of_lt M.accept.isLt
  omega
/-! ## Full one-step update layer -/
private def oldActionInput (M : UniformTM) (n budget : Nat)
    (i : Fin (configWidth M n budget)) :
    Fin (configWidth M n budget + actionWidth M) := Fin.castAdd _ i
private def actionInput (M : UniformTM) (n budget : Nat)
    (a : Fin (actionWidth M)) :
    Fin (configWidth M n budget + actionWidth M) := Fin.natAdd _ a
private def headPairs (n budget : Nat) :
    List (Fin (tapeLength n budget) × Fin 3) :=
  (List.finRange (tapeLength n budget)).flatMap fun old =>
    (List.finRange 3).map fun m => (old, m)
private def selectedHeadPairs (n budget : Nat)
    (i : Fin (tapeLength n budget)) :=
  (headPairs n budget).filter fun p =>
    decide (i = moveHead p.1 (indexedMove p.2))
private def updateHeadCircuit (M : UniformTM) (n budget : Nat)
    (i : Fin (tapeLength n budget)) :
    DagCircuit (configWidth M n budget + actionWidth M) :=
  bigOrCircuit ((selectedHeadPairs n budget i).map fun p =>
    andInputs
      (oldActionInput M n budget (headIndex M n budget p.1))
      (actionInput M n budget (moveActionIndex M (indexedMove p.2))))
private def rawUpdateHeadBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + actionWidth M) (tapeLength n budget) :=
  bundleOfFamily _ (updateHeadCircuit M n budget)
private def updateHeadStage (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + actionWidth M)
      (configWidth M n budget + actionWidth M + tapeLength n budget) :=
  passthroughBundle (rawUpdateHeadBundle M n budget)
private def updateHeadOutputIndex (M : UniformTM) (n budget : Nat)
    (i : Fin (tapeLength n budget)) :
    Fin (configWidth M n budget + actionWidth M + tapeLength n budget) :=
  Fin.natAdd _ i
private def updateTapeCircuit (M : UniformTM) (n budget : Nat)
    (valueRail : Bool) (i : Fin (tapeLength n budget)) :
    DagCircuit (configWidth M n budget + actionWidth M + tapeLength n budget) :=
  substInputs muxCircuit ![
    inputProj (Fin.castAdd _ (oldActionInput M n budget (headIndex M n budget i))),
    inputProj (Fin.castAdd _ (actionInput M n budget
      (if valueRail then writeValueActionIndex M else writePresentActionIndex M))),
    inputProj (Fin.castAdd _ (oldActionInput M n budget
      (if valueRail then tapeValueIndex M n budget i else
        tapePresentIndex M n budget i)))]
@[simp] private theorem updateTapeCircuit_gates (M : UniformTM) (n budget : Nat)
    (valueRail : Bool) (i : Fin (tapeLength n budget)) :
    (updateTapeCircuit M n budget valueRail i).gates = 4 := rfl
private theorem updateTapeCircuit_eval (M : UniformTM) (n budget : Nat)
    (valueRail : Bool) (i : Fin (tapeLength n budget))
    (z : Bitstring (configWidth M n budget + actionWidth M + tapeLength n budget)) :
    eval (updateTapeCircuit M n budget valueRail i) z =
      if z (Fin.castAdd _ (oldActionInput M n budget (headIndex M n budget i))) then
        z (Fin.castAdd _ (actionInput M n budget
          (if valueRail then writeValueActionIndex M else writePresentActionIndex M)))
      else z (Fin.castAdd _ (oldActionInput M n budget
        (if valueRail then tapeValueIndex M n budget i else
          tapePresentIndex M n budget i))) := by
  simp [updateTapeCircuit]
private def rawUpdatePresentBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + actionWidth M + tapeLength n budget)
      (tapeLength n budget) :=
  bundleOfFamily _ (updateTapeCircuit M n budget false)
private def updatePresentStage (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + actionWidth M)
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget) :=
  substBundle (passthroughBundle (rawUpdatePresentBundle M n budget))
    (updateHeadStage M n budget)
private def updatePresentOutputIndex (M : UniformTM) (n budget : Nat)
    (i : Fin (tapeLength n budget)) : Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget) :=
  Fin.natAdd _ i
private def updateTapeValueCircuit (M : UniformTM) (n budget : Nat)
    (i : Fin (tapeLength n budget)) : DagCircuit
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget) :=
  relabelInputs (Fin.castAdd (tapeLength n budget))
    (updateTapeCircuit M n budget true i)
@[simp] private theorem updateTapeValueCircuit_gates (M : UniformTM)
    (n budget : Nat) (i : Fin (tapeLength n budget)) :
    (updateTapeValueCircuit M n budget i).gates = 4 := rfl
private def rawUpdateValueBundle (M : UniformTM) (n budget : Nat) : DagBundle
    (configWidth M n budget + actionWidth M + tapeLength n budget +
      tapeLength n budget) (tapeLength n budget) :=
  bundleOfFamily _ (updateTapeValueCircuit M n budget)
private def updateInternalBundle (M : UniformTM) (n budget : Nat) : DagBundle
    (configWidth M n budget + actionWidth M)
    (configWidth M n budget + actionWidth M + tapeLength n budget +
      tapeLength n budget + tapeLength n budget) :=
  substBundle (passthroughBundle (rawUpdateValueBundle M n budget))
    (updatePresentStage M n budget)
private def updateReindex (M : UniformTM) (n budget : Nat) :
    Fin (configWidth M n budget) → Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget + tapeLength n budget) :=
  blockDispatch M n budget
    (fun q => ⟨configWidth M n budget + (nextStateActionIndex M q).val, by
      have := (nextStateActionIndex M q).isLt; omega⟩)
    (fun i => ⟨configWidth M n budget + actionWidth M + i.val, by
      have := i.isLt; omega⟩)
    (fun i => ⟨configWidth M n budget + actionWidth M + tapeLength n budget + i.val,
      by have := i.isLt; omega⟩)
    (fun i => ⟨configWidth M n budget + actionWidth M + 2 * tapeLength n budget + i.val,
      by have := i.isLt; omega⟩)
/-- Update the state/head/tape layout from old configuration plus action rails.
The tape MUX selector is the old head rail. -/
def updateBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget + actionWidth M) (configWidth M n budget) :=
  reindexOutputs (updateInternalBundle M n budget) (updateReindex M n budget)
private def updateHeadMeaning (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) : Bool :=
  (selectedHeadPairs n budget i).any fun p =>
    y (oldActionInput M n budget (headIndex M n budget p.1)) &&
      y (actionInput M n budget (moveActionIndex M (indexedMove p.2)))
private theorem updateHeadStage_eval (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updateHeadStage M n budget).evalOutput (updateHeadOutputIndex M n budget i) y =
      updateHeadMeaning M n budget y i := by
  simp [updateHeadStage, updateHeadOutputIndex, rawUpdateHeadBundle,
    updateHeadCircuit, updateHeadMeaning, Function.comp_def]
private theorem updateHeadStage_input (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (configWidth M n budget + actionWidth M)) :
    (updateHeadStage M n budget).evalOutput (Fin.castAdd _ i) y = y i := by
  simp [updateHeadStage]
private theorem updatePresentStage_input (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (configWidth M n budget + actionWidth M)) :
    (updatePresentStage M n budget).evalOutput ⟨i.val, by
      have := i.isLt; omega⟩ y = y i := by
  rw [updatePresentStage, evalOutput_substBundle]
  rw [show (⟨i.val, by have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget)) = Fin.castAdd _ (Fin.castAdd _ i) by
          apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, updateHeadStage_input]
private theorem updatePresentStage_eval (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updatePresentStage M n budget).evalOutput
        (updatePresentOutputIndex M n budget i) y =
      if y (oldActionInput M n budget (headIndex M n budget i)) then
        y (actionInput M n budget (writePresentActionIndex M))
      else y (oldActionInput M n budget (tapePresentIndex M n budget i)) := by
  simp [updatePresentStage, updatePresentOutputIndex, rawUpdatePresentBundle,
    updateTapeCircuit, updateHeadStage_input]
private theorem updatePresentStage_head (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updatePresentStage M n budget).evalOutput
        ⟨configWidth M n budget + actionWidth M + i.val, by
          have := i.isLt; omega⟩ y = updateHeadMeaning M n budget y i := by
  rw [updatePresentStage, evalOutput_substBundle]
  rw [show (⟨configWidth M n budget + actionWidth M + i.val, by
      have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget)) = Fin.castAdd _ (updateHeadOutputIndex M n budget i) by
          apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, updateHeadStage_eval]
private theorem updateInternal_input (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (configWidth M n budget + actionWidth M)) :
    (updateInternalBundle M n budget).evalOutput ⟨i.val, by
      have := i.isLt; omega⟩ y = y i := by
  rw [updateInternalBundle, evalOutput_substBundle]
  rw [show (⟨i.val, by have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget + tapeLength n budget)) =
      Fin.castAdd _ ⟨i.val, by have := i.isLt; omega⟩ by apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, updatePresentStage_input]
private theorem updateInternal_head (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updateInternalBundle M n budget).evalOutput
        ⟨configWidth M n budget + actionWidth M + i.val, by
          have := i.isLt; omega⟩ y = updateHeadMeaning M n budget y i := by
  rw [updateInternalBundle, evalOutput_substBundle]
  rw [show (⟨configWidth M n budget + actionWidth M + i.val, by
      have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget + tapeLength n budget)) = Fin.castAdd _
      ⟨configWidth M n budget + actionWidth M + i.val, by
        have := i.isLt; omega⟩ by apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input]
  exact updatePresentStage_head M n budget y i
private theorem updateInternal_present (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updateInternalBundle M n budget).evalOutput
        ⟨configWidth M n budget + actionWidth M + tapeLength n budget + i.val,
          by have := i.isLt; omega⟩ y =
      if y (oldActionInput M n budget (headIndex M n budget i)) then
        y (actionInput M n budget (writePresentActionIndex M))
      else y (oldActionInput M n budget (tapePresentIndex M n budget i)) := by
  rw [updateInternalBundle, evalOutput_substBundle]
  rw [show (⟨configWidth M n budget + actionWidth M + tapeLength n budget + i.val,
      by have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget + tapeLength n budget)) = Fin.castAdd _
      (updatePresentOutputIndex M n budget i) by apply Fin.ext; rfl]
  rw [evalOutput_passthroughBundle_input, updatePresentStage_eval]
private theorem updateInternal_value (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updateInternalBundle M n budget).evalOutput
        ⟨configWidth M n budget + actionWidth M + 2 * tapeLength n budget + i.val,
          by have := i.isLt; omega⟩ y =
      if y (oldActionInput M n budget (headIndex M n budget i)) then
        y (actionInput M n budget (writeValueActionIndex M))
      else y (oldActionInput M n budget (tapeValueIndex M n budget i)) := by
  rw [updateInternalBundle, evalOutput_substBundle]
  rw [show (⟨configWidth M n budget + actionWidth M + 2 * tapeLength n budget + i.val,
      by have := i.isLt; omega⟩ : Fin
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget + tapeLength n budget)) = Fin.natAdd
      (configWidth M n budget + actionWidth M + tapeLength n budget +
        tapeLength n budget) i by apply Fin.ext; simp; omega]
  rw [evalOutput_passthroughBundle_output, rawUpdateValueBundle,
    evalOutput_bundleOfFamily, updateTapeValueCircuit, eval_relabelInputs,
    updateTapeCircuit_eval]
  have hhead := updatePresentStage_input M n budget y
    (oldActionInput M n budget (headIndex M n budget i))
  have hwrite := updatePresentStage_input M n budget y
    (actionInput M n budget (writeValueActionIndex M))
  have hold := updatePresentStage_input M n budget y
    (oldActionInput M n budget (tapeValueIndex M n budget i))
  simp only [ite_true]
  rw [show Fin.castAdd (tapeLength n budget) (Fin.castAdd (tapeLength n budget)
      (oldActionInput M n budget (headIndex M n budget i))) =
      ⟨(oldActionInput M n budget (headIndex M n budget i)).val, by
        have := (oldActionInput M n budget (headIndex M n budget i)).isLt
        omega⟩ by apply Fin.ext; rfl]
  rw [hhead]
  rw [show Fin.castAdd (tapeLength n budget) (Fin.castAdd (tapeLength n budget)
      (actionInput M n budget (writeValueActionIndex M))) =
      ⟨(actionInput M n budget (writeValueActionIndex M)).val, by
        have := (actionInput M n budget (writeValueActionIndex M)).isLt
        omega⟩ by apply Fin.ext; rfl]
  rw [hwrite]
  rw [show Fin.castAdd (tapeLength n budget) (Fin.castAdd (tapeLength n budget)
      (oldActionInput M n budget (tapeValueIndex M n budget i))) =
      ⟨(oldActionInput M n budget (tapeValueIndex M n budget i)).val, by
        have := (oldActionInput M n budget (tapeValueIndex M n budget i)).isLt
        omega⟩ by apply Fin.ext; rfl]
  rw [hold]
private theorem updateBundle_state (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M)) (q : Fin M.stateCount) :
    (updateBundle M n budget).evalOutput (stateIndex M n budget q) y =
      y (actionInput M n budget (nextStateActionIndex M q)) := by
  rw [updateBundle, evalOutput_reindexOutputs]
  simp only [updateReindex, blockDispatch_state]
  convert updateInternal_input M n budget y
    (actionInput M n budget (nextStateActionIndex M q)) using 1
private theorem updateBundle_head (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updateBundle M n budget).evalOutput (headIndex M n budget i) y =
      updateHeadMeaning M n budget y i := by
  simp [updateBundle, updateReindex, updateInternal_head]
private theorem updateBundle_present (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updateBundle M n budget).evalOutput (tapePresentIndex M n budget i) y =
      if y (oldActionInput M n budget (headIndex M n budget i)) then
        y (actionInput M n budget (writePresentActionIndex M))
      else y (oldActionInput M n budget (tapePresentIndex M n budget i)) := by
  simp [updateBundle, updateReindex, updateInternal_present]
private theorem updateBundle_value (M : UniformTM) (n budget : Nat)
    (y : Bitstring (configWidth M n budget + actionWidth M))
    (i : Fin (tapeLength n budget)) :
    (updateBundle M n budget).evalOutput (tapeValueIndex M n budget i) y =
      if y (oldActionInput M n budget (headIndex M n budget i)) then
        y (actionInput M n budget (writeValueActionIndex M))
      else y (oldActionInput M n budget (tapeValueIndex M n budget i)) := by
  simp [updateBundle, updateReindex, updateInternal_value]
private theorem headPairs_length (n budget : Nat) :
    (headPairs n budget).length = tapeLength n budget * 3 := by
  simp [headPairs]
private theorem selectedHeadPairs_sum (n budget : Nat) :
    (∑ i : Fin (tapeLength n budget), (selectedHeadPairs n budget i).length) =
      tapeLength n budget * 3 := by
  simpa [selectedHeadPairs, headPairs_length] using
    sum_filter_length_eq (headPairs n budget)
      (fun p => moveHead p.1 (indexedMove p.2))
private theorem rawUpdateHeadBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawUpdateHeadBundle M n budget).gates = 7 * tapeLength n budget := by
  rw [rawUpdateHeadBundle, bundleOfFamily_gates]
  simp only [updateHeadCircuit, bigOrCircuit_gates, List.map_map]
  simp [Function.comp_def]
  rw [show (∑ x : Fin (tapeLength n budget),
      (1 + (selectedHeadPairs n budget x).length * 2)) =
      (∑ _x : Fin (tapeLength n budget), 1) +
        (∑ x : Fin (tapeLength n budget),
          (selectedHeadPairs n budget x).length) * 2 by
            rw [Finset.sum_add_distrib, Finset.sum_mul]]
  rw [selectedHeadPairs_sum]
  simp
  omega
private theorem rawUpdatePresentBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawUpdatePresentBundle M n budget).gates = 4 * tapeLength n budget := by
  rw [rawUpdatePresentBundle, bundleOfFamily_gates]
  simp
  omega
private theorem rawUpdateValueBundle_gates (M : UniformTM) (n budget : Nat) :
    (rawUpdateValueBundle M n budget).gates = 4 * tapeLength n budget := by
  rw [rawUpdateValueBundle, bundleOfFamily_gates]
  simp
  omega
@[simp] theorem updateBundle_gates (M : UniformTM) (n budget : Nat) :
    (updateBundle M n budget).gates = 15 * tapeLength n budget := by
  simp [updateBundle, updateInternalBundle, updatePresentStage, updateHeadStage,
    rawUpdateHeadBundle_gates, rawUpdatePresentBundle_gates,
    rawUpdateValueBundle_gates]
  omega
/-- The concrete one-step bundle: the update graph is layered once over the
single shared action graph. -/
def stepBundle (M : UniformTM) (n budget : Nat) :
    DagBundle (configWidth M n budget) (configWidth M n budget) :=
  substBundle (updateBundle M n budget) (actionBundle M n budget)
private theorem any_finRange_selected {k : Nat} (chosen : Fin k)
    (f : Fin k → Bool) :
    (List.finRange k).any (fun i => decide (i = chosen) && f i) = f chosen := by
  apply Bool.eq_iff_iff.mpr
  simp
private theorem updateHeadMeaning_encode (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    updateHeadMeaning M n budget
      ((actionBundle M n budget).evalFun (encodeConfig M c)) i =
      decide (i = moveHead c.head (M.step c.state (c.tape c.head)).2.2) := by
  rw [actionBundle_eval_encodeConfig]
  simp only [updateHeadMeaning, selectedHeadPairs, any_filter_eq]
  simp only [oldActionInput, actionInput, Fin.addCases_left, Fin.addCases_right,
    encodeConfig_head]
  simp only [actionPredicate_moveActionIndex]
  rw [show (headPairs n budget).any (fun p =>
      (decide (p.1 = c.head) &&
        decide (indexedMove p.2 = (M.step c.state (c.tape c.head)).2.2)) &&
      decide (i = moveHead p.1 (indexedMove p.2))) = _ by
        rfl]
  simp only [headPairs, List.any_flatMap, List.any_map]
  have hinner (old : Fin (tapeLength n budget)) :
      (List.finRange 3).any (fun m =>
        (decide (old = c.head) &&
          decide (indexedMove m = (M.step c.state (c.tape c.head)).2.2)) &&
            decide (i = moveHead old (indexedMove m))) =
        (decide (old = c.head) &&
          decide (i = moveHead old (M.step c.state (c.tape c.head)).2.2)) := by
    rw [finRange_three_any]
    cases hm : (M.step c.state (c.tape c.head)).2.2 <;> simp [indexedMove]
  simp only [Function.comp_def]
  simp_rw [hinner]
  rw [any_finRange_selected]
/-- Canonical evaluation is exactly the pure encoded semantic step. -/
theorem stepBundle_eval_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    (stepBundle M n budget).evalFun (encodeConfig M c) =
      encodedStep M n budget (encodeConfig M c) := by
  funext o
  rw [DagBundle.evalFun_apply, stepBundle, evalOutput_substBundle]
  rcases configIndex_cover M n budget o with
    ⟨q, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [updateBundle_state]
    simp [actionInput, encodedStep]
  · rw [updateBundle_head]
    change updateHeadMeaning M n budget
      ((actionBundle M n budget).evalFun (encodeConfig M c)) i = _
    rw [updateHeadMeaning_encode]
    simp [encodedStep]
  · rw [updateBundle_present]
    simp [oldActionInput, actionInput, encodedStep, nextPresent]
  · rw [updateBundle_value]
    simp [oldActionInput, actionInput, encodedStep, nextValue]
/-- The direct shared bundle satisfies the semantic one-step contract. -/
theorem stepBundle_spec (M : UniformTM) (n budget : Nat) :
    StepSpec M (stepBundle M n budget) := by
  intro c
  rw [stepBundle_eval_encodeConfig, encodedStep_encodeConfig]
/-- Exact sum of the action and update stages. -/
theorem stepBundle_gates (M : UniformTM) (n budget : Nat) :
    (stepBundle M n budget).gates =
      19 * tapeLength n budget + 10 * M.stateCount + 12 +
        actionSupportCount M (fun a => symbolPresent a.2.1) +
        actionSupportCount M (fun a => symbolValue a.2.1) := by
  simp [stepBundle, actionBundle_gates]
  omega
/-- Coarse explicit per-step gate cap used by later polynomial domination. -/
theorem stepBundle_gates_le (M : UniformTM) (n budget : Nat) :
    (stepBundle M n budget).gates ≤
      19 * tapeLength n budget + 16 * M.stateCount + 13 := by
  rw [stepBundle, substBundle_gates]
  have h := actionBundle_gates_le M n budget
  rw [updateBundle_gates]
  omega
end Pnp3.Complexity.Uniform.V1.Circuit
