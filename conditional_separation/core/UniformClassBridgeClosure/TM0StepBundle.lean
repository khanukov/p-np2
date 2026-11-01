import UniformClassBridgeClosure.TM0Window
import Complexity.DagGadgets

/-! Executable radius-one to radius-zero compiler. One-hot LOCAL tuples, not
an assumed whole-window encoding or a polynomial-time run simulation. -/
namespace UniformClassBridgeClosure.TM0DAG
open Turing Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit

def symbols : List Symbol :=
  [(false, none), (false, some false), (false, some true),
   (true, none), (true, some false), (true, some true)]
def locals {Λ : Type} (labels : List Λ) : List (Local Λ) :=
  [false, true].product (labels.product (symbols.product (symbols.product symbols)))
def centers {Λ : Type} (labels : List Λ) : List (Center Λ) :=
  [false, true].product (labels.product symbols)
private theorem symbols_complete (a : Symbol) : a ∈ symbols := by
  rcases a with ⟨b, a⟩; cases b <;> cases a with
  | none => decide
  | some a => cases a <;> decide
private theorem locals_complete {Λ : Type} (labels : List Λ)
    (complete : ∀ q, q ∈ labels) (a : Local Λ) : a ∈ locals labels := by
  rcases a with ⟨h,q,l,c,r⟩
  simp [locals, complete, symbols_complete]
private def oneHot {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    Bitstring xs.length := fun i => decide (xs[i] = a)
private def row {α β : Type} [DecidableEq β] (xs : List α) (f : α → β)
    (b : β) : DagCircuit xs.length :=
  bigOrCircuit ((List.finRange xs.length).map fun i =>
    if f xs[i] = b then inputProj i else constCircuit _ false)
private theorem row_correct {α β : Type} [DecidableEq α] [DecidableEq β]
    (xs : List α) (f : α → β) (a : α) (ha : a ∈ xs) (b : β) :
    eval (row xs f b) (oneHot xs a) = decide (f a = b) := by
  obtain ⟨i, hi, ei⟩ := List.getElem_of_mem ha
  apply Bool.eq_iff_iff.mpr
  simp only [row, eval_bigOrCircuit_map, List.any_eq_true, List.mem_finRange,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    split at hj
    · simp only [eval_inputProj, oneHot, decide_eq_true_eq] at hj
      simpa [hj] using ‹f xs[j] = b›
    · simp at hj
  · intro h
    refine ⟨⟨i,hi⟩, ?_⟩
    simp [ei, h, oneHot]
private theorem row_gates {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → β) (b : β) :
    (row xs f b).gates ≤ 1 + 2 * xs.length := by
  rw [row, bigOrCircuit_gates, List.map_map]
  have aux : ∀ is : List (Fin xs.length),
      (is.map (fun i => (if f xs[i] = b then inputProj i else constCircuit _ false).gates + 1)).sum
        ≤ 2 * is.length := by
    intro is; induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      split
      · have hg : (inputProj i).gates = 0 := rfl
        rw [hg]; omega
      · have hg : (constCircuit xs.length false).gates = 1 := rfl
        rw [hg]; omega
  have h := aux (List.finRange xs.length)
  simpa only [List.length_finRange, Function.comp_def] using Nat.add_le_add_left h 1

def encodeLocal {Λ : Type} [DecidableEq Λ] (labels : List Λ) (a : Local Λ) :
    Bitstring (locals labels).length := fun i =>
  let x := (locals labels)[i]
  decide (x.1 = a.1) && decide (x.2.1 = a.2.1) &&
    decide (x.2.2.1 = a.2.2.1) && decide (x.2.2.2.1 = a.2.2.2.1) &&
    decide (x.2.2.2.2 = a.2.2.2.2)

def encodeCenter {Λ : Type} [DecidableEq Λ] (labels : List Λ) (a : Center Λ) :
    Bitstring (centers labels).length := oneHot (centers labels) a

def stepBundle {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) :
    DagBundle (locals labels).length (centers labels).length :=
  bundleOfFamily _ (fun o => row (locals labels) (localStep T) (centers labels)[o])

theorem step_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (s : Bool × TM0.Cfg Symbol Λ) (o : Fin (centers labels).length) :
    (stepBundle labels T).evalOutput o (encodeLocal labels (observe s)) =
      encodeCenter labels (center (saturatedStep T s)) o := by
  letI : DecidableEq (Local Λ) := Classical.decEq _
  have enc (a : Local Λ) : encodeLocal labels a = oneHot (locals labels) a := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp [encodeLocal, oneHot, Prod.ext_iff, Bool.and_eq_true, and_assoc]
  rw [enc, stepBundle, evalOutput_bundleOfFamily,
    row_correct _ _ _ (locals_complete labels complete (observe s))]
  simp only [encodeCenter, oneHot, localStep_correct]
  simp only [eq_comm]

theorem check_step_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels)
    (T : TM0.Machine (Bool × Option Bool) Λ)
    (s : Bool × TM0.Cfg (Bool × Option Bool) Λ) (o : Fin (centers labels).length) :
    (stepBundle labels T).evalOutput o (encodeLocal labels (observe s)) =
      encodeCenter labels (center (saturatedStep T s)) o := step_correct labels complete T s o

private theorem product_length {α β : Type} (xs : List α) (ys : List β) :
    (xs.product ys).length = xs.length * ys.length := by
  change (xs ×ˢ ys).length = _
  exact List.length_product xs ys

theorem step_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) :
    (stepBundle labels T).gates ≤ 12 * labels.length * (1 + 864 * labels.length) := by
  rw [stepBundle, bundleOfFamily_gates]
  calc
    _ ≤ ∑ _ : Fin (centers labels).length, (1 + 2 * (locals labels).length) :=
      Finset.sum_le_sum (fun _ _ => row_gates _ _ _)
    _ = _ := by simp [centers, locals, symbols, product_length]; ring

theorem check_step_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine (Bool × Option Bool) Λ) :
    (stepBundle labels T).gates ≤ 12 * labels.length * (1 + 864 * labels.length) :=
  step_gates labels T

#check (symbols : List (Bool × Option Bool))
#check (@locals : {Λ : Type} → List Λ → List (Bool × Λ × Symbol × Symbol × Symbol))
#check (@centers : {Λ : Type} → List Λ → List (Bool × Λ × Symbol))
#check (@encodeLocal : {Λ : Type} → [DecidableEq Λ] → (labels : List Λ) →
  Local Λ → Bitstring (locals labels).length)
#check (@encodeCenter : {Λ : Type} → [DecidableEq Λ] → (labels : List Λ) →
  Center Λ → Bitstring (centers labels).length)
#check (@stepBundle : {Λ : Type} → [Inhabited Λ] → [DecidableEq Λ] →
  (labels : List Λ) → TM0.Machine Symbol Λ →
  DagBundle (locals labels).length (centers labels).length)
#print axioms symbols
#print axioms locals
#print axioms centers
#print axioms symbols_complete
#print axioms locals_complete
#print axioms oneHot
#print axioms row
#print axioms row_correct
#print axioms row_gates
#print axioms encodeLocal
#print axioms encodeCenter
#print axioms stepBundle
#print axioms step_correct
#print axioms check_step_correct
#print axioms product_length
#print axioms step_gates
#print axioms check_step_gates
-- SG2_LITERAL_TYPE_PINS: mechanical elaboration checks, not independent reproof.
#check (@oneHot : {α : Type} → [DecidableEq α] → (xs : List α) → α → Bitstring xs.length)
#check (@row : {α β : Type} → [DecidableEq β] → (xs : List α) → (α → β) → β → DagCircuit xs.length)
#check (@step_correct : ∀ {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (_complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (s : Bool × TM0.Cfg Symbol Λ) (o : Fin (centers labels).length),
    (stepBundle labels T).evalOutput o (encodeLocal labels (observe s)) =
      encodeCenter labels (center (saturatedStep T s)) o)
#check (@check_step_correct : ∀ {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (_complete : ∀ q, q ∈ labels)
    (T : TM0.Machine (Bool × Option Bool) Λ)
    (s : Bool × TM0.Cfg (Bool × Option Bool) Λ) (o : Fin (centers labels).length),
    (stepBundle labels T).evalOutput o (encodeLocal labels (observe s)) =
      encodeCenter labels (center (saturatedStep T s)) o)
#check (@step_gates : ∀ {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ),
    (stepBundle labels T).gates ≤ 12 * labels.length * (1 + 864 * labels.length))
#check (@check_step_gates : ∀ {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine (Bool × Option Bool) Λ),
    (stepBundle labels T).gates ≤ 12 * labels.length * (1 + 864 * labels.length))

end UniformClassBridgeClosure.TM0DAG
