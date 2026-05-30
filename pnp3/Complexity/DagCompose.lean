import Complexity.Interfaces
import Mathlib.Tactic

/-!
# DAG-circuit composition library (for the decision→search extraction)

Circuit-composition infrastructure that the pnp4 decision→search *extraction
theorem* needs and that the repository previously lacked (the `DagCircuit` API
had only `eval`, `size`, `support`).

Composition layer — micro-step progress (one reusable primitive per commit):

* step 0 — leaf primitives `inputProj`, `constCircuit` (+ eval/size);  ✓
* step 1 — `relabelInputs` (input reindexing) with eval/size correctness;  ✓
* step 2 — index transport `weakenWireRight`/`shiftWireBy` (+ gate versions):
  the `Fin` arithmetic needed to concatenate gate lists;  ← this commit
* step 3 — `appendCircuit` / multi-output `DagBundle`;
* step 4 — `substInputs` (input substitution) with eval/size lemmas.

Downstream (separate files): greedy `BoundedSearchSolver` assembly →
`PpolyDAG (PrefixExtensionLanguage) → BoundedSearchSolver` and its
contrapositive → replace the abstract `SearchMCSPMagnificationContract` field
(closes the audit hole flagged by the D0 review).

This file introduces **no** endpoint, source theorem, `PpolyDAG` bridge, or
`P ≠ NP` consequence; it is pure circuit plumbing.  The lower bound itself
(`¬BoundedSearchSolver`) is *not* addressed here and remains the open problem.
-/

namespace Pnp3
namespace ComplexityInterfaces
namespace DagCircuit

/-- The projection circuit: zero gates, output is input wire `j`. -/
def inputProj {n : Nat} (j : Fin n) : DagCircuit n where
  gates := 0
  gate := fun i => absurd i.2 (Nat.not_lt_zero i.1)
  output := DagWire.input j

@[simp] theorem eval_inputProj {n : Nat} (j : Fin n) (x : Bitstring n) :
    eval (inputProj j) x = x j := rfl

@[simp] theorem size_inputProj {n : Nat} (j : Fin n) :
    size (inputProj j) = 1 := rfl

/-- The constant circuit: one `const b` gate, output is that gate. -/
def constCircuit (n : Nat) (b : Bool) : DagCircuit n where
  gates := 1
  gate := fun _ => DagGate.const b
  output := DagWire.gate ⟨0, Nat.zero_lt_one⟩

@[simp] theorem eval_constCircuit {n : Nat} (b : Bool) (x : Bitstring n) :
    eval (constCircuit n b) x = b := by
  unfold eval
  unfold DagCircuit.eval.evalGateAt
  rfl

@[simp] theorem size_constCircuit (n : Nat) (b : Bool) :
    size (constCircuit n b) = 2 := rfl

/-! ### Composition layer, step 1: input relabelling

`relabelInputs ρ C` reindexes the input wires of `C` by `ρ : Fin n → Fin m`
without touching the gate graph (same gates, same gate references).  This is the
smallest genuine composition primitive: it provides projection/field wiring for
later substitution, and its `eval` lemma is the first `evalGateAt`-induction of
the library (modelled on `evalGateAt_eq_of_eq_on_supportAt`).
-/

/-- Remap the input wires of a wire by `ρ` (gate references unchanged). -/
def mapWireInputs {n m k : Nat} (ρ : Fin n → Fin m) : DagWire n k → DagWire m k
  | .input j => .input (ρ j)
  | .gate g => .gate g

/-- Remap the input wires occurring in a gate by `ρ`. -/
def mapGateInputs {n m k : Nat} (ρ : Fin n → Fin m) : DagGate n k → DagGate m k
  | .const b => .const b
  | .not w => .not (mapWireInputs ρ w)
  | .and w₁ w₂ => .and (mapWireInputs ρ w₁) (mapWireInputs ρ w₂)
  | .or w₁ w₂ => .or (mapWireInputs ρ w₁) (mapWireInputs ρ w₂)

/-- Relabel the inputs of `C` by `ρ`, keeping the gate graph fixed. -/
def relabelInputs {n m : Nat} (ρ : Fin n → Fin m) (C : DagCircuit n) :
    DagCircuit m where
  gates := C.gates
  gate := fun i => mapGateInputs ρ (C.gate i)
  output := mapWireInputs ρ C.output

@[simp] theorem size_relabelInputs {n m : Nat} (ρ : Fin n → Fin m) (C : DagCircuit n) :
    size (relabelInputs ρ C) = size C := rfl

/-- Gate-level evaluation is preserved by input relabelling: evaluating the
relabelled gate at `x` equals evaluating the original gate at `x ∘ ρ`. -/
theorem evalGateAt_relabelInputs {n m : Nat} (ρ : Fin n → Fin m) (C : DagCircuit n) :
    ∀ {i : Nat} (hi : i < C.gates) (x : Bitstring m),
      DagCircuit.eval.evalGateAt (C := relabelInputs ρ C) (x := x) i hi =
        DagCircuit.eval.evalGateAt (C := C) (x := fun j => x (ρ j)) i hi
  | i, hi, x => by
      have hgate : (relabelInputs ρ C).gate ⟨i, hi⟩
            = mapGateInputs ρ (C.gate ⟨i, hi⟩) := rfl
      cases hOp : C.gate ⟨i, hi⟩ with
      | const b =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
          rw [hgate, hOp]
          rfl
      | not w =>
          cases w with
          | input j =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
              rw [hgate, hOp]
              rfl
          | gate j =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
              rw [hgate, hOp]
              simp only [mapGateInputs, mapWireInputs]
              rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j.2 hi) x]
      | and w₁ w₂ =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
          rw [hgate, hOp]
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ => rfl
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x]
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x,
                      evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
      | or w₁ w₂ =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
          rw [hgate, hOp]
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ => rfl
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x]
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x,
                      evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
  termination_by i => i

/-- **Input-relabelling correctness.**  Evaluating `relabelInputs ρ C` at `x`
equals evaluating `C` at the relabelled input `fun j => x (ρ j)`. -/
@[simp] theorem eval_relabelInputs {n m : Nat} (ρ : Fin n → Fin m)
    (C : DagCircuit n) (x : Bitstring m) :
    eval (relabelInputs ρ C) x = eval C (fun j => x (ρ j)) := by
  unfold eval
  cases hout : C.output with
  | input j =>
      simp [relabelInputs, mapWireInputs, hout]
  | gate g =>
      have h : (relabelInputs ρ C).output = DagWire.gate g := by
        simp [relabelInputs, mapWireInputs, hout]
      rw [h]
      exact evalGateAt_relabelInputs ρ C g.2 x

/-! ### Composition layer, step 2: index transport

Two distinct `Fin`-index shifts on wires/gates, kept deliberately separate to
avoid `k + extra` vs `offset + k` arithmetic fights in `append`/`substInputs`:

* `weakenWireRight extra` embeds `Fin k ↪ Fin (k + extra)` (via `Fin.castAdd`) —
  keeps the *first* circuit's gate references valid after appending `extra`
  gates on the right;
* `shiftWireBy offset` embeds `Fin k ↪ Fin (offset + k)` (via `Fin.natAdd`) —
  moves the *second* circuit's local gate references to their global positions.

These are purely index transport: wires/gates have no standalone `eval`, so the
semantic lemmas appear later, with `append`/`substInputs`.
-/

/-- Keep a wire valid after `extra` gates are appended on the right. -/
def weakenWireRight {n k : Nat} (extra : Nat) : DagWire n k → DagWire n (k + extra)
  | .input j => .input j
  | .gate g => .gate (Fin.castAdd extra g)

@[simp] theorem weakenWireRight_input {n k : Nat} (extra : Nat) (j : Fin n) :
    weakenWireRight (n := n) (k := k) extra (DagWire.input j) = DagWire.input j := rfl

@[simp] theorem weakenWireRight_gate {n k : Nat} (extra : Nat) (g : Fin k) :
    weakenWireRight (n := n) extra (DagWire.gate g) = DagWire.gate (Fin.castAdd extra g) := rfl

/-- Shift a wire's gate reference by `offset` (the second circuit in `append`). -/
def shiftWireBy {n k : Nat} (offset : Nat) : DagWire n k → DagWire n (offset + k)
  | .input j => .input j
  | .gate g => .gate (Fin.natAdd offset g)

@[simp] theorem shiftWireBy_input {n k : Nat} (offset : Nat) (j : Fin n) :
    shiftWireBy (n := n) (k := k) offset (DagWire.input j) = DagWire.input j := rfl

@[simp] theorem shiftWireBy_gate {n k : Nat} (offset : Nat) (g : Fin k) :
    shiftWireBy (n := n) offset (DagWire.gate g) = DagWire.gate (Fin.natAdd offset g) := rfl

/-- Gate version of `weakenWireRight`. -/
def weakenGateRight {n k : Nat} (extra : Nat) : DagGate n k → DagGate n (k + extra)
  | .const b => .const b
  | .not w => .not (weakenWireRight extra w)
  | .and w₁ w₂ => .and (weakenWireRight extra w₁) (weakenWireRight extra w₂)
  | .or w₁ w₂ => .or (weakenWireRight extra w₁) (weakenWireRight extra w₂)

/-- Gate version of `shiftWireBy`. -/
def shiftGateBy {n k : Nat} (offset : Nat) : DagGate n k → DagGate n (offset + k)
  | .const b => .const b
  | .not w => .not (shiftWireBy offset w)
  | .and w₁ w₂ => .and (shiftWireBy offset w₁) (shiftWireBy offset w₂)
  | .or w₁ w₂ => .or (shiftWireBy offset w₁) (shiftWireBy offset w₂)

@[simp] theorem weakenGateRight_const {n k : Nat} (extra : Nat) (b : Bool) :
    weakenGateRight (n := n) (k := k) extra (DagGate.const b) = DagGate.const b := rfl

@[simp] theorem shiftGateBy_const {n k : Nat} (offset : Nat) (b : Bool) :
    shiftGateBy (n := n) (k := k) offset (DagGate.const b) = DagGate.const b := rfl

@[simp] theorem weakenGateRight_not {n k : Nat} (extra : Nat) (w : DagWire n k) :
    weakenGateRight extra (DagGate.not w) = DagGate.not (weakenWireRight extra w) := rfl

@[simp] theorem weakenGateRight_and {n k : Nat} (extra : Nat) (w₁ w₂ : DagWire n k) :
    weakenGateRight extra (DagGate.and w₁ w₂)
      = DagGate.and (weakenWireRight extra w₁) (weakenWireRight extra w₂) := rfl

@[simp] theorem weakenGateRight_or {n k : Nat} (extra : Nat) (w₁ w₂ : DagWire n k) :
    weakenGateRight extra (DagGate.or w₁ w₂)
      = DagGate.or (weakenWireRight extra w₁) (weakenWireRight extra w₂) := rfl

@[simp] theorem shiftGateBy_not {n k : Nat} (offset : Nat) (w : DagWire n k) :
    shiftGateBy offset (DagGate.not w) = DagGate.not (shiftWireBy offset w) := rfl

@[simp] theorem shiftGateBy_and {n k : Nat} (offset : Nat) (w₁ w₂ : DagWire n k) :
    shiftGateBy offset (DagGate.and w₁ w₂)
      = DagGate.and (shiftWireBy offset w₁) (shiftWireBy offset w₂) := rfl

@[simp] theorem shiftGateBy_or {n k : Nat} (offset : Nat) (w₁ w₂ : DagWire n k) :
    shiftGateBy offset (DagGate.or w₁ w₂)
      = DagGate.or (shiftWireBy offset w₁) (shiftWireBy offset w₂) := rfl

/-! ### Composition layer, step 3: single-output append (definitions + size)

`appendOutputLeft`/`appendOutputRight C₁ C₂` concatenate the gate lists of `C₁`
and `C₂` (`C₁.gates + C₂.gates` gates) and select, respectively, `C₁`'s or `C₂`'s
output.  Given the dependent-indexed representation, `C₁`'s gates keep their
positions/references unchanged (no transport); only `C₂`'s gates are shifted by
`C₁.gates` (`shiftGateBy`).  `C₁`'s output wire is weakened into the larger
index space (`weakenWireRight`); `C₂`'s output wire is shifted (`shiftWireBy`).

The shared gate function is defined with `Fin.addCases`, avoiding manual
dependent casts.  This commit is definitions + size only; the `eval`-preservation
lemmas (the genuine `evalGateAt`-induction with index splitting) follow next.
-/

/-- Shared concatenated gate function for the append of `C₁` and `C₂`:
left positions reuse `C₁`'s gates as-is; right positions use `C₂`'s gates with
references shifted by `C₁.gates`. -/
def appendGate {n : Nat} (C₁ C₂ : DagCircuit n)
    (i : Fin (C₁.gates + C₂.gates)) : DagGate n i.1 :=
  Fin.addCases (motive := fun i => DagGate n i.1)
    (fun p => C₁.gate p)
    (fun j => shiftGateBy C₁.gates (C₂.gate j))
    i

/-- Append `C₂`'s gates after `C₁`'s, keeping `C₁`'s output. -/
def appendOutputLeft {n : Nat} (C₁ C₂ : DagCircuit n) : DagCircuit n where
  gates := C₁.gates + C₂.gates
  gate := appendGate C₁ C₂
  output := weakenWireRight C₂.gates C₁.output

/-- Append `C₂`'s gates after `C₁`'s, keeping `C₂`'s (shifted) output. -/
def appendOutputRight {n : Nat} (C₁ C₂ : DagCircuit n) : DagCircuit n where
  gates := C₁.gates + C₂.gates
  gate := appendGate C₁ C₂
  output := shiftWireBy C₁.gates C₂.output

@[simp] theorem size_appendOutputLeft {n : Nat} (C₁ C₂ : DagCircuit n) :
    size (appendOutputLeft C₁ C₂) = C₁.gates + C₂.gates + 1 := rfl

@[simp] theorem size_appendOutputRight {n : Nat} (C₁ C₂ : DagCircuit n) :
    size (appendOutputRight C₁ C₂) = C₁.gates + C₂.gates + 1 := rfl

theorem size_appendOutputLeft_le {n : Nat} (C₁ C₂ : DagCircuit n) :
    size (appendOutputLeft C₁ C₂) ≤ size C₁ + size C₂ := by
  rw [size_appendOutputLeft]; simp only [size]; omega

theorem size_appendOutputRight_le {n : Nat} (C₁ C₂ : DagCircuit n) :
    size (appendOutputRight C₁ C₂) ≤ size C₁ + size C₂ := by
  rw [size_appendOutputRight]; simp only [size]; omega

/-- On a left (`castAdd`) position the append reuses `C₁`'s gate unchanged. -/
@[simp] theorem appendGate_left {n : Nat} (C₁ C₂ : DagCircuit n) (p : Fin C₁.gates) :
    appendGate C₁ C₂ (Fin.castAdd C₂.gates p) = C₁.gate p := by
  unfold appendGate
  rw [Fin.addCases_left]

/-- On a right (`natAdd`) position the append uses `C₂`'s gate shifted by `C₁.gates`. -/
@[simp] theorem appendGate_right {n : Nat} (C₁ C₂ : DagCircuit n) (j : Fin C₂.gates) :
    appendGate C₁ C₂ (Fin.natAdd C₁.gates j) = shiftGateBy C₁.gates (C₂.gate j) := by
  unfold appendGate
  rw [Fin.addCases_right]

/-! ### Composition layer, step 3b: append eval-preservation

Gate-level agreement on the left part (positions `< C₁.gates`): the append
evaluates exactly like `C₁`.  The lemma takes *both* the append-side bound
`hiA` and the local `C₁`-bound `hi₁`, and aligns the `Fin` index by
`Fin.ext rfl` before `appendGate_left` — this avoids dependent-cast/proof-
irrelevance pain.  Same `evalGateAt`-induction shape as `evalGateAt_relabelInputs`.
-/
theorem evalGateAt_append_left {n : Nat} (C₁ C₂ : DagCircuit n) :
    ∀ {i : Nat} (hiA : i < (appendOutputLeft C₁ C₂).gates) (hi₁ : i < C₁.gates)
      (x : Bitstring n),
      DagCircuit.eval.evalGateAt (C := appendOutputLeft C₁ C₂) (x := x) i hiA =
        DagCircuit.eval.evalGateAt (C := C₁) (x := x) i hi₁
  | i, hiA, hi₁, x => by
      -- `Fin.castAdd C₂.gates ⟨i, hi₁⟩` and `⟨i, hiA⟩` are defeq (same `.val`,
      -- proof-irrelevant bound), so `appendGate_left` applies directly.
      have hgate : (appendOutputLeft C₁ C₂).gate ⟨i, hiA⟩ = C₁.gate ⟨i, hi₁⟩ :=
        appendGate_left C₁ C₂ ⟨i, hi₁⟩
      cases hOp : C₁.gate ⟨i, hi₁⟩ with
      | const b =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
          simp only [hOp]
      | not w =>
          cases w with
          | input j =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
              simp only [hOp]
          | gate g =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
              simp only [hOp]
              rw [evalGateAt_append_left C₁ C₂ (Nat.lt_trans g.2 hiA) (Nat.lt_trans g.2 hi₁) x]
      | and w₁ w₂ =>
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
                  rw [evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₂.2 hiA) (Nat.lt_trans j₂.2 hi₁) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
                  rw [evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₁.2 hiA) (Nat.lt_trans j₁.2 hi₁) x]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
                  rw [evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₁.2 hiA) (Nat.lt_trans j₁.2 hi₁) x,
                      evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₂.2 hiA) (Nat.lt_trans j₂.2 hi₁) x]
      | or w₁ w₂ =>
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
                  rw [evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₂.2 hiA) (Nat.lt_trans j₂.2 hi₁) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
                  rw [evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₁.2 hiA) (Nat.lt_trans j₁.2 hi₁) x]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp]
                  rw [evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₁.2 hiA) (Nat.lt_trans j₁.2 hi₁) x,
                      evalGateAt_append_left C₁ C₂ (Nat.lt_trans j₂.2 hiA) (Nat.lt_trans j₂.2 hi₁) x]
  termination_by i => i

/-- Gate-level agreement on the right part (positions `C₁.gates + j`): the append
evaluates like `C₂`, with `C₂`'s gate references shifted by `C₁.gates`.  Heavier
than the left version: a sub-gate `g : Fin j` of `C₂` becomes the global index
`C₁.gates + g.1`, so the recursive call sits at `C₁.gates + g.1`. -/
theorem evalGateAt_append_right {n : Nat} (C₁ C₂ : DagCircuit n) :
    ∀ {j : Nat} (hjA : C₁.gates + j < (appendOutputRight C₁ C₂).gates) (hj₂ : j < C₂.gates)
      (x : Bitstring n),
      DagCircuit.eval.evalGateAt (C := appendOutputRight C₁ C₂) (x := x) (C₁.gates + j) hjA =
        DagCircuit.eval.evalGateAt (C := C₂) (x := x) j hj₂
  | j, hjA, hj₂, x => by
      have hgate : (appendOutputRight C₁ C₂).gate ⟨C₁.gates + j, hjA⟩
            = shiftGateBy C₁.gates (C₂.gate ⟨j, hj₂⟩) :=
        appendGate_right C₁ C₂ ⟨j, hj₂⟩
      cases hOp : C₂.gate ⟨j, hj₂⟩ with
      | const b =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
          simp only [hOp, shiftGateBy_const]
      | not w =>
          cases w with
          | input jj =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
              simp only [hOp, shiftGateBy_not, shiftWireBy_input]
          | gate g =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
              simp only [hOp, shiftGateBy_not, shiftWireBy_gate, Fin.coe_natAdd]
              rw [evalGateAt_append_right C₁ C₂
                    (Nat.add_lt_add_left (Nat.lt_trans g.2 hj₂) C₁.gates)
                    (Nat.lt_trans g.2 hj₂) x]
      | and w₁ w₂ =>
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_input]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₂.2 hj₂) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₁.2 hj₂) x]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₁.2 hj₂) x,
                      evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₂.2 hj₂) x]
      | or w₁ w₂ =>
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_input]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₂.2 hj₂) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₁.2 hj₂) x]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₁.2 hj₂) x,
                      evalGateAt_append_right C₁ C₂
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hj₂) C₁.gates)
                        (Nat.lt_trans j₂.2 hj₂) x]
  termination_by j => j

/-- **Left append correctness.**  `appendOutputLeft C₁ C₂` evaluates like `C₁`. -/
@[simp] theorem eval_appendOutputLeft {n : Nat} (C₁ C₂ : DagCircuit n)
    (x : Bitstring n) :
    eval (appendOutputLeft C₁ C₂) x = eval C₁ x := by
  unfold eval
  cases hout : C₁.output with
  | input j =>
      simp [appendOutputLeft, weakenWireRight, hout]
  | gate g =>
      have h : (appendOutputLeft C₁ C₂).output = DagWire.gate (Fin.castAdd C₂.gates g) := by
        simp [appendOutputLeft, weakenWireRight, hout]
      rw [h]
      exact evalGateAt_append_left C₁ C₂ _ g.2 x

/-- **Right append correctness.**  `appendOutputRight C₁ C₂` evaluates like `C₂`. -/
@[simp] theorem eval_appendOutputRight {n : Nat} (C₁ C₂ : DagCircuit n)
    (x : Bitstring n) :
    eval (appendOutputRight C₁ C₂) x = eval C₂ x := by
  unfold eval
  cases hout : C₂.output with
  | input j =>
      simp [appendOutputRight, shiftWireBy, hout]
  | gate g =>
      have h : (appendOutputRight C₁ C₂).output = DagWire.gate (Fin.natAdd C₁.gates g) := by
        simp [appendOutputRight, shiftWireBy, hout]
      rw [h]
      exact evalGateAt_append_right C₁ C₂ _ g.2 x

/-! ### Composition layer, step 4a: multi-output `DagBundle` (definitions)

A `DagBundle n out` is a `DagCircuit`-like object with one shared gate list and
`out` output wires.  This is the container `substInputs` needs: substituting
`G₁,…,Gₙ` into a circuit requires keeping *all* their output wires, which a
single-output `DagCircuit` cannot hold.

`asCircuit`/`evalOutput` bridge back to ordinary circuits so the (already proved)
append eval lemmas can be reused for the `snocBundle` semantics (the old-output
eval lemma below); the new (last) output is handled by a direct induction.
-/

/-- Multi-output DAG: a shared gate list with `out` output wires. -/
structure DagBundle (n out : Nat) where
  gates : Nat
  gate : (i : Fin gates) → DagGate n i.1
  output : Fin out → DagWire n gates

/-- View one output of a bundle as an ordinary `DagCircuit`. -/
def DagBundle.asCircuit {n out : Nat} (B : DagBundle n out) (o : Fin out) : DagCircuit n where
  gates := B.gates
  gate := B.gate
  output := B.output o

/-- Evaluate one output of a bundle. -/
def DagBundle.evalOutput {n out : Nat} (B : DagBundle n out) (o : Fin out)
    (x : Bitstring n) : Bool :=
  eval (B.asCircuit o) x

/-- The empty bundle: no outputs, no gates. -/
def emptyBundle (n : Nat) : DagBundle n 0 where
  gates := 0
  gate := fun i => absurd i.2 (Nat.not_lt_zero i.1)
  output := fun o => absurd o.2 (Nat.not_lt_zero o.1)

/-- Append circuit `C` as a new (last) output of bundle `B`, concatenating gate
lists.  Old gate references stay (left part of `Fin.addCases`); `C`'s gates are
shifted by `B.gates`.  Old output wires are weakened; `C`'s output is shifted. -/
def snocBundle {n out : Nat} (B : DagBundle n out) (C : DagCircuit n) :
    DagBundle n (out + 1) where
  gates := B.gates + C.gates
  gate := Fin.addCases (motive := fun i => DagGate n i.1)
    (fun p => B.gate p)
    (fun j => shiftGateBy B.gates (C.gate j))
  output := Fin.addCases (motive := fun _ => DagWire n (B.gates + C.gates))
    (fun o => weakenWireRight C.gates (B.output o))
    (fun _ => shiftWireBy B.gates C.output)

@[simp] theorem snocBundle_gates {n out : Nat} (B : DagBundle n out) (C : DagCircuit n) :
    (snocBundle B C).gates = B.gates + C.gates := rfl

/-! ### Composition layer, step 4a (eval): `snocBundle` correctness

First the gate/output characterization on the two `Fin.addCases` branches (left =
old part, right = the newly appended `C`), then eval-preservation for both outputs:

* the **old** outputs reuse the already-proved `appendOutputLeft` semantics, via the
  circuit equality `(snocBundle B C).asCircuit (castAdd 1 o) = appendOutputLeft (B.asCircuit o) C`
  (only the `output` field differs, and `snocBundle_output_old` settles it);
* the **new** (last) output is proved *directly* by a gate-level induction
  (`evalGateAt_snocBundle_right`).  There is no `DagCircuit` view of `B` to feed
  `appendOutputRight` when `out = 0` (a `DagWire n B.gates` need not exist when
  `n = B.gates = 0`), so no left circuit is fabricated.
-/

/-- Old (left, `castAdd`) gate positions of `snocBundle` reuse `B`'s gate. -/
@[simp] theorem snocBundle_gate_left {n out : Nat} (B : DagBundle n out) (C : DagCircuit n)
    (p : Fin B.gates) :
    (snocBundle B C).gate (Fin.castAdd C.gates p) = B.gate p := by
  simp only [snocBundle, Fin.addCases_left]

/-- New (right, `natAdd`) gate positions of `snocBundle` use `C`'s gate shifted by `B.gates`. -/
@[simp] theorem snocBundle_gate_right {n out : Nat} (B : DagBundle n out) (C : DagCircuit n)
    (j : Fin C.gates) :
    (snocBundle B C).gate (Fin.natAdd B.gates j) = shiftGateBy B.gates (C.gate j) := by
  simp only [snocBundle, Fin.addCases_right]

/-- An old output wire of `snocBundle` is `B`'s output wire, weakened. -/
@[simp] theorem snocBundle_output_old {n out : Nat} (B : DagBundle n out) (C : DagCircuit n)
    (o : Fin out) :
    (snocBundle B C).output (Fin.castAdd 1 o) = weakenWireRight C.gates (B.output o) := by
  simp only [snocBundle, Fin.addCases_left]

/-- The new (last) output wire of `snocBundle` is `C`'s output wire, shifted by `B.gates`. -/
@[simp] theorem snocBundle_output_new {n out : Nat} (B : DagBundle n out) (C : DagCircuit n) :
    (snocBundle B C).output (Fin.natAdd out (0 : Fin 1)) = shiftWireBy B.gates C.output := by
  simp only [snocBundle, Fin.addCases_right]

/-- **Old-output correctness.**  An old output of `snocBundle B C` evaluates exactly like
the corresponding output of `B`.  Reuses `eval_appendOutputLeft` through the circuit
equality `(snocBundle B C).asCircuit (castAdd 1 o) = appendOutputLeft (B.asCircuit o) C`. -/
@[simp] theorem evalOutput_snocBundle_old {n out : Nat} (B : DagBundle n out) (C : DagCircuit n)
    (o : Fin out) (x : Bitstring n) :
    (snocBundle B C).evalOutput (Fin.castAdd 1 o) x = B.evalOutput o x := by
  have h : (snocBundle B C).asCircuit (Fin.castAdd 1 o) = appendOutputLeft (B.asCircuit o) C := by
    unfold DagBundle.asCircuit
    rw [snocBundle_output_old B C o]
    rfl
  unfold DagBundle.evalOutput
  rw [h, eval_appendOutputLeft]

/-- Gate-level agreement for the new (appended) part of `snocBundle`: position
`B.gates + j` evaluates like `C`'s gate `j`.  Direct analogue of
`evalGateAt_append_right`, using `snocBundle_gate_right` for the gate lookup — no
left `DagCircuit` is needed (so `out = 0` is fine). -/
theorem evalGateAt_snocBundle_right {n out : Nat} (B : DagBundle n out) (C : DagCircuit n) :
    ∀ {j : Nat} (hjA : B.gates + j < (snocBundle B C).gates) (hjC : j < C.gates)
      (x : Bitstring n),
      DagCircuit.eval.evalGateAt
          (C := (snocBundle B C).asCircuit (Fin.natAdd out (0 : Fin 1)))
          (x := x) (B.gates + j) hjA =
        DagCircuit.eval.evalGateAt (C := C) (x := x) j hjC
  | j, hjA, hjC, x => by
      have hgate : ((snocBundle B C).asCircuit (Fin.natAdd out (0 : Fin 1))).gate
            ⟨B.gates + j, hjA⟩ = shiftGateBy B.gates (C.gate ⟨j, hjC⟩) :=
        snocBundle_gate_right B C ⟨j, hjC⟩
      cases hOp : C.gate ⟨j, hjC⟩ with
      | const b =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
          simp only [hOp, shiftGateBy_const]
      | not w =>
          cases w with
          | input jj =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
              simp only [hOp, shiftGateBy_not, shiftWireBy_input]
          | gate g =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
              simp only [hOp, shiftGateBy_not, shiftWireBy_gate, Fin.coe_natAdd]
              rw [evalGateAt_snocBundle_right B C
                    (Nat.add_lt_add_left (Nat.lt_trans g.2 hjC) B.gates)
                    (Nat.lt_trans g.2 hjC) x]
      | and w₁ w₂ =>
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_input]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hjC) B.gates)
                        (Nat.lt_trans j₂.2 hjC) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hjC) B.gates)
                        (Nat.lt_trans j₁.2 hjC) x]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_and, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hjC) B.gates)
                        (Nat.lt_trans j₁.2 hjC) x,
                      evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hjC) B.gates)
                        (Nat.lt_trans j₂.2 hjC) x]
      | or w₁ w₂ =>
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_input]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hjC) B.gates)
                        (Nat.lt_trans j₂.2 hjC) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_input, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hjC) B.gates)
                        (Nat.lt_trans j₁.2 hjC) x]
              | gate j₂ =>
                  rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt, hgate]
                  simp only [hOp, shiftGateBy_or, shiftWireBy_gate, Fin.coe_natAdd]
                  rw [evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₁.2 hjC) B.gates)
                        (Nat.lt_trans j₁.2 hjC) x,
                      evalGateAt_snocBundle_right B C
                        (Nat.add_lt_add_left (Nat.lt_trans j₂.2 hjC) B.gates)
                        (Nat.lt_trans j₂.2 hjC) x]
  termination_by j => j

/-- **New-output correctness.**  The new (last) output of `snocBundle B C` evaluates
exactly like `C`.  Proved directly (no fabricated left circuit). -/
@[simp] theorem evalOutput_snocBundle_new {n out : Nat} (B : DagBundle n out) (C : DagCircuit n)
    (x : Bitstring n) :
    (snocBundle B C).evalOutput (Fin.natAdd out (0 : Fin 1)) x = eval C x := by
  unfold DagBundle.evalOutput
  unfold eval
  cases hout : C.output with
  | input j =>
      simp [DagBundle.asCircuit, snocBundle_output_new, shiftWireBy, hout]
  | gate g =>
      have h : ((snocBundle B C).asCircuit (Fin.natAdd out (0 : Fin 1))).output
            = DagWire.gate (Fin.natAdd B.gates g) := by
        simp [DagBundle.asCircuit, snocBundle_output_new, shiftWireBy, hout]
      rw [h]
      exact evalGateAt_snocBundle_right B C _ g.2 x

end DagCircuit
end ComplexityInterfaces
end Pnp3
