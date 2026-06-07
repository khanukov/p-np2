import Pnp4.Frontier.ContractExpansion.TreeMCSPGateStreamLayout

/-!
# `flattenStack` — D2t-5 pure core: the preorder→postorder stack linearization

D2t-5 is the on-tape **prefix→postfix engine**: the certificate is a `CircuitTree` in **preorder**
(`encodeCircuitTree`: `tag(root) ++ encode(child₁) ++ encode(child₂)`), but the WORK record stream the
interpreter consumes is **postorder** with **absolute** operand indices (`CircuitTree.flattenAt`:
`flatten(child₁) ++ flatten(child₂) ++ [gate(root)]`, root operands `offset + |sub₁| − 1`,
`offset + |sub₁| + |sub₂| − 1`).  Converting one to the other **requires a stack**; a fixed-phase TM puts
that stack in tape scratch (the §11 design).

This module fixes the **pure algorithm** the on-tape stack machine (D2t-5a/b) must realise, and proves it
correct against the structural spec — the "correctness seam first" discipline (spec before tape), and the
de-risking foundation for D2t-5c (whose loop invariant is exactly "the tape state encodes a `runSteps`
configuration"):

* `toSteps` — the tree's **postorder step program**: leaves emit their gate; each internal node emits a
  `mk*` step *after* its children, carrying the **right child's size** (the datum the tape STACK supplies,
  letting the emitter locate the left operand relative to the running WORK length).
* `runSteps` — executes a step program against a WORK accumulator `out`, computing each gate's **absolute**
  operands from `out.length` (the next index) and the carried size.  Structurally recursive on the program.
* `flattenStack_eq_flattenAt` / `flattenStack_eq_flatten` — `runSteps (toSteps c) [] = flattenAt 0 c =
  (flatten c).gates`: the iterative stack linearization equals the structural postorder flatten, **index
  arithmetic and all**.
* `encodeGateRecordStream_flattenStack` — hence the emitted WORK record stream equals
  `encodeGateRecordStream (flatten c).gates` (the D2t-5c target).

**Progress classification (AGENTS.md): Infrastructure** — a pure transcoder-algorithm spec proven against
the verified `flattenAt`; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Every gate tree has at least one gate (each node contributes one). -/
theorem CircuitTree.one_le_size {n : Nat} (c : CircuitTree n) : 1 ≤ c.size := by
  cases c <;> simp only [CircuitTree.size] <;> omega

/-- A single step of the postorder linearization.  `leaf g` emits the leaf gate `g`; `mkNot` emits the
unary gate over the previous gate; `mkAnd s₂` / `mkOr s₂` emit the binary gate whose **right** operand is
the previous gate and whose **left** operand sits `s₂` (the right child's size) further back.  The size
`s₂` is exactly what the tape STACK hands the emitter. -/
inductive FlattenStep (n : Nat) where
  | leaf : SLGate n → FlattenStep n
  | mkNot : FlattenStep n
  | mkAnd : Nat → FlattenStep n
  | mkOr : Nat → FlattenStep n

/-- The tree's **postorder step program**: children first, then the node's emit step (carrying the right
child's size for the binary cases).  This is the order the preorder-reading stack machine retires nodes. -/
def toSteps {n : Nat} : CircuitTree n → List (FlattenStep n)
  | .input i => [FlattenStep.leaf (SLGate.input i)]
  | .const b => [FlattenStep.leaf (SLGate.const b)]
  | .not c => toSteps c ++ [FlattenStep.mkNot]
  | .and a b => toSteps a ++ toSteps b ++ [FlattenStep.mkAnd b.size]
  | .or a b => toSteps a ++ toSteps b ++ [FlattenStep.mkOr b.size]

/-- Execute a step program against the WORK accumulator `out`, appending one gate per step.  The next
gate's index is `out.length`; binary operands are read off as `out.length - 1` (the previous gate) and
`out.length - 1 - s₂` (its left sibling, `s₂` gates back).  Structurally recursive on the program. -/
def runSteps {n : Nat} : List (FlattenStep n) → List (SLGate n) → List (SLGate n)
  | [], out => out
  | FlattenStep.leaf g :: w, out => runSteps w (out ++ [g])
  | FlattenStep.mkNot :: w, out => runSteps w (out ++ [SLGate.notGate (out.length - 1)])
  | FlattenStep.mkAnd s2 :: w, out =>
      runSteps w (out ++ [SLGate.andGate (out.length - 1 - s2) (out.length - 1)])
  | FlattenStep.mkOr s2 :: w, out =>
      runSteps w (out ++ [SLGate.orGate (out.length - 1 - s2) (out.length - 1)])

/-- `runSteps` distributes over program concatenation (left fold). -/
theorem runSteps_append {n : Nat} (w1 w2 : List (FlattenStep n)) (out : List (SLGate n)) :
    runSteps (w1 ++ w2) out = runSteps w2 (runSteps w1 out) := by
  induction w1 generalizing out with
  | nil => simp [runSteps]
  | cons s w1 ih => cases s <;> simp only [List.cons_append, runSteps, ih]

/-- **The key invariant.**  Running the postorder program of `c` (then continuing with `w`) appends
exactly `flattenAt out.length c` to the WORK accumulator — the structural postorder flatten at the current
offset, with all absolute operand indices matching.  Induction on `c`; the binary cases need only
`1 ≤ a.size` to reconcile the `out.length - 1 - s₂` arithmetic with `flattenAt`'s `offset + |sub₁| - 1`. -/
theorem runSteps_toSteps {n : Nat} (c : CircuitTree n) :
    ∀ (w : List (FlattenStep n)) (out : List (SLGate n)),
      runSteps (toSteps c ++ w) out = runSteps w (out ++ CircuitTree.flattenAt out.length c) := by
  induction c with
  | input i => intro w out; simp [toSteps, runSteps, CircuitTree.flattenAt]
  | const b => intro w out; simp [toSteps, runSteps, CircuitTree.flattenAt]
  | not c ih =>
      intro w out
      have hcat : toSteps (CircuitTree.not c) ++ w = toSteps c ++ (FlattenStep.mkNot :: w) := by
        simp [toSteps, List.append_assoc]
      rw [hcat, ih (FlattenStep.mkNot :: w) out]
      simp only [runSteps, CircuitTree.flattenAt, List.length_append, CircuitTree.flattenAt_length,
        List.append_assoc]
  | and a b iha ihb =>
      intro w out
      have hcat : toSteps (CircuitTree.and a b) ++ w
          = toSteps a ++ (toSteps b ++ (FlattenStep.mkAnd b.size :: w)) := by
        simp [toSteps, List.append_assoc]
      rw [hcat, iha (toSteps b ++ (FlattenStep.mkAnd b.size :: w)) out,
        ihb (FlattenStep.mkAnd b.size :: w) (out ++ CircuitTree.flattenAt out.length a)]
      have ha : 1 ≤ a.size := CircuitTree.one_le_size a
      simp only [runSteps, CircuitTree.flattenAt, List.length_append, CircuitTree.flattenAt_length,
        List.append_assoc]
      rw [show SLGate.andGate (out.length + (a.size + b.size) - 1 - b.size)
              (out.length + (a.size + b.size) - 1)
            = SLGate.andGate (out.length + a.size - 1) (out.length + a.size + b.size - 1) from by
          congr 1 <;> omega]
  | or a b iha ihb =>
      intro w out
      have hcat : toSteps (CircuitTree.or a b) ++ w
          = toSteps a ++ (toSteps b ++ (FlattenStep.mkOr b.size :: w)) := by
        simp [toSteps, List.append_assoc]
      rw [hcat, iha (toSteps b ++ (FlattenStep.mkOr b.size :: w)) out,
        ihb (FlattenStep.mkOr b.size :: w) (out ++ CircuitTree.flattenAt out.length a)]
      have ha : 1 ≤ a.size := CircuitTree.one_le_size a
      simp only [runSteps, CircuitTree.flattenAt, List.length_append, CircuitTree.flattenAt_length,
        List.append_assoc]
      rw [show SLGate.orGate (out.length + (a.size + b.size) - 1 - b.size)
              (out.length + (a.size + b.size) - 1)
            = SLGate.orGate (out.length + a.size - 1) (out.length + a.size + b.size - 1) from by
          congr 1 <;> omega]

/-- The iterative stack linearization of a circuit tree: run its postorder step program from an empty
WORK accumulator. -/
def flattenStack {n : Nat} (c : CircuitTree n) : List (SLGate n) :=
  runSteps (toSteps c) []

/-- **D2t-5 algorithm correctness (pure).**  The iterative stack linearization equals the structural
postorder flatten — `runSteps (toSteps c) [] = flattenAt 0 c`. -/
theorem flattenStack_eq_flattenAt {n : Nat} (c : CircuitTree n) :
    flattenStack c = CircuitTree.flattenAt 0 c := by
  have h := runSteps_toSteps c [] []
  simpa [flattenStack, runSteps] using h

/-- The stack linearization equals the flattened straight-line program's gate list. -/
theorem flattenStack_eq_flatten {n : Nat} (c : CircuitTree n) :
    flattenStack c = (CircuitTree.flatten c).gates := by
  rw [flattenStack_eq_flattenAt]; rfl

/-- **D2t-5c target (pure).**  The WORK record stream the stack machine emits equals the record stream of
the flattened circuit — `encodeGateRecordStream (flatten c).gates`, exactly what the on-tape WORK must
match. -/
theorem encodeGateRecordStream_flattenStack {n : Nat} (c : CircuitTree n) :
    encodeGateRecordStream (flattenStack c) = encodeGateRecordStream (CircuitTree.flatten c).gates := by
  rw [flattenStack_eq_flatten]

end ContractExpansion
end Frontier
end Pnp4
