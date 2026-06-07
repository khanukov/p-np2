import Pnp4.Frontier.ContractExpansion.TreeMCSPStackFlatten

/-!
# `runStack` — D2t-5b foundation: the value-stack execution model

D2t-5's on-tape driver reads the certificate in **preorder** and maintains, in tape scratch, a **value
stack** of completed-subtree **root WORK-indices**: a leaf emits its record and pushes its index; an
internal node, once its children are done, **pops** their indices, emits the gate record with those
indices as operands, and pushes its own index.  This module fixes the pure semantics of that value stack
and proves it correct against the structural `flattenAt` — the loop invariant the on-tape driver (D2t-5b)
will be proven to maintain.

It reuses D2t-5's postorder step program `toSteps` (#1589) but executes it with a **value stack** rather
than the static carried sizes:

* `runStack prog (out, S)` — threads the WORK accumulator `out` and the index stack `S`.  A leaf/`mk*`
  step appends one gate and pushes its index `out.length`; binary `mk*` steps **pop** the two operand
  indices off `S` (so operands are read off the stack directly — no truncating-`Nat` arithmetic, unlike
  `runSteps`).
* `runStack_toSteps` — the key invariant: running `c`'s program appends exactly `flattenAt out.length c`
  to WORK and pushes its root index `out.length + c.size - 1`.
* `flattenStackVS_eq_flatten` — `(runStack (toSteps c) ([], [])).1 = (flatten c).gates`, and the final
  value stack is the single root index `[c.size - 1]`.
* `flattenStackVS_eq_flattenStack` — the value-stack model agrees with the size-carrying `flattenStack`
  (#1589): both compute the postorder flatten.

**Progress classification (AGENTS.md): Infrastructure** — a pure transcoder-algorithm spec proven against
the verified `flattenAt`; builds no machine and proves no separation.  Standard `[propext, Quot.sound]`
only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Execute a postorder step program against a WORK accumulator `out` **and** a value stack `S` of
completed-subtree root indices.  A leaf / unary / binary step appends one gate at index `out.length` and
pushes that index; binary steps first **pop** their two operand indices off `S` (so the gate's operands
are exactly the children's indices — read off the stack, never computed by subtraction).  The size carried
by `mkAnd`/`mkOr` is ignored here (the stack supplies the operands).

This is a **propositional spec** (used only inside proofs, never executed), so the per-step `out ++ [·]`
accumulation and the malformed-state halt are immaterial to its role: the only intended caller is
`flattenStackVS` (`runStack (toSteps c) ([], [])`), and `runStack_toSteps` establishes that such a run is
well-formed (the value stack never underflows) and equals `flattenAt 0 c`.  A `mk*` step with too few
stacked indices simply halts unchanged (the catch-all) — that state never arises from a `toSteps`-produced
program run from the empty stack, so it is unreachable on the proven path; running an arbitrary, hand-built
program is not a supported use. -/
def runStack {n : Nat} :
    List (FlattenStep n) → List (SLGate n) × List Nat → List (SLGate n) × List Nat
  | [], st => st
  | FlattenStep.leaf g :: w, (out, S) => runStack w (out ++ [g], out.length :: S)
  | FlattenStep.mkNot :: w, (out, i :: S) => runStack w (out ++ [SLGate.notGate i], out.length :: S)
  | FlattenStep.mkAnd _ :: w, (out, i2 :: i1 :: S) =>
      runStack w (out ++ [SLGate.andGate i1 i2], out.length :: S)
  | FlattenStep.mkOr _ :: w, (out, i2 :: i1 :: S) =>
      runStack w (out ++ [SLGate.orGate i1 i2], out.length :: S)
  | _ :: _, st => st

/-- **The value-stack invariant.**  Running the postorder program of `c` appends exactly
`flattenAt out.length c` to WORK and pushes `c`'s root index `out.length + c.size - 1`.  Induction on `c`;
the operand indices come straight off the stack (the IH's pushed root indices), so no `Nat`-subtraction
reconciliation is needed — only the pushed root index uses `size`. -/
theorem runStack_toSteps {n : Nat} (c : CircuitTree n) :
    ∀ (w : List (FlattenStep n)) (out : List (SLGate n)) (S : List Nat),
      runStack (toSteps c ++ w) (out, S)
        = runStack w (out ++ CircuitTree.flattenAt out.length c,
            (out.length + c.size - 1) :: S) := by
  induction c with
  | input i => intro w out S; simp [toSteps, runStack, CircuitTree.flattenAt, CircuitTree.size]
  | const b => intro w out S; simp [toSteps, runStack, CircuitTree.flattenAt, CircuitTree.size]
  | not c ih =>
      intro w out S
      have hcat : toSteps (CircuitTree.not c) ++ w = toSteps c ++ (FlattenStep.mkNot :: w) := by
        simp [toSteps, List.append_assoc]
      rw [hcat, ih (FlattenStep.mkNot :: w) out S]
      simp only [runStack, CircuitTree.flattenAt, CircuitTree.size, List.length_append,
        CircuitTree.flattenAt_length, List.append_assoc]
      congr 2
  | and a b iha ihb =>
      intro w out S
      have hcat : toSteps (CircuitTree.and a b) ++ w
          = toSteps a ++ (toSteps b ++ (FlattenStep.mkAnd b.size :: w)) := by
        simp [toSteps, List.append_assoc]
      rw [hcat, iha (toSteps b ++ (FlattenStep.mkAnd b.size :: w)) out S,
        ihb (FlattenStep.mkAnd b.size :: w) (out ++ CircuitTree.flattenAt out.length a)
          ((out.length + a.size - 1) :: S)]
      simp only [runStack, CircuitTree.flattenAt, CircuitTree.size, List.length_append,
        CircuitTree.flattenAt_length, List.append_assoc]
      congr 2
  | or a b iha ihb =>
      intro w out S
      have hcat : toSteps (CircuitTree.or a b) ++ w
          = toSteps a ++ (toSteps b ++ (FlattenStep.mkOr b.size :: w)) := by
        simp [toSteps, List.append_assoc]
      rw [hcat, iha (toSteps b ++ (FlattenStep.mkOr b.size :: w)) out S,
        ihb (FlattenStep.mkOr b.size :: w) (out ++ CircuitTree.flattenAt out.length a)
          ((out.length + a.size - 1) :: S)]
      simp only [runStack, CircuitTree.flattenAt, CircuitTree.size, List.length_append,
        CircuitTree.flattenAt_length, List.append_assoc]
      congr 2

/-- Running `c`'s program from the empty WORK/stack: the WORK is the flattened gate list and the value
stack ends with the single root index `c.size - 1`. -/
theorem runStack_toSteps_nil {n : Nat} (c : CircuitTree n) :
    runStack (toSteps c) ([], []) = ((CircuitTree.flatten c).gates, [c.size - 1]) := by
  have h := runStack_toSteps c [] [] []
  simpa [runStack, CircuitTree.flatten] using h

/-- The value-stack model's WORK output: the iterative value-stack linearization of a circuit tree. -/
def flattenStackVS {n : Nat} (c : CircuitTree n) : List (SLGate n) :=
  (runStack (toSteps c) ([], [])).1

/-- **D2t-5b invariant (pure).**  The value-stack execution produces exactly the flattened gate list. -/
theorem flattenStackVS_eq_flatten {n : Nat} (c : CircuitTree n) :
    flattenStackVS c = (CircuitTree.flatten c).gates := by
  rw [flattenStackVS, runStack_toSteps_nil]

/-- The value-stack model agrees with the size-carrying `flattenStack` (#1589): both compute the postorder
flatten. -/
theorem flattenStackVS_eq_flattenStack {n : Nat} (c : CircuitTree n) :
    flattenStackVS c = flattenStack c := by
  rw [flattenStackVS_eq_flatten, flattenStack_eq_flatten]

/-- The value-stack WORK record stream equals that of the flattened circuit — the D2t-5c target, reached
through the on-tape driver's value-stack discipline. -/
theorem encodeGateRecordStream_flattenStackVS {n : Nat} (c : CircuitTree n) :
    encodeGateRecordStream (flattenStackVS c) = encodeGateRecordStream (CircuitTree.flatten c).gates := by
  rw [flattenStackVS_eq_flatten]

/-! ### Pure D2t-5 capstone: the stack algorithm is a faithful transcoder

Packaging the value-stack linearization with the self-delimiting gate-count prefix gives the full
**stack-based transcoder output**; decoding it recovers a straight-line program computing the circuit.
This connects the D2t-5 *algorithm* (not just `flatten` abstractly) to the §9 transcoder faithfulness
(`transcodeWitness_faithful`), and is the pure correctness statement the on-tape driver (D2t-5b/c) must
realise: its WORK + gate-count prefix equals this stream. -/

/-- The stack-based transcoder output: the count-prefixed gate-record stream produced by the D2t-5
value-stack linearization algorithm. -/
def transcodeStreamViaStack {n : Nat} (c : CircuitTree n) : List Bool :=
  encodeGateStream (flattenStackVS c)

/-- The stack transcoder stream equals the self-delimiting stream of the flattened circuit. -/
theorem transcodeStreamViaStack_eq {n : Nat} (c : CircuitTree n) :
    transcodeStreamViaStack c = encodeGateStream (CircuitTree.flatten c).gates := by
  rw [transcodeStreamViaStack, flattenStackVS_eq_flatten]

/-- **D2t-5 algorithm faithfulness (pure).**  The value-stack transcoder of a circuit's tree yields a
self-delimiting stream that decodes to a straight-line program computing the circuit's value — the stack
algorithm realises the §9 transcoder spec end-to-end (cf. `transcodeWitness_faithful`, which routes
through `flatten` directly). -/
theorem transcodeStreamViaStack_faithful {n : Nat} (c : Pnp3.Models.Circuit n) (x : Fin n → Bool) :
    ∃ gates : List (SLGate n),
      decodeGateStream n (transcodeStreamViaStack (toTree c)) = some (gates, [])
      ∧ SLProgram.eval ⟨gates⟩ x = some (Pnp3.Models.Circuit.eval c x) := by
  rw [transcodeStreamViaStack_eq]
  simpa using decodeGateStream_circuit_eval c x []

end ContractExpansion
end Frontier
end Pnp4
