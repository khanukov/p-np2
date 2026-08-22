import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Direct iterative evaluation of concrete tree-codec witnesses

**Progress classification (AGENTS.md): Infrastructure.**  This removes a concrete semantic
sub-obligation of the `PrefixExtensionNPWitness` route, but constructs no verifier bridge and
reduces neither mainline source obligation.  **No `P ≠ NP` claim.**

The existing depth-free decoder reads the authoritative five-tag, fixed-width prefix encoding.
After that direct parse, `directEvalLoop` evaluates the decoded tree with explicit control and
value stacks.  In particular, evaluation does not recurse on `Circuit`; recursive occurrences are
placed on the control stack and consumed by a fuelled tail-recursive loop.
-/

/-- Control-stack entries for the direct tree evaluator. -/
inductive DirectEvalTask (n : Nat) where
  | visit : Pnp3.Models.Circuit n → DirectEvalTask n
  | applyNot : DirectEvalTask n
  | applyAnd : DirectEvalTask n
  | applyOr : DirectEvalTask n

/-- Exact number of control-loop iterations used to visit and reduce a circuit. -/
def directEvalCost {n : Nat} : Pnp3.Models.Circuit n → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => directEvalCost c + 2
  | .and a b => directEvalCost a + directEvalCost b + 2
  | .or a b => directEvalCost a + directEvalCost b + 2

/-- Tail-recursive evaluator with explicit control/value stacks and an explicit gate counter.
Malformed control states (including value-stack underflow) return `none`. -/
def directEvalLoop {n : Nat} (x : Fin n → Bool) :
    Nat → List (DirectEvalTask n) → List Bool → Nat → Option (Nat × Bool)
  | _, [], [v], gates => some (gates, v)
  | _, [], _, _ => none
  | 0, _ :: _, _, _ => none
  | fuel + 1, .visit (.input i) :: tasks, values, gates =>
      directEvalLoop x fuel tasks (x i :: values) (gates + 1)
  | fuel + 1, .visit (.const b) :: tasks, values, gates =>
      directEvalLoop x fuel tasks (b :: values) (gates + 1)
  | fuel + 1, .visit (.not c) :: tasks, values, gates =>
      directEvalLoop x fuel (.visit c :: .applyNot :: tasks) values (gates + 1)
  | fuel + 1, .visit (.and a b) :: tasks, values, gates =>
      directEvalLoop x fuel (.visit a :: .visit b :: .applyAnd :: tasks) values (gates + 1)
  | fuel + 1, .visit (.or a b) :: tasks, values, gates =>
      directEvalLoop x fuel (.visit a :: .visit b :: .applyOr :: tasks) values (gates + 1)
  | fuel + 1, .applyNot :: tasks, v :: values, gates =>
      directEvalLoop x fuel tasks ((!v) :: values) gates
  | _ + 1, .applyNot :: _, [], _ => none
  | fuel + 1, .applyAnd :: tasks, right :: left :: values, gates =>
      directEvalLoop x fuel tasks ((left && right) :: values) gates
  | _ + 1, .applyAnd :: _, _, _ => none
  | fuel + 1, .applyOr :: tasks, right :: left :: values, gates =>
      directEvalLoop x fuel tasks ((left || right) :: values) gates
  | _ + 1, .applyOr :: _, _, _ => none

/-- A visit consumes its exact cost and leaves the recursive evaluator's value and size on the
explicit stacks.  The continuation and its residual fuel are arbitrary. -/
theorem directEvalLoop_visit {n : Nat} (x : Fin n → Bool) (c : Pnp3.Models.Circuit n) :
    ∀ (fuel : Nat) (tasks : List (DirectEvalTask n)) (values : List Bool) (gates : Nat),
      directEvalLoop x (directEvalCost c + fuel) (.visit c :: tasks) values gates =
        directEvalLoop x fuel tasks (Pnp3.Models.Circuit.eval c x :: values)
          (gates + Pnp3.Models.Circuit.size c) := by
  induction c with
  | input i =>
      intro fuel tasks values gates
      rw [show directEvalCost (.input i) + fuel = fuel + 1 by
        simp [directEvalCost]; omega]
      simp [directEvalLoop, Pnp3.Models.Circuit.eval, Pnp3.Models.Circuit.size]
  | const b =>
      intro fuel tasks values gates
      rw [show directEvalCost (.const b) + fuel = fuel + 1 by
        simp [directEvalCost]; omega]
      simp [directEvalLoop, Pnp3.Models.Circuit.eval, Pnp3.Models.Circuit.size]
  | not c ih =>
      intro fuel tasks values gates
      simp only [directEvalCost, Pnp3.Models.Circuit.eval, Pnp3.Models.Circuit.size]
      rw [show directEvalCost c + 2 + fuel = (directEvalCost c + (fuel + 1)) + 1 by omega]
      simp only [directEvalLoop]
      rw [ih (fuel + 1) (.applyNot :: tasks) values (gates + 1)]
      simp [directEvalLoop, Nat.add_assoc, Nat.add_comm]
  | and a b iha ihb =>
      intro fuel tasks values gates
      simp only [directEvalCost, Pnp3.Models.Circuit.eval, Pnp3.Models.Circuit.size]
      rw [show directEvalCost a + directEvalCost b + 2 + fuel =
          (directEvalCost a + (directEvalCost b + (fuel + 1))) + 1 by omega]
      simp only [directEvalLoop]
      rw [iha (directEvalCost b + (fuel + 1))
        (.visit b :: .applyAnd :: tasks) values (gates + 1)]
      rw [ihb (fuel + 1) (.applyAnd :: tasks)
        (Pnp3.Models.Circuit.eval a x :: values)
        (gates + 1 + Pnp3.Models.Circuit.size a)]
      simp [directEvalLoop, Nat.add_assoc, Nat.add_comm]
  | or a b iha ihb =>
      intro fuel tasks values gates
      simp only [directEvalCost, Pnp3.Models.Circuit.eval, Pnp3.Models.Circuit.size]
      rw [show directEvalCost a + directEvalCost b + 2 + fuel =
          (directEvalCost a + (directEvalCost b + (fuel + 1))) + 1 by omega]
      simp only [directEvalLoop]
      rw [iha (directEvalCost b + (fuel + 1))
        (.visit b :: .applyOr :: tasks) values (gates + 1)]
      rw [ihb (fuel + 1) (.applyOr :: tasks)
        (Pnp3.Models.Circuit.eval a x :: values)
        (gates + 1 + Pnp3.Models.Circuit.size a)]
      simp [directEvalLoop, Nat.add_assoc, Nat.add_comm]

/-- Iterative evaluation of one already-decoded native tree circuit. -/
def directCircuitEval {n : Nat} (c : Pnp3.Models.Circuit n) (x : Fin n → Bool) :
    Option (Nat × Bool) :=
  directEvalLoop x (directEvalCost c) [.visit c] [] 0

/-- The iterative control/value-stack evaluator returns recursive size and semantics exactly. -/
theorem directCircuitEval_correct {n : Nat} (c : Pnp3.Models.Circuit n)
    (x : Fin n → Bool) :
    directCircuitEval c x = some (Pnp3.Models.Circuit.size c, Pnp3.Models.Circuit.eval c x) := by
  unfold directCircuitEval
  rw [show directEvalCost c = directEvalCost c + 0 by omega]
  rw [directEvalLoop_visit x c 0 [] [] 0]
  simp [directEvalLoop]

/-- Direct reference evaluator on an arbitrary list in the concrete codec format.  The parser is
the actual depth-free prefix decoder, with runtime input-index width `bitLength n`. -/
def nativeEvalList (n : Nat) (bits : List Bool) (x : Fin n → Bool) :
    Option (Nat × Bool) :=
  match decodeCircuitFull n (bitLength n) bits with
  | none => none
  | some (c, _) => directCircuitEval c x

/-- Direct reference evaluator on the actual fixed-width witness bits. -/
def nativeEval (threshold : Nat → Nat) (n : Nat)
    (w : AlgorithmsToLowerBounds.BitVec
      ((treeCircuitWitnessCodec threshold).witnessBits n))
    (x : Fin n → Bool) : Option (Nat × Bool) :=
  nativeEvalList n (List.ofFn w) x

/-- Headline arbitrary-witness theorem: decode failure is rejected, while every successful
concrete decode returns exactly the decoded tree's size and value.  There are no hypotheses. -/
theorem nativeEval_spec (threshold : Nat → Nat) (n : Nat)
    (w : AlgorithmsToLowerBounds.BitVec
      ((treeCircuitWitnessCodec threshold).witnessBits n))
    (x : Fin n → Bool) :
    match (treeCircuitWitnessCodec threshold).decode n w with
    | none => nativeEval threshold n w x = none
    | some c => nativeEval threshold n w x =
        some (Pnp3.Models.Circuit.size c, Pnp3.Models.Circuit.eval c x) := by
  unfold treeCircuitWitnessCodec treeSelfDelimitingCode SelfDelimitingCircuitCode.toCodec
  unfold nativeEval nativeEvalList
  cases h : decodeCircuitFull n (bitLength n) (List.ofFn w) with
  | none => simp [h]
  | some p =>
      rcases p with ⟨c, rest⟩
      simp [h, directCircuitEval_correct]

/-- Fewer than three bits cannot contain a tree tag. -/
theorem nativeEvalList_rejects_short_tag (n : Nat) (bits : List Bool)
    (x : Fin n → Bool) (hshort : bits.length < 3) :
    nativeEvalList n bits x = none := by
  unfold nativeEvalList decodeCircuitFull decodeCircuit
  rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, tail⟩⟩⟩
  · simp [Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth]
  · simp [Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth]
  · simp [Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth]
  · simp only [List.length_cons] at hshort
    omega

/-- Malformed tag `101` is rejected for every tail. -/
@[simp] theorem nativeEvalList_rejects_tag101 (n : Nat) (rest : List Bool)
    (x : Fin n → Bool) :
    nativeEvalList n (true :: false :: true :: rest) x = none := by
  simp [nativeEvalList, decodeCircuitFull, decodeCircuit,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth]

/-- Malformed tag `110` is rejected for every tail. -/
@[simp] theorem nativeEvalList_rejects_tag110 (n : Nat) (rest : List Bool)
    (x : Fin n → Bool) :
    nativeEvalList n (true :: true :: false :: rest) x = none := by
  simp [nativeEvalList, decodeCircuitFull, decodeCircuit,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth]

/-- Malformed tag `111` is rejected for every tail. -/
@[simp] theorem nativeEvalList_rejects_tag111 (n : Nat) (rest : List Bool)
    (x : Fin n → Bool) :
    nativeEvalList n (true :: true :: true :: rest) x = none := by
  simp [nativeEvalList, decodeCircuitFull, decodeCircuit,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth]

/-- The input tag rejects a payload shorter than the runtime field width `bitLength n`. -/
theorem nativeEvalList_rejects_short_input_field (n : Nat) (rest : List Bool)
    (x : Fin n → Bool) (hshort : rest.length < bitLength n) :
    nativeEvalList n (false :: false :: false :: rest) x = none := by
  simp [nativeEvalList, decodeCircuitFull, decodeCircuit,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth, hshort]

/-- A full runtime-width input field is still rejected when its decoded index is outside `Fin n`.
This makes the index-validity failure distinct from the short-field failure above. -/
theorem nativeEvalList_rejects_invalid_input_index (n : Nat)
    (i : Fin (2 ^ bitLength n)) (rest : List Bool) (x : Fin n → Bool)
    (hinvalid : n ≤ i.val) :
    nativeEvalList n
      (false :: false :: false ::
        (Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeFin (bitLength n) i ++ rest)) x = none := by
  simp [nativeEvalList, decodeCircuitFull, decodeCircuit,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeCircuitTreeAtDepth,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeFin_length,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.decodeFin_encodeFin]
  split <;> simp_all

/-- Size-capped direct evaluation.  This is the concrete threshold-overflow check needed by the
verifier, separated from parsing because the codec's own `decode` intentionally does not cap. -/
def nativeEvalBounded (threshold : Nat → Nat) (n : Nat)
    (w : AlgorithmsToLowerBounds.BitVec
      ((treeCircuitWitnessCodec threshold).witnessBits n))
    (x : Fin n → Bool) : Option (Nat × Bool) :=
  match nativeEval threshold n w x with
  | some r => if r.1 ≤ threshold n then some r else none
  | none => none

/-- Threshold overflow is explicitly rejected. -/
theorem nativeEvalBounded_rejects_threshold_overflow
    (threshold : Nat → Nat) (n : Nat)
    (w : AlgorithmsToLowerBounds.BitVec
      ((treeCircuitWitnessCodec threshold).witnessBits n))
    (x : Fin n → Bool) (r : Nat × Bool)
    (hEval : nativeEval threshold n w x = some r) (hOverflow : threshold n < r.1) :
    nativeEvalBounded threshold n w x = none := by
  simp [nativeEvalBounded, hEval, Nat.not_le.mpr hOverflow]

/-- Explicit value-stack-underflow rejection for unary reduction. -/
theorem directEvalLoop_rejects_not_underflow {n fuel gates : Nat} (x : Fin n → Bool)
    (tasks : List (DirectEvalTask n)) :
    directEvalLoop x (fuel + 1) (.applyNot :: tasks) [] gates = none := by
  simp [directEvalLoop]

/-- Explicit value-stack-underflow rejection for binary reduction. -/
theorem directEvalLoop_rejects_and_underflow {n fuel gates : Nat} (x : Fin n → Bool)
    (tasks : List (DirectEvalTask n)) (values : List Bool) (h : values.length < 2) :
    directEvalLoop x (fuel + 1) (.applyAnd :: tasks) values gates = none := by
  rcases values with _ | ⟨a, _ | ⟨b, tail⟩⟩
  · simp [directEvalLoop]
  · simp [directEvalLoop]
  · simp only [List.length_cons] at h
    omega

/-- The loop uses fewer than twice the number of circuit nodes plus one iterations. -/
theorem directEvalCost_le_two_mul_size {n : Nat} (c : Pnp3.Models.Circuit n) :
    directEvalCost c ≤ 2 * Pnp3.Models.Circuit.size c := by
  induction c with
  | input i => simp [directEvalCost, Pnp3.Models.Circuit.size]
  | const b => simp [directEvalCost, Pnp3.Models.Circuit.size]
  | not c ih => simp only [directEvalCost, Pnp3.Models.Circuit.size]; omega
  | and a b iha ihb => simp only [directEvalCost, Pnp3.Models.Circuit.size]; omega
  | or a b iha ihb => simp only [directEvalCost, Pnp3.Models.Circuit.size]; omega

/-- Conservative linear reference capacity for a serialized direct-evaluator layout. -/
def directStackCapacity (serializedLength : Nat) : Nat := 2 * serializedLength + 2

/-- A quadratic single-tape microstep budget: at most `2L+1` logical iterations, each allowed a
home-to-home scan of at most `2L+2` cells. -/
def directMicrostepBound (serializedLength : Nat) : Nat :=
  (2 * serializedLength + 1) * directStackCapacity serializedLength

theorem directMicrostepBound_polynomial (L : Nat) :
    directMicrostepBound L ≤ 4 * (L + 1) ^ 2 := by
  unfold directMicrostepBound directStackCapacity
  nlinarith

end ContractExpansion
end Frontier
end Pnp4
