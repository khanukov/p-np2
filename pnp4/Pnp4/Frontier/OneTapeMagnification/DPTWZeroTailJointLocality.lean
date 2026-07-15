import Pnp4.Frontier.OneTapeMagnification.FiniteCheckpointToPpolyDAGBridge

/-!
# Joint locality for a DPTW-inspired zero-tail modification

This module formalizes only the deterministic circuit plumbing behind a
zero-tail modification of the Forbes--Kelley recursion used by
Doron--Pyne--Tell--Williams.
It contains no branching-program model, pseudorandomness theorem, fooling
claim, lower-bound source, or contract wrapper.

The DPTW generator has an `A` block and a `B` block at every level and an
additional packed tail `v`.  Our modification deletes `v` and fixes the
terminal recurrence value to zero.  Consequently the last `B` block is
semantically dead.  The construction deliberately keeps that block, its
primitive coordinate circuit, and its gates: this retains the paper's `A/B`
prefix layout after deleting `v` and makes the exact gate equation below honest.

For `extraLevels + 1` levels, primitive joint-coordinate gate counts `gA` and
`gB`, and primitive seed length `s`, the constructed joint circuit has exactly

`(extraLevels + 1) * (gA + gB) + 5 * extraLevels`

internal gates and exactly `(extraLevels + 1) * (s + s)` seed inputs.  The five
new gates per nonterminal level compute `a XOR (b AND tail)`.  When `0 < n`,
existing constant-free hardwiring then gives a fixed-seed circuit with the
additional exact cost `2 * seedBits`.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped BigOperators

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open StreamingMagnification
open StreamingMagnification.StandardDAG
open StreamingMagnification.TotalSearch

/-- One reusable primitive whose output coordinates are computed by one joint
standard DAG on `(primitiveSeed, truthTableInput)`.

No independence or distributional property is stored here.  Such a property
belongs to the probabilistic analysis, not to this finite locality checkpoint.
-/
structure DPTWCoordinatePrimitive (n seedBits : Nat) where
  generate : FiniteBitTape seedBits -> TruthTable n
  jointCircuit : FlatCircuit (seedBits + n)
  usesOnlyAndOrNot : jointCircuit.UsesOnlyAndOrNot
  jointCircuit_eval : forall seed index,
    jointCircuit.eval (Fin.addCases seed (lexInput n index)) =
      generate seed index

/-! ## The five-gate Boolean head -/

/-- A five-gate constant-free DAG computing `a XOR (b AND tail)`.

Gate zero computes `q = b AND tail`; the remaining four gates implement
`a XOR q = (a OR q) AND NOT (a AND q)`.
-/
def dptwZeroTailLevelHead : DagCircuit 3 where
  gates := 5
  gate := fun i =>
    Fin.cases
      (DagGate.and
        (DagWire.input (1 : Fin 3))
        (DagWire.input (2 : Fin 3)))
      (fun i1 : Fin 4 =>
        Fin.cases
          (DagGate.or
            (DagWire.input (0 : Fin 3))
            (DagWire.gate (0 : Fin 1)))
          (fun i2 : Fin 3 =>
            Fin.cases
              (DagGate.and
                (DagWire.input (0 : Fin 3))
                (DagWire.gate (0 : Fin 2)))
              (fun i3 : Fin 2 =>
                Fin.cases
                  (DagGate.not (DagWire.gate (2 : Fin 3)))
                  (fun i4 : Fin 1 =>
                    Fin.cases
                      (DagGate.and
                        (DagWire.gate (1 : Fin 4))
                        (DagWire.gate (3 : Fin 4)))
                      (fun impossible : Fin 0 => Fin.elim0 impossible)
                      i4)
                  i3)
              i2)
          i1)
      i
  output := DagWire.gate (4 : Fin 5)

@[simp] theorem dptwZeroTailLevelHead_gates :
    dptwZeroTailLevelHead.gates = 5 :=
  rfl

/-- Exact semantics of the five-gate Boolean head. -/
theorem eval_dptwZeroTailLevelHead (a b tail : Bool) :
    DagCircuit.eval dptwZeroTailLevelHead ![a, b, tail] =
      Bool.xor a (b && tail) := by
  let input : Bitstring 3 := ![a, b, tail]
  have hGate0 (h : 0 < dptwZeroTailLevelHead.gates) :
      dptwZeroTailLevelHead.gate ⟨0, h⟩ =
        DagGate.and
          (DagWire.input (1 : Fin 3))
          (DagWire.input (2 : Fin 3)) := by
    rfl
  have hEval0 (h : 0 < dptwZeroTailLevelHead.gates) :
      DagCircuit.eval.evalGateAt
          dptwZeroTailLevelHead input 0 h = (b && tail) := by
    rw [DagCircuit.eval.evalGateAt.eq_1]
    rw [hGate0]
    rfl
  have hGate1 (h : 1 < dptwZeroTailLevelHead.gates) :
      dptwZeroTailLevelHead.gate ⟨1, h⟩ =
        DagGate.or
          (DagWire.input (0 : Fin 3))
          (DagWire.gate (0 : Fin 1)) := by
    rfl
  have hEval1 (h : 1 < dptwZeroTailLevelHead.gates) :
      DagCircuit.eval.evalGateAt
          dptwZeroTailLevelHead input 1 h = (a || (b && tail)) := by
    rw [DagCircuit.eval.evalGateAt.eq_1]
    rw [hGate1]
    change (a || DagCircuit.eval.evalGateAt
      dptwZeroTailLevelHead input 0 _) = _
    rw [hEval0]
  have hGate2 (h : 2 < dptwZeroTailLevelHead.gates) :
      dptwZeroTailLevelHead.gate ⟨2, h⟩ =
        DagGate.and
          (DagWire.input (0 : Fin 3))
          (DagWire.gate (0 : Fin 2)) := by
    rfl
  have hEval2 (h : 2 < dptwZeroTailLevelHead.gates) :
      DagCircuit.eval.evalGateAt
          dptwZeroTailLevelHead input 2 h = (a && (b && tail)) := by
    rw [DagCircuit.eval.evalGateAt.eq_1]
    rw [hGate2]
    change (a && DagCircuit.eval.evalGateAt
      dptwZeroTailLevelHead input 0 _) = _
    rw [hEval0]
  have hGate3 (h : 3 < dptwZeroTailLevelHead.gates) :
      dptwZeroTailLevelHead.gate ⟨3, h⟩ =
        DagGate.not (DagWire.gate (2 : Fin 3)) := by
    rfl
  have hEval3 (h : 3 < dptwZeroTailLevelHead.gates) :
      DagCircuit.eval.evalGateAt
          dptwZeroTailLevelHead input 3 h = !(a && (b && tail)) := by
    rw [DagCircuit.eval.evalGateAt.eq_1]
    rw [hGate3]
    change (!(DagCircuit.eval.evalGateAt
      dptwZeroTailLevelHead input 2 _)) = _
    rw [hEval2]
  have hGate4 (h : 4 < dptwZeroTailLevelHead.gates) :
      dptwZeroTailLevelHead.gate ⟨4, h⟩ =
        DagGate.and
          (DagWire.gate (1 : Fin 4))
          (DagWire.gate (3 : Fin 4)) := by
    rfl
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt
    dptwZeroTailLevelHead input 4 _ = _
  rw [DagCircuit.eval.evalGateAt.eq_1]
  rw [hGate4]
  change
    (DagCircuit.eval.evalGateAt dptwZeroTailLevelHead input 1 _ &&
      DagCircuit.eval.evalGateAt dptwZeroTailLevelHead input 3 _) = _
  rw [hEval1, hEval3]
  cases a <;> cases b <;> cases tail <;> rfl

/-- The five-gate head contains no constant gate. -/
theorem dptwZeroTailLevelHead_noConst :
    forall gate, noConstDAGGate (dptwZeroTailLevelHead.gate gate) := by
  intro gate
  fin_cases gate <;> trivial

/-! ## Seed layout and input relabellings -/

/-- The first `A` seed block in the retained DPTW `A/B` level layout. -/
def dptwFirstASeed
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s))) :
    FiniteBitTape s :=
  fun index => seed <| Fin.mk index.val <| by
    have hPositive : 0 < levelsAfterFirst + 1 := Nat.succ_pos _
    have hBlock : s <= (levelsAfterFirst + 1) * (s + s) := by
      calc
        s <= s + s := Nat.le_add_right s s
        _ <= (levelsAfterFirst + 1) * (s + s) := by
          simpa only [Nat.one_mul] using
            Nat.mul_le_mul_right (s + s) hPositive
    omega

/-- The first `B` seed block in the retained DPTW `A/B` level layout. -/
def dptwFirstBSeed
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s))) :
    FiniteBitTape s :=
  fun index => seed <| Fin.mk (s + index.val) <| by
    have hPositive : 0 < levelsAfterFirst + 1 := Nat.succ_pos _
    have hBlock : s + s <= (levelsAfterFirst + 1) * (s + s) := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (s + s) hPositive
    omega

/-- Remove the first pair of seed blocks.  This is used only when another
level remains after the current one. -/
def dptwTailSeed
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s))) :
    FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) :=
  fun index => seed <| Fin.mk ((s + s) + index.val) <| by
    have hindex := index.isLt
    simp only [Nat.add_mul, Nat.one_mul] at *
    omega

/-- Relabel one primitive coordinate DAG to the first `A` or `B` seed block
and to the shared truth-table input. -/
def dptwFirstPrimitiveRelabel
    (levelsAfterFirst s n : Nat) (isB : Bool) :
    Fin (s + n) -> Fin (((levelsAfterFirst + 1) * (s + s)) + n) :=
  Fin.addCases
    (fun seedIndex =>
      Fin.castAdd n <| Fin.mk
        ((if isB then s else 0) + seedIndex.val) <| by
          have hPositive : 0 < levelsAfterFirst + 1 := Nat.succ_pos _
          have hBlock : s + s <= (levelsAfterFirst + 1) * (s + s) := by
            simpa only [Nat.one_mul] using
              Nat.mul_le_mul_right (s + s) hPositive
          split <;> omega)
    (fun inputIndex =>
      Fin.natAdd ((levelsAfterFirst + 1) * (s + s)) inputIndex)

/-- Relabel the recursively built tail DAG after the current pair of seed
blocks while preserving the shared truth-table input. -/
def dptwTailRelabel
    (levelsAfterFirst s n : Nat) :
    Fin (((levelsAfterFirst + 1) * (s + s)) + n) ->
      Fin (((levelsAfterFirst + 2) * (s + s)) + n) :=
  Fin.addCases
    (fun seedIndex =>
      Fin.castAdd n <| Fin.mk ((s + s) + seedIndex.val) <| by
        have hindex := seedIndex.isLt
        simp only [Nat.add_mul, Nat.one_mul] at *
        omega)
    (fun inputIndex =>
      Fin.natAdd ((levelsAfterFirst + 2) * (s + s)) inputIndex)

/-- Three circuits substituted into the inputs `(a,b,tail)` of the five-gate
head. -/
def dptwZeroTailHeadInputs {m : Nat}
    (a b tail : DagCircuit m) : Fin 3 -> DagCircuit m :=
  fun input =>
    Fin.cases a
      (fun rest : Fin 2 => Fin.cases b (fun _ : Fin 1 => tail) rest)
      input

@[simp] theorem dptwZeroTailHeadInputs_zero {m : Nat}
    (a b tail : DagCircuit m) :
    dptwZeroTailHeadInputs a b tail (0 : Fin 3) = a :=
  rfl

@[simp] theorem dptwZeroTailHeadInputs_one {m : Nat}
    (a b tail : DagCircuit m) :
    dptwZeroTailHeadInputs a b tail (1 : Fin 3) = b :=
  rfl

@[simp] theorem dptwZeroTailHeadInputs_two {m : Nat}
    (a b tail : DagCircuit m) :
    dptwZeroTailHeadInputs a b tail (2 : Fin 3) = tail :=
  rfl

theorem sum_dptwZeroTailHeadInputs_gates {m : Nat}
    (a b tail : DagCircuit m) :
    (∑ input : Fin 3,
      (dptwZeroTailHeadInputs a b tail input).gates) =
      a.gates + b.gates + tail.gates := by
  simp [dptwZeroTailHeadInputs, Fin.sum_univ_succ, Nat.add_assoc]

/-! ## Our zero-tail modification and its joint DAG -/

/-- Our zero-tail modification with `levelsAfterFirst + 1` levels, retaining
the DPTW `A/B` level layout but deleting the paper's packed tail `v`.

At the last level the mathematical expression is `A XOR (B AND false) = A`.
The final `B` seed block is therefore present but semantically unused.
-/
def dptwZeroTailGenerate
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s) :
    (levelsAfterFirst : Nat) ->
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) -> TruthTable n
  | 0, seed => a.generate (dptwFirstASeed seed)
  | levelsAfterFirst + 1, seed => fun index =>
      Bool.xor
        (a.generate (dptwFirstASeed seed) index)
        (b.generate (dptwFirstBSeed seed) index &&
          dptwZeroTailGenerate a b levelsAfterFirst
            (dptwTailSeed seed) index)

/-- At the final level the recursion is exactly `A`: the retained final `B`
seed block is semantically dead because the mathematical tail is zero. -/
@[simp] theorem dptwZeroTailGenerate_final
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (seed : FiniteBitTape (1 * (s + s))) :
    dptwZeroTailGenerate a b 0 seed =
      a.generate (dptwFirstASeed seed) :=
  rfl

/-- Public equation for one nonterminal recursion level. -/
@[simp] theorem dptwZeroTailGenerate_step
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (index : Fin (2 ^ n)) :
    dptwZeroTailGenerate a b (levelsAfterFirst + 1) seed index =
      Bool.xor
        (a.generate (dptwFirstASeed seed) index)
        (b.generate (dptwFirstBSeed seed) index &&
          dptwZeroTailGenerate a b levelsAfterFirst
            (dptwTailSeed seed) index) :=
  rfl

/-- Primitive `A` coordinate DAG at the first seed block. -/
def dptwFirstACircuit
    {n s : Nat} (a : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    DagCircuit (((levelsAfterFirst + 1) * (s + s)) + n) :=
  relabelInputs
    (dptwFirstPrimitiveRelabel levelsAfterFirst s n false)
    a.jointCircuit.toDag

/-- Primitive `B` coordinate DAG at the first seed block. -/
def dptwFirstBCircuit
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    DagCircuit (((levelsAfterFirst + 1) * (s + s)) + n) :=
  relabelInputs
    (dptwFirstPrimitiveRelabel levelsAfterFirst s n true)
    b.jointCircuit.toDag

/-- Joint coordinate DAG for the modified recursion with
`levelsAfterFirst + 1` positive levels.

The base uses `appendOutputLeft A B`: it returns `A`, as required by the zero
tail, but deliberately retains and counts the dead final `B` circuit.
-/
def dptwZeroTailJointDAG
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s) :
    (levelsAfterFirst : Nat) ->
      DagCircuit (((levelsAfterFirst + 1) * (s + s)) + n)
  | 0 => appendOutputLeft (dptwFirstACircuit a 0) (dptwFirstBCircuit b 0)
  | levelsAfterFirst + 1 =>
      substInputs dptwZeroTailLevelHead <|
        dptwZeroTailHeadInputs
          (dptwFirstACircuit a (levelsAfterFirst + 1))
          (dptwFirstBCircuit b (levelsAfterFirst + 1))
          (relabelInputs (dptwTailRelabel levelsAfterFirst s n)
            (dptwZeroTailJointDAG a b levelsAfterFirst))

/-- Flat standard-DAG presentation of the joint zero-tail coordinate circuit. -/
def dptwZeroTailJointCircuit
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    FlatCircuit (((levelsAfterFirst + 1) * (s + s)) + n) :=
  FlatCircuit.ofDag (dptwZeroTailJointDAG a b levelsAfterFirst)

/-! ## Exact gate count -/

@[simp] theorem dptwFirstACircuit_gates
    {n s : Nat} (a : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    (dptwFirstACircuit a levelsAfterFirst).gates =
      a.jointCircuit.gateCount :=
  rfl

@[simp] theorem dptwFirstBCircuit_gates
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    (dptwFirstBCircuit b levelsAfterFirst).gates =
      b.jointCircuit.gateCount :=
  rfl

@[simp] theorem dptwTailRelabel_gates
    {n levelsAfterFirst s : Nat}
    (circuit : DagCircuit (((levelsAfterFirst + 1) * (s + s)) + n)) :
    (relabelInputs (dptwTailRelabel levelsAfterFirst s n) circuit).gates =
      circuit.gates :=
  rfl

/-- Exact internal-gate equation.  The summand for `B` occurs once per level,
including the semantically dead final `B` primitive. -/
theorem dptwZeroTailJointDAG_gates
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    (dptwZeroTailJointDAG a b levelsAfterFirst).gates =
      (levelsAfterFirst + 1) *
          (a.jointCircuit.gateCount + b.jointCircuit.gateCount) +
        5 * levelsAfterFirst := by
  induction levelsAfterFirst with
  | zero =>
      simp [dptwZeroTailJointDAG, appendOutputLeft]
  | succ levelsAfterFirst ih =>
      simp only [dptwZeroTailJointDAG]
      change
        (bundleOfFamily 3
          (dptwZeroTailHeadInputs
            (dptwFirstACircuit a (levelsAfterFirst + 1))
            (dptwFirstBCircuit b (levelsAfterFirst + 1))
            (relabelInputs (dptwTailRelabel levelsAfterFirst s n)
              (dptwZeroTailJointDAG a b levelsAfterFirst)))).gates +
            dptwZeroTailLevelHead.gates = _
      rw [bundleOfFamily_gates, sum_dptwZeroTailHeadInputs_gates]
      simp only [dptwFirstACircuit_gates, dptwFirstBCircuit_gates,
        dptwTailRelabel_gates, dptwZeroTailLevelHead_gates, ih]
      ring

/-- Exact gate count in the flat standard-DAG presentation. -/
theorem dptwZeroTailJointCircuit_gateCount
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    (dptwZeroTailJointCircuit a b levelsAfterFirst).gateCount =
      (levelsAfterFirst + 1) *
          (a.jointCircuit.gateCount + b.jointCircuit.gateCount) +
        5 * levelsAfterFirst := by
  exact dptwZeroTailJointDAG_gates a b levelsAfterFirst

/-! ## Evaluation -/

/-- Evaluation of the first `A` primitive after seed/input relabelling. -/
theorem eval_dptwFirstACircuit
    {n s : Nat} (a : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (input : Bitstring n) :
    DagCircuit.eval (dptwFirstACircuit a levelsAfterFirst)
        (Fin.addCases seed input) =
      a.jointCircuit.eval
        (Fin.addCases (dptwFirstASeed seed) input) := by
  rw [dptwFirstACircuit, eval_relabelInputs]
  change a.jointCircuit.eval _ = a.jointCircuit.eval _
  apply congrArg a.jointCircuit.eval
  funext primitiveInput
  refine Fin.addCases
    (motive := fun primitiveInput : Fin (s + n) =>
      (Fin.addCases seed input :
          Bitstring (((levelsAfterFirst + 1) * (s + s)) + n))
          (dptwFirstPrimitiveRelabel levelsAfterFirst s n false
            primitiveInput) =
        (Fin.addCases (dptwFirstASeed seed) input : Bitstring (s + n))
          primitiveInput)
    (fun seedInput => by
      simp only [dptwFirstPrimitiveRelabel, Fin.addCases_left,
        Bool.false_eq_true, if_false, dptwFirstASeed]
      apply congrArg seed
      apply Fin.ext
      simp)
    (fun tableInput => by
      simp [dptwFirstPrimitiveRelabel])
    primitiveInput

/-- Evaluation of the first `B` primitive after seed/input relabelling. -/
theorem eval_dptwFirstBCircuit
    {n s : Nat} (b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (input : Bitstring n) :
    DagCircuit.eval (dptwFirstBCircuit b levelsAfterFirst)
        (Fin.addCases seed input) =
      b.jointCircuit.eval
        (Fin.addCases (dptwFirstBSeed seed) input) := by
  rw [dptwFirstBCircuit, eval_relabelInputs]
  change b.jointCircuit.eval _ = b.jointCircuit.eval _
  apply congrArg b.jointCircuit.eval
  funext primitiveInput
  refine Fin.addCases
    (motive := fun primitiveInput : Fin (s + n) =>
      (Fin.addCases seed input :
          Bitstring (((levelsAfterFirst + 1) * (s + s)) + n))
          (dptwFirstPrimitiveRelabel levelsAfterFirst s n true
            primitiveInput) =
        (Fin.addCases (dptwFirstBSeed seed) input : Bitstring (s + n))
          primitiveInput)
    (fun seedInput => by
      simp only [dptwFirstPrimitiveRelabel, Fin.addCases_left,
        dptwFirstBSeed]
      apply congrArg seed
      apply Fin.ext
      simp)
    (fun tableInput => by
      simp [dptwFirstPrimitiveRelabel])
    primitiveInput

/-- Evaluation of a recursively built tail after moving it behind the current
pair of seed blocks. -/
theorem eval_dptwTailRelabel
    {n s levelsAfterFirst : Nat}
    (circuit : DagCircuit (((levelsAfterFirst + 1) * (s + s)) + n))
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s)))
    (input : Bitstring n) :
    DagCircuit.eval
        (relabelInputs (dptwTailRelabel levelsAfterFirst s n) circuit)
        (Fin.addCases seed input) =
      DagCircuit.eval circuit (Fin.addCases (dptwTailSeed seed) input) := by
  rw [eval_relabelInputs]
  apply congrArg (DagCircuit.eval circuit)
  funext tailInput
  refine Fin.addCases
    (motive := fun tailInput :
        Fin (((levelsAfterFirst + 1) * (s + s)) + n) =>
      (Fin.addCases seed input :
          Bitstring (((levelsAfterFirst + 2) * (s + s)) + n))
          (dptwTailRelabel levelsAfterFirst s n tailInput) =
        (Fin.addCases (dptwTailSeed seed) input :
          Bitstring (((levelsAfterFirst + 1) * (s + s)) + n)) tailInput)
    (fun seedInput => by
      simp only [dptwTailRelabel, Fin.addCases_left, dptwTailSeed])
    (fun tableInput => by
      simp [dptwTailRelabel])
    tailInput

/-- Exact coordinate semantics of the modified zero-tail joint DAG. -/
theorem eval_dptwZeroTailJointDAG
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (index : Fin (2 ^ n)) :
    DagCircuit.eval (dptwZeroTailJointDAG a b levelsAfterFirst)
        (Fin.addCases seed (lexInput n index)) =
      dptwZeroTailGenerate a b levelsAfterFirst seed index := by
  induction levelsAfterFirst with
  | zero =>
      rw [dptwZeroTailJointDAG, eval_appendOutputLeft]
      rw [eval_dptwFirstACircuit]
      exact a.jointCircuit_eval (dptwFirstASeed seed) index
  | succ levelsAfterFirst ih =>
      rw [dptwZeroTailJointDAG, eval_substInputs]
      let input : Bitstring (((levelsAfterFirst + 2) * (s + s)) + n) :=
        Fin.addCases seed (lexInput n index)
      have hInputs :
          (fun headInput : Fin 3 =>
            DagCircuit.eval
              (dptwZeroTailHeadInputs
                (dptwFirstACircuit a (levelsAfterFirst + 1))
                (dptwFirstBCircuit b (levelsAfterFirst + 1))
                (relabelInputs (dptwTailRelabel levelsAfterFirst s n)
                  (dptwZeroTailJointDAG a b levelsAfterFirst))
                headInput)
              input) =
            ![
              a.generate (dptwFirstASeed seed) index,
              b.generate (dptwFirstBSeed seed) index,
              dptwZeroTailGenerate a b levelsAfterFirst
                (dptwTailSeed seed) index
            ] := by
        funext headInput
        fin_cases headInput
        · change DagCircuit.eval
            (dptwFirstACircuit a (levelsAfterFirst + 1)) input = _
          rw [eval_dptwFirstACircuit]
          exact a.jointCircuit_eval (dptwFirstASeed seed) index
        · change DagCircuit.eval
            (dptwFirstBCircuit b (levelsAfterFirst + 1)) input = _
          rw [eval_dptwFirstBCircuit]
          exact b.jointCircuit_eval (dptwFirstBSeed seed) index
        · change DagCircuit.eval
            (relabelInputs (dptwTailRelabel levelsAfterFirst s n)
              (dptwZeroTailJointDAG a b levelsAfterFirst)) input = _
          rw [eval_dptwTailRelabel]
          exact ih (dptwTailSeed seed)
      rw [hInputs, eval_dptwZeroTailLevelHead]
      rfl

/-- Exact coordinate semantics in the flat standard-DAG presentation. -/
theorem dptwZeroTailJointCircuit_eval
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (index : Fin (2 ^ n)) :
    (dptwZeroTailJointCircuit a b levelsAfterFirst).eval
        (Fin.addCases seed (lexInput n index)) =
      dptwZeroTailGenerate a b levelsAfterFirst seed index := by
  unfold dptwZeroTailJointCircuit FlatCircuit.eval
  rw [FlatCircuit.toDag_ofDag]
  exact eval_dptwZeroTailJointDAG a b levelsAfterFirst seed index

/-! ## Constant-free AND/OR/NOT basis -/

/-- Input relabelling cannot introduce a constant gate. -/
lemma noConst_mapGateInputs
    {n m k : Nat} (relabel : Fin n -> Fin m)
    (gate : DagGate n k) (hGate : noConstDAGGate gate) :
    noConstDAGGate (mapGateInputs relabel gate) := by
  cases gate <;> trivial

/-- A constant-free DAG remains constant-free after input relabelling. -/
lemma relabelInputs_noConst
    {n m : Nat} (relabel : Fin n -> Fin m) (circuit : DagCircuit n)
    (hCircuit : forall gate, noConstDAGGate (circuit.gate gate)) :
    forall gate,
      noConstDAGGate ((relabelInputs relabel circuit).gate gate) := by
  intro gate
  exact noConst_mapGateInputs relabel (circuit.gate gate) (hCircuit gate)

/-- Appending a second constant-free gate list while retaining the first output
preserves constant-freeness. -/
lemma appendOutputLeft_noConst
    {n : Nat} (left right : DagCircuit n)
    (hLeft : forall gate, noConstDAGGate (left.gate gate))
    (hRight : forall gate, noConstDAGGate (right.gate gate)) :
    forall gate,
      noConstDAGGate ((appendOutputLeft left right).gate gate) := by
  intro gate
  refine Fin.addCases
    (motive := fun gate =>
      noConstDAGGate ((appendOutputLeft left right).gate gate))
    (fun leftGate => by
      simpa only [appendOutputLeft, appendGate_left] using hLeft leftGate)
    (fun rightGate => by
      have hShifted := noConst_shiftGateBy left.gates
        (right.gate rightGate) (hRight rightGate)
      simpa only [appendOutputLeft, appendGate_right] using hShifted)
    gate

/-- The recursively assembled joint DAG is constant-free whenever both
primitive joint-coordinate DAGs use the constant-free paper basis. -/
theorem dptwZeroTailJointDAG_noConst
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    forall gate,
      noConstDAGGate
        ((dptwZeroTailJointDAG a b levelsAfterFirst).gate gate) := by
  induction levelsAfterFirst with
  | zero =>
      apply appendOutputLeft_noConst
      · apply relabelInputs_noConst
        exact toDag_noConst_of_usesOnlyAndOrNot
          a.jointCircuit a.usesOnlyAndOrNot
      · apply relabelInputs_noConst
        exact toDag_noConst_of_usesOnlyAndOrNot
          b.jointCircuit b.usesOnlyAndOrNot
  | succ levelsAfterFirst ih =>
      apply substInputs_noConst
      · exact dptwZeroTailLevelHead_noConst
      · intro input gate
        fin_cases input
        · apply relabelInputs_noConst
          exact toDag_noConst_of_usesOnlyAndOrNot
            a.jointCircuit a.usesOnlyAndOrNot
        · apply relabelInputs_noConst
          exact toDag_noConst_of_usesOnlyAndOrNot
            b.jointCircuit b.usesOnlyAndOrNot
        · apply relabelInputs_noConst
          exact ih

/-- The joint flat circuit uses only the constant-free AND/OR/NOT basis. -/
theorem dptwZeroTailJointCircuit_usesOnlyAndOrNot
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    (dptwZeroTailJointCircuit a b levelsAfterFirst).UsesOnlyAndOrNot := by
  apply ofDag_usesOnlyAndOrNot_of_noConst
  exact dptwZeroTailJointDAG_noConst a b levelsAfterFirst

/-! ## Exact hardwiring cost and `DAGLocalGenerator` wrapper -/

/-- Specialization of the existing constant-free hardwiring theorem.  Besides
the modified joint gates (including the dead final `B` circuit), fixing a
seed costs exactly two internal gates per seed bit. -/
theorem dptwZeroTailHardwired_gateCount
    {n s : Nat} (hPositive : 0 < n)
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s))) :
    (hardwireSeedCircuit hPositive
      (dptwZeroTailJointCircuit a b levelsAfterFirst) seed).gateCount =
      (levelsAfterFirst + 1) *
          (a.jointCircuit.gateCount + b.jointCircuit.gateCount) +
        5 * levelsAfterFirst +
        2 * ((levelsAfterFirst + 1) * (s + s)) := by
  rw [hardwireSeedCircuit_gateCount,
    dptwZeroTailJointCircuit_gateCount]

/-- The modified zero-tail joint circuit, hardwired by the existing exact
builder, as a `DAGLocalGenerator` at its explicit internal-gate threshold.

The only positivity premise is the one already required by constant-free seed
hardwiring: the fixed-seed output circuit needs a real input `x_0` from which
to synthesize Boolean constants.
-/
def dptwZeroTailDAGLocalGenerator
    {n s : Nat} (hPositive : 0 < n)
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    DAGLocalGenerator n
      ((dptwZeroTailJointCircuit a b levelsAfterFirst).gateCount +
        2 * ((levelsAfterFirst + 1) * (s + s))) := by
  exact dagLocalGeneratorOfJointCircuit hPositive
    (dptwZeroTailJointCircuit a b levelsAfterFirst)
    (dptwZeroTailJointCircuit_usesOnlyAndOrNot
      a b levelsAfterFirst)

/-- Closed form of the wrapper's threshold parameter. -/
theorem dptwZeroTailDAGLocalGenerator_threshold_eq
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    (dptwZeroTailJointCircuit a b levelsAfterFirst).gateCount +
        2 * ((levelsAfterFirst + 1) * (s + s)) =
      (levelsAfterFirst + 1) *
          (a.jointCircuit.gateCount + b.jointCircuit.gateCount) +
        5 * levelsAfterFirst +
        2 * ((levelsAfterFirst + 1) * (s + s)) := by
  rw [dptwZeroTailJointCircuit_gateCount]

@[simp] theorem dptwZeroTailDAGLocalGenerator_seedBits
    {n s : Nat} (hPositive : 0 < n)
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    (dptwZeroTailDAGLocalGenerator hPositive
      a b levelsAfterFirst).seedBits =
      (levelsAfterFirst + 1) * (s + s) := by
  rfl

/-- The wrapper's generator is pointwise exactly our zero-tail recursion,
rather than merely extensionally equidistributed with it. -/
theorem dptwZeroTailDAGLocalGenerator_generate
    {n s : Nat} (hPositive : 0 < n)
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s))) :
    (dptwZeroTailDAGLocalGenerator hPositive
      a b levelsAfterFirst).generate seed =
        dptwZeroTailGenerate a b levelsAfterFirst seed := by
  funext index
  exact dptwZeroTailJointCircuit_eval
    a b levelsAfterFirst seed index

end OneTapeMagnification
end Frontier
end Pnp4
