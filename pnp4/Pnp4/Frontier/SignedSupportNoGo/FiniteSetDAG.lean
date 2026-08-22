import Pnp4.Frontier.SignedSupportNoGo.FiniteSignedSupport

/-!
# Explicit DAG avoidance of a finite set

For any finite set of `N`-bit strings, this module constructs a standard
fan-in-two `DagCircuit` accepting exactly its complement.  The construction
uses only `inputProj`, `constCircuit`, and `substInputs` from the current
`Complexity.DagCompose` layer.
-/

namespace Pnp4.Frontier.SignedSupportNoGo

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

private def unaryNotDAG : DagCircuit 1 where
  gates := 1
  gate := fun _ => DagGate.not (DagWire.input (0 : Fin 1))
  output := DagWire.gate (0 : Fin 1)

private def binaryAndDAG : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.and
    (DagWire.input (0 : Fin 2)) (DagWire.input (1 : Fin 2))
  output := DagWire.gate (0 : Fin 1)

private def binaryOrDAG : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.or
    (DagWire.input (0 : Fin 2)) (DagWire.input (1 : Fin 2))
  output := DagWire.gate (0 : Fin 1)

@[simp] private theorem eval_unaryNotDAG (input : Bitstring 1) :
    eval unaryNotDAG input = !input 0 := by
  simp [unaryNotDAG, eval, eval.evalGateAt]

@[simp] private theorem eval_binaryAndDAG (input : Bitstring 2) :
    eval binaryAndDAG input = (input 0 && input 1) := by
  simp [binaryAndDAG, eval, eval.evalGateAt]

@[simp] private theorem eval_binaryOrDAG (input : Bitstring 2) :
    eval binaryOrDAG input = (input 0 || input 1) := by
  simp [binaryOrDAG, eval, eval.evalGateAt]

private def dagNot {N : Nat} (circuit : DagCircuit N) : DagCircuit N :=
  substInputs unaryNotDAG (fun _ => circuit)

private def dagAnd {N : Nat}
    (left right : DagCircuit N) : DagCircuit N :=
  substInputs binaryAndDAG (fun index =>
    if index = (0 : Fin 2) then left else right)

private def dagOr {N : Nat}
    (left right : DagCircuit N) : DagCircuit N :=
  substInputs binaryOrDAG (fun index =>
    if index = (0 : Fin 2) then left else right)

@[simp] private theorem eval_dagNot {N : Nat}
    (circuit : DagCircuit N) (input : Bitstring N) :
    eval (dagNot circuit) input = !eval circuit input := by
  simp [dagNot]

@[simp] private theorem eval_dagAnd {N : Nat}
    (left right : DagCircuit N) (input : Bitstring N) :
    eval (dagAnd left right) input =
      (eval left input && eval right input) := by
  simp [dagAnd]

@[simp] private theorem eval_dagOr {N : Nat}
    (left right : DagCircuit N) (input : Bitstring N) :
    eval (dagOr left right) input =
      (eval left input || eval right input) := by
  simp [dagOr]

@[simp] private theorem gates_dagNot {N : Nat}
    (circuit : DagCircuit N) :
    (dagNot circuit).gates = circuit.gates + 1 := by
  simp [dagNot, substInputs, substInputsWithBundle,
    bundleOfFamily_gates, unaryNotDAG]

@[simp] private theorem gates_dagAnd {N : Nat}
    (left right : DagCircuit N) :
    (dagAnd left right).gates = left.gates + right.gates + 1 := by
  simp [dagAnd, substInputs, substInputsWithBundle,
    bundleOfFamily_gates, binaryAndDAG, Fin.sum_univ_two]

@[simp] private theorem gates_dagOr {N : Nat}
    (left right : DagCircuit N) :
    (dagOr left right).gates = left.gates + right.gates + 1 := by
  simp [dagOr, substInputs, substInputsWithBundle,
    bundleOfFamily_gates, binaryOrDAG, Fin.sum_univ_two]

private def dagAndList {N : Nat} : List (DagCircuit N) → DagCircuit N
  | [] => constCircuit N true
  | circuit :: circuits => dagAnd circuit (dagAndList circuits)

private def dagOrList {N : Nat} : List (DagCircuit N) → DagCircuit N
  | [] => constCircuit N false
  | circuit :: circuits => dagOr circuit (dagOrList circuits)

@[simp] private theorem eval_dagAndList {N : Nat}
    (circuits : List (DagCircuit N)) (input : Bitstring N) :
    eval (dagAndList circuits) input =
      circuits.all (fun circuit => eval circuit input) := by
  induction circuits with
  | nil => simp [dagAndList]
  | cons circuit circuits ih => simp [dagAndList, ih]

@[simp] private theorem eval_dagOrList {N : Nat}
    (circuits : List (DagCircuit N)) (input : Bitstring N) :
    eval (dagOrList circuits) input =
      circuits.any (fun circuit => eval circuit input) := by
  induction circuits with
  | nil => simp [dagOrList]
  | cons circuit circuits ih => simp [dagOrList, ih]

private theorem gates_dagAndList_le
    {N gateBound : Nat} (circuits : List (DagCircuit N))
    (hGate : ∀ circuit, circuit ∈ circuits →
      circuit.gates ≤ gateBound) :
    (dagAndList circuits).gates ≤
      circuits.length * (gateBound + 1) + 1 := by
  induction circuits with
  | nil => simp [dagAndList, constCircuit]
  | cons circuit circuits ih =>
      simp only [dagAndList, gates_dagAnd, List.length_cons]
      have hHead : circuit.gates ≤ gateBound := hGate circuit (by simp)
      have hTail : (dagAndList circuits).gates ≤
          circuits.length * (gateBound + 1) + 1 := by
        apply ih
        intro other hOther
        exact hGate other (by simp [hOther])
      calc
        circuit.gates + (dagAndList circuits).gates + 1 ≤
            gateBound + (circuits.length * (gateBound + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hHead hTail) 1
        _ = (circuits.length + 1) * (gateBound + 1) + 1 := by ring

private theorem gates_dagOrList_le
    {N gateBound : Nat} (circuits : List (DagCircuit N))
    (hGate : ∀ circuit, circuit ∈ circuits →
      circuit.gates ≤ gateBound) :
    (dagOrList circuits).gates ≤
      circuits.length * (gateBound + 1) + 1 := by
  induction circuits with
  | nil => simp [dagOrList, constCircuit]
  | cons circuit circuits ih =>
      simp only [dagOrList, gates_dagOr, List.length_cons]
      have hHead : circuit.gates ≤ gateBound := hGate circuit (by simp)
      have hTail : (dagOrList circuits).gates ≤
          circuits.length * (gateBound + 1) + 1 := by
        apply ih
        intro other hOther
        exact hGate other (by simp [hOther])
      calc
        circuit.gates + (dagOrList circuits).gates + 1 ≤
            gateBound + (circuits.length * (gateBound + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hHead hTail) 1
        _ = (circuits.length + 1) * (gateBound + 1) + 1 := by ring

private def literalDAG {N : Nat}
    (table : Bitstring N) (index : Fin N) : DagCircuit N :=
  if table index then inputProj index else dagNot (inputProj index)

@[simp] private theorem eval_literalDAG {N : Nat}
    (table input : Bitstring N) (index : Fin N) :
    eval (literalDAG table index) input =
      decide (input index = table index) := by
  cases hTable : table index <;> cases hInput : input index <;>
    simp [literalDAG, hTable, hInput]

private theorem gates_literalDAG_le_one {N : Nat}
    (table : Bitstring N) (index : Fin N) :
    (literalDAG table index).gates ≤ 1 := by
  cases hTable : table index <;> simp [literalDAG, hTable, inputProj]

/-- A standard DAG recognizing one explicitly given `N`-bit string. -/
def equalsTableDAG {N : Nat} (table : Bitstring N) : DagCircuit N :=
  dagAndList (List.ofFn fun index : Fin N => literalDAG table index)

@[simp] theorem eval_equalsTableDAG {N : Nat}
    (table input : Bitstring N) :
    eval (equalsTableDAG table) input = decide (input = table) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [equalsTableDAG, eval_dagAndList, List.all_eq_true,
    List.mem_ofFn, decide_eq_true_eq]
  constructor
  · intro h
    funext index
    have hLiteral := h (literalDAG table index) ⟨index, rfl⟩
    exact of_decide_eq_true (by simpa using hLiteral)
  · intro h circuit
    rintro ⟨index, rfl⟩
    rw [eval_literalDAG]
    exact decide_eq_true (congrFun h index)

/-- Gate bound for equality.  The public `DagCircuit.size` bound is one larger. -/
theorem gates_equalsTableDAG_le {N : Nat} (table : Bitstring N) :
    (equalsTableDAG table).gates ≤ 2 * N + 1 := by
  unfold equalsTableDAG
  have hBound := gates_dagAndList_le
    (gateBound := 1)
    (List.ofFn fun index : Fin N => literalDAG table index)
  have hEach : ∀ circuit,
      circuit ∈ (List.ofFn fun index : Fin N => literalDAG table index) →
      circuit.gates ≤ 1 := by
    intro circuit hCircuit
    rcases List.mem_ofFn.mp hCircuit with ⟨index, rfl⟩
    exact gates_literalDAG_le_one table index
  simpa [Nat.mul_comm] using hBound hEach

/-- A computable standard DAG accepting exactly the complement of a list of
forbidden strings.  This is the executable core; duplicate list entries are harmless. -/
def avoidListDAG {N : Nat}
    (forbidden : List (Bitstring N)) : DagCircuit N :=
  dagNot <| dagOrList <| forbidden.map equalsTableDAG

@[simp] theorem eval_avoidListDAG {N : Nat}
    (forbidden : List (Bitstring N)) (input : Bitstring N) :
    eval (avoidListDAG forbidden) input = decide (input ∉ forbidden) := by
  classical
  by_cases hMem : input ∈ forbidden
  · have hAny :
        (forbidden.map equalsTableDAG).any
            (fun circuit => eval circuit input) = true := by
      rw [List.any_eq_true]
      refine ⟨equalsTableDAG input, ?_, by simp⟩
      exact List.mem_map.mpr ⟨input, hMem, rfl⟩
    simp [avoidListDAG, hAny, hMem]
  · have hAny :
        (forbidden.map equalsTableDAG).any
            (fun circuit => eval circuit input) = false := by
      rw [List.any_eq_false]
      intro circuit hCircuit
      rcases List.mem_map.mp hCircuit with ⟨table, hTable, rfl⟩
      have hNe : input ≠ table := by
        intro hEq
        subst table
        exact hMem hTable
      simp [hNe]
    simp [avoidListDAG, hAny, hMem]

/-- Explicit size bound for the computable list constructor. -/
theorem size_avoidListDAG_le {N : Nat}
    (forbidden : List (Bitstring N)) :
    size (avoidListDAG forbidden) ≤ forbidden.length * (2 * N + 2) + 3 := by
  unfold avoidListDAG
  rw [size, gates_dagNot]
  have hOr := gates_dagOrList_le
    (gateBound := 2 * N + 1) (forbidden.map equalsTableDAG)
  have hEach : ∀ circuit,
      circuit ∈ forbidden.map equalsTableDAG → circuit.gates ≤ 2 * N + 1 := by
    intro circuit hCircuit
    rcases List.mem_map.mp hCircuit with ⟨table, _, rfl⟩
    exact gates_equalsTableDAG_le table
  have hBound := hOr hEach
  simp only [List.length_map] at hBound
  have hFactor : 2 * N + 1 + 1 = 2 * N + 2 := by omega
  rw [hFactor] at hBound
  omega

/-- Order-insensitive wrapper around the computable list constructor.  It is
noncomputable only because `Finset.toList` has no canonical order. -/
noncomputable def avoidFiniteSetDAG {N : Nat}
    (forbidden : Finset (Bitstring N)) : DagCircuit N :=
  avoidListDAG forbidden.toList

@[simp] theorem eval_avoidFiniteSetDAG {N : Nat}
    (forbidden : Finset (Bitstring N)) (input : Bitstring N) :
    eval (avoidFiniteSetDAG forbidden) input = decide (input ∉ forbidden) := by
  classical
  simp [avoidFiniteSetDAG]

/-- Explicit size bound, linear in `N` times the number of forbidden strings. -/
theorem size_avoidFiniteSetDAG_le {N : Nat}
    (forbidden : Finset (Bitstring N)) :
    size (avoidFiniteSetDAG forbidden) ≤
      forbidden.card * (2 * N + 2) + 3 := by
  classical
  simpa [avoidFiniteSetDAG] using size_avoidListDAG_le forbidden.toList

end Pnp4.Frontier.SignedSupportNoGo
