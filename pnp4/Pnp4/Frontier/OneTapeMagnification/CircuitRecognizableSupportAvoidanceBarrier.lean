import Pnp4.Frontier.OneTapeMagnification.ReverseOneSidedFoolingSupportEquivalence

/-!
# Circuit-recognizable support avoidance

The unrestricted support-avoidance predicate from `SupportAvoidance` is not
merely decidable.  On `N`-bit strings, the complement of any explicit finite
set is recognized by a standard fan-in-two `DagCircuit` of size linear in
`N * |forbidden|`.

Specializing the forbidden set to `Counting.easyTablesByCode n threshold`
gives a concrete obstruction to the dense local-HSG premise.  Once the outer
standard-DAG size bound is large enough to hard-code the whole codec image, a
dense outer predicate rejects every threshold-easy truth table.  This is an
unconditional no-go theorem, not a construction of the missing HSG.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open StreamingMagnification
open StreamingMagnification.TotalSearch
open Counting
open ContractExpansion

/-! ## Small compositional standard-DAG builders -/

private def avoidUnaryNotDAG : DagCircuit 1 where
  gates := 1
  gate := fun _ => DagGate.not (DagWire.input (0 : Fin 1))
  output := DagWire.gate (0 : Fin 1)

private def avoidBinaryAndDAG : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.and
    (DagWire.input (0 : Fin 2)) (DagWire.input (1 : Fin 2))
  output := DagWire.gate (0 : Fin 1)

private def avoidBinaryOrDAG : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.or
    (DagWire.input (0 : Fin 2)) (DagWire.input (1 : Fin 2))
  output := DagWire.gate (0 : Fin 1)

@[simp] private theorem eval_avoidUnaryNotDAG (input : Bitstring 1) :
    eval avoidUnaryNotDAG input = !input 0 := by
  simp [avoidUnaryNotDAG, eval, eval.evalGateAt]

@[simp] private theorem eval_avoidBinaryAndDAG (input : Bitstring 2) :
    eval avoidBinaryAndDAG input = (input 0 && input 1) := by
  simp [avoidBinaryAndDAG, eval, eval.evalGateAt]

@[simp] private theorem eval_avoidBinaryOrDAG (input : Bitstring 2) :
    eval avoidBinaryOrDAG input = (input 0 || input 1) := by
  simp [avoidBinaryOrDAG, eval, eval.evalGateAt]

private def dagNot {N : Nat} (circuit : DagCircuit N) : DagCircuit N :=
  substInputs avoidUnaryNotDAG (fun _ => circuit)

private def dagAnd {N : Nat}
    (left right : DagCircuit N) : DagCircuit N :=
  substInputs avoidBinaryAndDAG (fun index =>
    if index = (0 : Fin 2) then left else right)

private def dagOr {N : Nat}
    (left right : DagCircuit N) : DagCircuit N :=
  substInputs avoidBinaryOrDAG (fun index =>
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
    bundleOfFamily_gates, avoidUnaryNotDAG]

@[simp] private theorem gates_dagAnd {N : Nat}
    (left right : DagCircuit N) :
    (dagAnd left right).gates = left.gates + right.gates + 1 := by
  simp [dagAnd, substInputs, substInputsWithBundle,
    bundleOfFamily_gates, avoidBinaryAndDAG, Fin.sum_univ_two]

@[simp] private theorem gates_dagOr {N : Nat}
    (left right : DagCircuit N) :
    (dagOr left right).gates = left.gates + right.gates + 1 := by
  simp [dagOr, substInputs, substInputsWithBundle,
    bundleOfFamily_gates, avoidBinaryOrDAG, Fin.sum_univ_two]

private def dagAndList {N : Nat} : List (DagCircuit N) -> DagCircuit N
  | [] => constCircuit N true
  | circuit :: circuits => dagAnd circuit (dagAndList circuits)

private def dagOrList {N : Nat} : List (DagCircuit N) -> DagCircuit N
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
    (hGate : forall circuit, circuit ∈ circuits ->
      circuit.gates <= gateBound) :
    (dagAndList circuits).gates <=
      circuits.length * (gateBound + 1) + 1 := by
  induction circuits with
  | nil => simp [dagAndList, constCircuit]
  | cons circuit circuits ih =>
      simp only [dagAndList, gates_dagAnd, List.length_cons]
      have hHead : circuit.gates <= gateBound := hGate circuit (by simp)
      have hTail : (dagAndList circuits).gates <=
          circuits.length * (gateBound + 1) + 1 := by
        apply ih
        intro other hOther
        exact hGate other (by simp [hOther])
      calc
        circuit.gates + (dagAndList circuits).gates + 1 <=
            gateBound +
                (circuits.length * (gateBound + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hHead hTail) 1
        _ = (circuits.length + 1) * (gateBound + 1) + 1 := by
          ring

private theorem gates_dagOrList_le
    {N gateBound : Nat} (circuits : List (DagCircuit N))
    (hGate : forall circuit, circuit ∈ circuits ->
      circuit.gates <= gateBound) :
    (dagOrList circuits).gates <=
      circuits.length * (gateBound + 1) + 1 := by
  induction circuits with
  | nil => simp [dagOrList, constCircuit]
  | cons circuit circuits ih =>
      simp only [dagOrList, gates_dagOr, List.length_cons]
      have hHead : circuit.gates <= gateBound := hGate circuit (by simp)
      have hTail : (dagOrList circuits).gates <=
          circuits.length * (gateBound + 1) + 1 := by
        apply ih
        intro other hOther
        exact hGate other (by simp [hOther])
      calc
        circuit.gates + (dagOrList circuits).gates + 1 <=
            gateBound +
                (circuits.length * (gateBound + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hHead hTail) 1
        _ = (circuits.length + 1) * (gateBound + 1) + 1 := by
          ring

/-! ## Equality and finite-set avoidance -/

private def literalDAG {N : Nat}
    (table : Bitstring N) (index : Fin N) : DagCircuit N :=
  if table index then inputProj index else dagNot (inputProj index)

@[simp] private theorem eval_literalDAG {N : Nat}
    (table input : Bitstring N) (index : Fin N) :
    eval (literalDAG table index) input = decide (input index = table index) := by
  cases hTable : table index <;> cases hInput : input index <;>
    simp [literalDAG, hTable, hInput]

private theorem gates_literalDAG_le_one {N : Nat}
    (table : Bitstring N) (index : Fin N) :
    (literalDAG table index).gates <= 1 := by
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
    apply decide_eq_true
    exact congrFun h index

theorem gates_equalsTableDAG_le {N : Nat} (table : Bitstring N) :
    (equalsTableDAG table).gates <= 2 * N + 1 := by
  unfold equalsTableDAG
  have hBound := gates_dagAndList_le
    (gateBound := 1)
    (List.ofFn fun index : Fin N => literalDAG table index)
  have hEach : forall circuit,
      circuit ∈ (List.ofFn fun index : Fin N => literalDAG table index) ->
      circuit.gates <= 1 := by
    intro circuit hCircuit
    rcases List.mem_ofFn.mp hCircuit with ⟨index, rfl⟩
    exact gates_literalDAG_le_one table index
  have h := hBound hEach
  simpa [Nat.mul_comm] using h

/-- A standard DAG accepting exactly the complement of a finite forbidden
set of `N`-bit strings. -/
noncomputable def avoidFiniteSetDAG {N : Nat}
    (forbidden : Finset (Bitstring N)) : DagCircuit N :=
  dagNot <| dagOrList <|
    forbidden.toList.map equalsTableDAG

@[simp] theorem eval_avoidFiniteSetDAG {N : Nat}
    (forbidden : Finset (Bitstring N)) (input : Bitstring N) :
    eval (avoidFiniteSetDAG forbidden) input =
      decide (input ∉ forbidden) := by
  classical
  by_cases hMem : input ∈ forbidden
  · have hAny :
        (forbidden.toList.map equalsTableDAG).any
            (fun circuit => eval circuit input) = true := by
      rw [List.any_eq_true]
      refine ⟨equalsTableDAG input, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨input, by simpa using hMem, rfl⟩
      · simp
    simp [avoidFiniteSetDAG, hAny, hMem]
  · have hAny :
        (forbidden.toList.map equalsTableDAG).any
            (fun circuit => eval circuit input) = false := by
      rw [List.any_eq_false]
      intro circuit hCircuit
      rcases List.mem_map.mp hCircuit with ⟨table, hTable, rfl⟩
      have hNe : input ≠ table := by
        intro hEq
        subst table
        exact hMem (by simpa using hTable)
      simp [hNe]
    simp [avoidFiniteSetDAG, hAny, hMem]

/-- Explicit size bound for recognizing the complement of a finite set.  The
bound is linear in the ambient bit length times the number of forbidden
strings; the harmless additive constants cover empty folds. -/
theorem size_avoidFiniteSetDAG_le {N : Nat}
    (forbidden : Finset (Bitstring N)) :
    size (avoidFiniteSetDAG forbidden) <=
      forbidden.card * (2 * N + 2) + 3 := by
  classical
  unfold avoidFiniteSetDAG
  rw [size, gates_dagNot]
  have hOr := gates_dagOrList_le
    (gateBound := 2 * N + 1)
    (forbidden.toList.map equalsTableDAG)
  have hEach : forall circuit,
      circuit ∈ forbidden.toList.map equalsTableDAG ->
      circuit.gates <= 2 * N + 1 := by
    intro circuit hCircuit
    rcases List.mem_map.mp hCircuit with ⟨table, _hTable, rfl⟩
    exact gates_equalsTableDAG_le table
  have hBound := hOr hEach
  simp only [List.length_map, Finset.length_toList] at hBound
  have hFactor : 2 * N + 1 + 1 = 2 * N + 2 := by omega
  rw [hFactor] at hBound
  omega

/-! ## Codec-image specialization -/

/-- The standard-DAG predicate explicitly avoiding the whole canonical codec
image.  This image contains every truth table with a paper-basis DAG of at
most `threshold` gates. -/
noncomputable def avoidEasyTablesByCodeDAG (n threshold : Nat) :
    DagCircuit (Pnp3.Models.Partial.tableLen n) :=
  avoidFiniteSetDAG (easyTablesByCode n threshold)

@[simp] theorem eval_avoidEasyTablesByCodeDAG
    (n threshold : Nat) (table : TruthTable n) :
    eval (avoidEasyTablesByCodeDAG n threshold) table =
      decide (table ∉ easyTablesByCode n threshold) := by
  simp [avoidEasyTablesByCodeDAG]

/-- Every threshold-easy truth table is rejected by the explicit outer DAG. -/
theorem avoidEasyTablesByCodeDAG_rejects_hasCircuit
    {n threshold : Nat} {table : TruthTable n}
    (hEasy : HasCircuit n threshold table) :
    eval (avoidEasyTablesByCodeDAG n threshold) table = false := by
  simp [mem_easyTablesByCode_of_hasCircuit hEasy]

/-- Concrete codec-only size bound. -/
theorem size_avoidEasyTablesByCodeDAG_le (n threshold : Nat) :
    size (avoidEasyTablesByCodeDAG n threshold) <=
      (2 ^ DAGCodec.codeLength n threshold) *
          (2 * Pnp3.Models.Partial.tableLen n + 2) + 3 := by
  apply le_trans (size_avoidFiniteSetDAG_le (easyTablesByCode n threshold))
  have hCard := card_easyTablesByCode_le n threshold
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right (2 * Pnp3.Models.Partial.tableLen n + 2) hCard) 3

/-- The codec-image avoider accepts a set larger than half of the truth-table
cube under the same length gap used by the mainline MCSP transfer. -/
theorem avoidEasyTablesByCodeDAG_denseAboveHalf
    (n threshold : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n) :
    DenseAboveHalf n
      (fun table : TruthTable n =>
        eval (avoidEasyTablesByCodeDAG n threshold) table = true) := by
  classical
  let witnesses : Finset (TruthTable n) :=
    Finset.univ \ easyTablesByCode n threshold
  have hCardEasy := four_mul_card_easyTablesByCode_lt n threshold hLength
  have hCardWitnesses :
      witnesses.card = 2 ^ (2 ^ n) -
        (easyTablesByCode n threshold).card := by
    dsimp [witnesses]
    rw [Finset.card_sdiff (Finset.subset_univ _)]
    simp
  have hDense : 2 ^ (2 ^ n) < witnesses.card * 2 := by
    rw [hCardWitnesses]
    omega
  refine ⟨witnesses, hDense, ?_⟩
  intro table hTable
  have hNotMem : table ∉ easyTablesByCode n threshold := by
    simpa [witnesses] using hTable
  simp [hNotMem]

/-- Once the outer size budget can hard-code the whole codec image, no local
generator can hit every dense standard-DAG predicate: the explicit avoider is
dense, is within budget, and rejects every locally easy output. -/
theorem not_hitsDenseDAGPredicates_of_codecAvoider_fits
    {n threshold maxSize : Nat}
    (generator : DAGLocalGenerator n threshold)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hFits :
      (2 ^ DAGCodec.codeLength n threshold) *
          (2 * Pnp3.Models.Partial.tableLen n + 2) + 3 <= maxSize) :
    Not (HitsDenseDAGPredicates generator maxSize) := by
  intro hHits
  let avoider := avoidEasyTablesByCodeDAG n threshold
  have hSize : C_DAG.size avoider <= maxSize :=
    (size_avoidEasyTablesByCodeDAG_le n threshold).trans hFits
  have hDense : DenseAboveHalf n
      (fun table : TruthTable n => C_DAG.eval avoider table = true) :=
    avoidEasyTablesByCodeDAG_denseAboveHalf n threshold hLength
  rcases hHits avoider hSize hDense with ⟨seed, hAccepts⟩
  have hRejects : C_DAG.eval avoider (generator.generate seed) = false :=
    avoidEasyTablesByCodeDAG_rejects_hasCircuit
      (generator.image_easy seed)
  exact Bool.false_ne_true (hRejects.symm.trans hAccepts)

/-- Existential generator form: under the explicit size inequality, there is
no pointwise-local generator satisfying the dense standard-DAG HSG endpoint. -/
theorem not_exists_DAGLocalGenerator_hitsDense_of_codecAvoider_fits
    {n threshold maxSize : Nat}
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hFits :
      (2 ^ DAGCodec.codeLength n threshold) *
          (2 * Pnp3.Models.Partial.tableLen n + 2) + 3 <= maxSize) :
    Not (Exists fun generator : DAGLocalGenerator n threshold =>
      HitsDenseDAGPredicates generator maxSize) := by
  rintro ⟨generator, hHits⟩
  exact
    not_hitsDenseDAGPredicates_of_codecAvoider_fits
      generator hLength hFits hHits

/-- Generator-free form of the same obstruction.  Once the codec-image
avoider fits the tested outer class, that one dense standard-DAG predicate
accepts no threshold-easy table at all. -/
theorem not_everyDenseDAGPredicateAcceptsEasyTable_of_codecAvoider_fits
    {n threshold maxSize : Nat}
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hFits :
      (2 ^ DAGCodec.codeLength n threshold) *
          (2 * Pnp3.Models.Partial.tableLen n + 2) + 3 <= maxSize) :
    Not (EveryDenseDAGPredicateAcceptsEasyTable n threshold maxSize) := by
  intro hEvery
  let avoider := avoidEasyTablesByCodeDAG n threshold
  have hSize : C_DAG.size avoider <= maxSize :=
    (size_avoidEasyTablesByCodeDAG_le n threshold).trans hFits
  have hDense : DenseAboveHalf n
      (fun table : TruthTable n => C_DAG.eval avoider table = true) :=
    avoidEasyTablesByCodeDAG_denseAboveHalf n threshold hLength
  rcases hEvery avoider hSize hDense with
    ⟨table, hEasy, hAccepts⟩
  have hRejects : C_DAG.eval avoider table = false :=
    avoidEasyTablesByCodeDAG_rejects_hasCircuit hEasy
  exact Bool.false_ne_true (hRejects.symm.trans hAccepts)

/-- Polynomial-size specialization of the codec avoider.  If the codec length
plus the two elementary hard-coding overhead bits fits below
`n * exponent`, then the explicit avoider already fits the `PpolyDAG` outer
budget `tableLen n ^ exponent + exponent + 1`.

Equivalently, any possible all-exponent dense-HSG witness must eventually
make `codeLength n (threshold n) / n` arbitrarily large; a codec length bounded
linearly in `n` is ruled out by a sufficiently large outer exponent. -/
theorem not_exists_DAGLocalGenerator_hitsDense_polynomial_of_codecBudget
    {n threshold exponent : Nat}
    (hExponent : 2 <= exponent)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hCodecBudget :
      DAGCodec.codeLength n threshold + n + 2 <= n * exponent) :
    Not (Exists fun generator : DAGLocalGenerator n threshold =>
      HitsDenseDAGPredicates generator
        ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) := by
  apply not_exists_DAGLocalGenerator_hitsDense_of_codecAvoider_fits hLength
  let N := Pnp3.Models.Partial.tableLen n
  let codeBits := DAGCodec.codeLength n threshold
  have hNPositive : 0 < N := by
    simp [N, Pnp3.Models.Partial.tableLen]
  have hFactor : 2 * N + 2 <= 4 * N := by omega
  have hPowerExponent :
      2 ^ (codeBits + n + 2) <= 2 ^ (n * exponent) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hCodecBudget
  have hCore :
      (2 ^ codeBits) * (2 * N + 2) <= N ^ exponent := by
    calc
      (2 ^ codeBits) * (2 * N + 2) <=
          (2 ^ codeBits) * (4 * N) :=
        Nat.mul_le_mul_left _ hFactor
      _ = 2 ^ (codeBits + n + 2) := by
        simp [N, Pnp3.Models.Partial.tableLen, pow_add]
        ring
      _ <= 2 ^ (n * exponent) := hPowerExponent
      _ = N ^ exponent := by
        simp [N, Pnp3.Models.Partial.tableLen, pow_mul]
  dsimp [codeBits, N] at hCore ⊢
  omega

/-- Generator-free polynomial specialization.  The hypotheses are identical
to the local-generator no-go above, but the conclusion targets exactly the
remaining dense/easy semantic intersection obligation. -/
theorem not_everyDenseDAGPredicateAcceptsEasyTable_polynomial_of_codecBudget
    {n threshold exponent : Nat}
    (hExponent : 2 <= exponent)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hCodecBudget :
      DAGCodec.codeLength n threshold + n + 2 <= n * exponent) :
    Not (EveryDenseDAGPredicateAcceptsEasyTable n threshold
      ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) := by
  intro hEvery
  have hMaxSize := two_le_ppolyDAGBound_with_outputNot n exponent
  have hExists :
      Exists fun generator : DAGLocalGenerator n threshold =>
        HitsDenseDAGPredicates generator
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1) :=
    (exists_hitsDenseDAGLocalGenerator_iff_everyDenseAcceptsEasy
      n threshold
        ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)
        hMaxSize).2 hEvery
  exact
    (not_exists_DAGLocalGenerator_hitsDense_polynomial_of_codecBudget
      hExponent hLength hCodecBudget) hExists

/-- Exact all-exponent consequence: a threshold family whose canonical codec
length is bounded by one fixed linear function of `n` cannot satisfy the
dense-HSG premise for every polynomial outer size.  The refuting exponent is
`linearConstant + 3`; the witness length may depend on the exponent, so this
rules out that quantifier pattern directly rather than only pointwise. -/
theorem not_allExponent_hitsDense_of_codeLength_linear
    (threshold : Nat -> Nat) (linearConstant : Nat)
    (hLinear : forall n : Nat, 0 < n ->
      DAGCodec.codeLength n (threshold n) <= linearConstant * n) :
    Not (forall exponent : Nat,
      Exists fun n : Nat =>
      Exists fun generator : DAGLocalGenerator n (threshold n) =>
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        HitsDenseDAGPredicates generator
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) := by
  intro hAll
  let exponent := linearConstant + 3
  rcases hAll exponent with ⟨n, generator, hLength, hHits⟩
  have hNPositive : 0 < n := by
    by_contra hNotPositive
    have hZero : n = 0 := by omega
    subst n
    norm_num at hLength
  have hExponent : 2 <= exponent := by
    simp [exponent]
  have hCodecBudget :
      DAGCodec.codeLength n (threshold n) + n + 2 <= n * exponent := by
    have hCode := hLinear n hNPositive
    dsimp [exponent]
    calc
      DAGCodec.codeLength n (threshold n) + n + 2 <=
          linearConstant * n + n + 2 := by omega
      _ <= n * (linearConstant + 3) := by
        nlinarith
  exact
    (not_exists_DAGLocalGenerator_hitsDense_polynomial_of_codecBudget
      hExponent hLength hCodecBudget) ⟨generator, hHits⟩

/-- Generator-free all-exponent refutation under the same revised positive-
length linear codec bound.  This conclusion is stated directly in terms of
`EveryDenseDAGPredicateAcceptsEasyTable`, matching the semantic dense/easy
obligation with no generator existential in its surface. -/
theorem not_allExponent_everyDenseDAGPredicateAcceptsEasyTable_of_codeLength_linear
    (threshold : Nat -> Nat) (linearConstant : Nat)
    (hLinear : forall n : Nat, 0 < n ->
      DAGCodec.codeLength n (threshold n) <= linearConstant * n) :
    Not (forall exponent : Nat,
      Exists fun n : Nat =>
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        EveryDenseDAGPredicateAcceptsEasyTable n (threshold n)
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) := by
  intro hAll
  apply
    (not_allExponent_hitsDense_of_codeLength_linear
      threshold linearConstant hLinear)
  intro exponent
  rcases hAll exponent with ⟨n, hLength, hEvery⟩
  have hMaxSize := two_le_ppolyDAGBound_with_outputNot n exponent
  rcases
      (exists_hitsDenseDAGLocalGenerator_iff_everyDenseAcceptsEasy
        n (threshold n)
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)
          hMaxSize).2 hEvery with
    ⟨generator, hHits⟩
  exact ⟨n, generator, hLength, hHits⟩

/-- Eventual-`O(n)` version of the generator-free all-exponent barrier.  A
finite prefix is absorbed into one explicit sum `prefixBudget`; the selected
outer exponent dominates both that prefix and the eventual linear bound.
Thus no hidden global-from-zero convention is needed. -/
theorem not_allExponent_everyDenseDAGPredicateAcceptsEasyTable_of_codeLength_eventuallyLinear
    (threshold : Nat -> Nat) (linearConstant : Nat)
    (hEventuallyLinear : Exists fun cutoff : Nat =>
      forall n : Nat, cutoff <= n ->
        DAGCodec.codeLength n (threshold n) <= linearConstant * n) :
    Not (forall exponent : Nat,
      Exists fun n : Nat =>
        DAGCodec.codeLength n (threshold n) + 2 < 2 ^ n /\
        EveryDenseDAGPredicateAcceptsEasyTable n (threshold n)
          ((Pnp3.Models.Partial.tableLen n) ^ exponent + exponent + 1)) := by
  rcases hEventuallyLinear with ⟨cutoff, hLinear⟩
  let prefixBudget : Nat :=
    ∑ index ∈ Finset.range cutoff,
      (DAGCodec.codeLength index (threshold index) + index + 2)
  let exponent : Nat := linearConstant + prefixBudget + 3
  intro hAll
  rcases hAll exponent with ⟨n, hLength, hEvery⟩
  have hNPositive : 0 < n := by
    by_contra hNotPositive
    have hZero : n = 0 := by omega
    subst n
    norm_num at hLength
  have hExponent : 2 <= exponent := by
    simp [exponent]
  have hCodecBudget :
      DAGCodec.codeLength n (threshold n) + n + 2 <= n * exponent := by
    by_cases hLate : cutoff <= n
    · have hCode := hLinear n hLate
      have hBase :
          DAGCodec.codeLength n (threshold n) + n + 2 <=
            n * (linearConstant + 3) := by
        calc
          DAGCodec.codeLength n (threshold n) + n + 2 <=
              linearConstant * n + n + 2 := by omega
          _ <= n * (linearConstant + 3) := by
            nlinarith
      have hExponentMonotone : linearConstant + 3 <= exponent := by
        dsimp [exponent]
        omega
      exact hBase.trans
        (Nat.mul_le_mul_left n hExponentMonotone)
    · have hBefore : n < cutoff := by omega
      have hMem : n ∈ Finset.range cutoff :=
        Finset.mem_range.mpr hBefore
      have hTerm :
          DAGCodec.codeLength n (threshold n) + n + 2 <= prefixBudget := by
        dsimp [prefixBudget]
        exact Finset.single_le_sum
          (fun index _hIndex => Nat.zero_le
            (DAGCodec.codeLength index (threshold index) + index + 2))
          hMem
      have hPrefixLeExponent : prefixBudget <= exponent := by
        dsimp [exponent]
        omega
      have hOneLeN : 1 <= n := Nat.succ_le_iff.mpr hNPositive
      calc
        DAGCodec.codeLength n (threshold n) + n + 2 <=
            prefixBudget := hTerm
        _ <= exponent := hPrefixLeExponent
        _ = 1 * exponent := by simp
        _ <= n * exponent := Nat.mul_le_mul_right exponent hOneLeN
  exact
    (not_everyDenseDAGPredicateAcceptsEasyTable_polynomial_of_codecBudget
      hExponent hLength hCodecBudget) hEvery

end OneTapeMagnification
end Frontier
end Pnp4
