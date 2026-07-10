import Pnp4.Frontier.OneTapeMagnification.LocalPRG
import Pnp4.Frontier.StreamingMagnification.DAGCodec
import Mathlib.Tactic

/-!
# Finite counting for standard-DAG truth tables

Every bounded standard DAG has a canonical fixed-length code.  Mapping the
entire finite code cube to truth tables (with one harmless default table for
malformed codes) therefore gives an explicit finite superset of the easy
tables.  Its cardinality is at most `2 ^ codeLength`.

The final theorem states the exact finite condition consumed by the CHMY
probability step: if `codeLength + 2 < 2^n`, fewer than one quarter of all
`2^n`-bit truth tables lie in this easy-table superset.  This is the concrete
finite form behind the usual asymptotic counting statement; no `o(·)` token
or probability oracle is used.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification
namespace Counting

open StreamingMagnification
open StreamingMagnification.TotalSearch

/-- The all-zero table used only as the image of malformed external codes. -/
def defaultTruthTable (n : Nat) : TruthTable n := fun _ => false

/-- Total map from every fixed-length bit body to a truth table. -/
def tableOfCode (n threshold : Nat)
    (code : DAGCodec.Code n threshold) : TruthTable n :=
  match DAGCodec.decode code with
  | some circuit => circuitTruthTable circuit.val
  | none => defaultTruthTable n

/-- Explicit finite superset of all threshold-easy standard-DAG tables. -/
def easyTablesByCode (n threshold : Nat) : Finset (TruthTable n) :=
  Finset.univ.image (tableOfCode n threshold)

@[simp]
theorem tableOfCode_encode
    {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold) :
    tableOfCode n threshold (DAGCodec.encode circuit) =
      circuitTruthTable circuit.val := by
  simp [tableOfCode]

/-- Every table with a bounded standard DAG belongs to the explicit set. -/
theorem mem_easyTablesByCode_of_hasCircuit
    {n threshold : Nat} {table : TruthTable n}
    (hEasy : HasCircuit n threshold table) :
    table ∈ easyTablesByCode n threshold := by
  rcases hEasy with ⟨circuit, hSize, _hBasis, hComputes⟩
  let bounded : DAGCodec.BoundedCircuit n threshold := ⟨circuit, hSize⟩
  apply Finset.mem_image.mpr
  refine ⟨DAGCodec.encode bounded, Finset.mem_univ _, ?_⟩
  simpa [bounded, tableOfCode] using hComputes

/-- The easy-table image cannot be larger than the external code cube. -/
theorem card_easyTablesByCode_le
    (n threshold : Nat) :
    (easyTablesByCode n threshold).card <=
      2 ^ DAGCodec.codeLength n threshold := by
  calc
    (easyTablesByCode n threshold).card <=
        (Finset.univ : Finset (DAGCodec.Code n threshold)).card := by
      exact Finset.card_image_le
    _ = Fintype.card (DAGCodec.Code n threshold) := by simp
    _ = 2 ^ DAGCodec.codeLength n threshold :=
      DAGCodec.card_code n threshold

/--
If the code needs at least two fewer bits than the truth table, the explicit
easy set occupies strictly less than one quarter of the table cube.
-/
theorem four_mul_card_easyTablesByCode_lt
    (n threshold : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n) :
    (easyTablesByCode n threshold).card * 4 < 2 ^ (2 ^ n) := by
  calc
    (easyTablesByCode n threshold).card * 4 <=
        (2 ^ DAGCodec.codeLength n threshold) * 4 :=
      Nat.mul_le_mul_right 4 (card_easyTablesByCode_le n threshold)
    _ = 2 ^ (DAGCodec.codeLength n threshold + 2) := by
      rw [pow_add]
      norm_num
    _ < 2 ^ (2 ^ n) :=
      Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hLength

/-- Outside the explicit superset there is genuinely no bounded DAG. -/
theorem not_hasCircuit_of_not_mem_easyTablesByCode
    {n threshold : Nat} {table : TruthTable n}
    (hNotMem : table ∉ easyTablesByCode n threshold) :
    Not (HasCircuit n threshold table) := by
  intro hEasy
  exact hNotMem (mem_easyTablesByCode_of_hasCircuit hEasy)

/--
Concrete finite input to `uniformMachineAcceptance_lt_half_of_easy_set_small`:
a one-third soundness bound on genuinely hard tables plus the code-length
inequality gives uniform acceptance strictly below one half.
-/
theorem uniformMachineAcceptance_lt_half_of_code_count
    (machine : RandomizedMachine)
    (n threshold randomBits steps : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hSoundness : forall table : TruthTable n,
      Not (HasCircuit n threshold table) ->
        machineAcceptance machine table randomBits steps <= (1 : Rat) / 3) :
    uniformMachineAcceptance machine n randomBits steps < (1 : Rat) / 2 := by
  apply uniformMachineAcceptance_lt_half_of_easy_set_small
    machine n randomBits steps (easyTablesByCode n threshold)
  · exact four_mul_card_easyTablesByCode_lt n threshold hLength
  · intro table hNotMem
    exact hSoundness table (not_hasCircuit_of_not_mem_easyTablesByCode hNotMem)

end Counting
end OneTapeMagnification
end Frontier
end Pnp4
