import Pnp4.Frontier.StreamingMagnification.StreamMergeDriver
import Mathlib.Tactic

/-!
# Correctness of the pure Stream-Merge block driver

This module proves the decreasing-unread-suffix invariant for the explicit
fuel loop, preservation of `PrefixAgreement` across every successful block,
sound early failure, and exact final found/no-circuit behavior.

These are functional reference theorems only.  They neither construct a
`StreamingRAM.Program` nor serialize its report bits.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeDriver

open StandardDAG
open TotalSearch
open StreamMerge

/-! ## Exact blocks and progress -/

@[simp] theorem nextBlock_length
    {n : Nat} (table : TruthTable n) (blockLength consumed : Nat) :
    (nextBlock table blockLength consumed).length =
      expectedLength n blockLength consumed := by
  simp [nextBlock, tableBlock, expectedLength, List.length_take,
    tableBits_length]

theorem nextBlock_windowWellFormed
    {n : Nat} (table : TruthTable n) (blockLength consumed : Nat)
    (hconsumed : consumed <= 2 ^ n) :
    WindowWellFormed n blockLength consumed
      (nextBlock table blockLength consumed) :=
  ⟨hconsumed, nextBlock_length table blockLength consumed⟩

theorem nextBlock_is_tableBlock
    {n : Nat} (table : TruthTable n) (blockLength consumed : Nat) :
    nextBlock table blockLength consumed =
      tableBlock table consumed
        (nextBlock table blockLength consumed).length := by
  rw [nextBlock_length]
  rfl

theorem nextBlock_length_pos
    {n blockLength consumed : Nat} {table : TruthTable n}
    (hpositive : 0 < blockLength)
    (hmore : consumed < 2 ^ n) :
    0 < (nextBlock table blockLength consumed).length := by
  rw [nextBlock_length]
  unfold expectedLength
  have hremaining : 0 < 2 ^ n - consumed := by omega
  omega

theorem nextConsumed_le
    {n blockLength consumed : Nat} {table : TruthTable n}
    (hconsumed : consumed <= 2 ^ n) :
    consumed + (nextBlock table blockLength consumed).length <= 2 ^ n :=
  StreamMerge.nextConsumed_le
    (nextBlock_windowWellFormed table blockLength consumed hconsumed)

theorem unreadSuffix_strictly_decreases
    {n blockLength consumed : Nat} {table : TruthTable n}
    (hpositive : 0 < blockLength)
    (hmore : consumed < 2 ^ n) :
    2 ^ n - (consumed + (nextBlock table blockLength consumed).length) <
      2 ^ n - consumed := by
  have hlength := nextBlock_length_pos (table := table) hpositive hmore
  have hnext := nextConsumed_le (table := table) (blockLength := blockLength)
    (Nat.le_of_lt hmore)
  omega

/-! ## Run invariant -/

/-- Exact meaning of a terminal reference-driver result. -/
def CorrectResult {n s : Nat} (table : TruthTable n) : Result n s -> Prop
  | .found code =>
      Exists fun circuit : DAGCodec.BoundedCircuit n s =>
        DAGCodec.decode code = some circuit /\
          circuit.val.UsesOnlyAndOrNot /\ Computes circuit.val table
  | .noCircuit => Not (HasCircuit n s table)
  | .malformed _ => False

theorem computes_implies_prefixAgreement
    {n : Nat} {circuit : FlatCircuit n} {table : TruthTable n}
    (hcomputes : Computes circuit table) (used : Nat) :
    PrefixAgreement circuit table used := by
  unfold Computes at hcomputes
  unfold PrefixAgreement circuitBits
  rw [hcomputes]

theorem hasCircuit_implies_prefixExtension
    {n s : Nat} {table : TruthTable n} (used : Nat)
    (hhas : HasCircuit n s table) :
    Exists fun circuit : DAGCodec.BoundedCircuit n s =>
      circuit.val.UsesOnlyAndOrNot /\
        PrefixAgreement circuit.val table used := by
  rcases hhas with ⟨circuit, hsize, hbasis, hcomputes⟩
  exact ⟨⟨circuit, hsize⟩, hbasis,
    computes_implies_prefixAgreement hcomputes used⟩

/-- The initial technical prior need not use the paper basis because it
constrains an empty prefix.  After any successful positive-length block, the
selected circuit is in the paper basis. -/
def BasisAfterProgress {n s : Nat} (consumed : Nat)
    (current : DAGCodec.BoundedCircuit n s) : Prop :=
  consumed = 0 ∨ current.val.UsesOnlyAndOrNot

/-- Main fuel invariant.  The strict fuel hypothesis is exactly what the
public initial call supplies and what one positive block preserves. -/
theorem runFuel_correct
    {n s blockLength fuel consumed : Nat}
    {table : TruthTable n}
    {currentCode : DAGCodec.Code n s}
    {current : DAGCodec.BoundedCircuit n s}
    (hpositive : 0 < blockLength)
    (hconsumed : consumed <= 2 ^ n)
    (hfuel : 2 ^ n - consumed < fuel)
    (hdecode : DAGCodec.decode currentCode = some current)
    (hbasis : BasisAfterProgress consumed current)
    (hprefix : PrefixAgreement current.val table consumed) :
    CorrectResult table
      (runFuel table blockLength fuel consumed currentCode) := by
  induction fuel generalizing consumed currentCode current with
  | zero => omega
  | succ fuel ih =>
      simp only [runFuel]
      by_cases hdone : consumed = 2 ^ n
      · rw [if_pos hdone]
        unfold CorrectResult
        have hpaper : current.val.UsesOnlyAndOrNot := by
          rcases hbasis with hzero | hpaper
          · have hpow : 0 < 2 ^ n := pow_pos (by omega) n
            omega
          · exact hpaper
        refine ⟨current, hdecode, hpaper, ?_⟩
        apply (prefixAgreement_full_iff_computes current.val table).mp
        simpa only [hdone] using hprefix
      · rw [if_neg hdone]
        have hmore : consumed < 2 ^ n := by omega
        rw [if_pos hmore]
        let block := nextBlock table blockLength consumed
        have hwindow : WindowWellFormed n blockLength consumed block :=
          nextBlock_windowWellFormed table blockLength consumed hconsumed
        have hliteral : block = tableBlock table consumed block.length :=
          nextBlock_is_tableBlock table blockLength consumed
        cases hmerge : referenceStreamMerge currentCode blockLength consumed block with
        | found nextCode =>
            rcases referenceStreamMerge_found_prefixAgreement
              hdecode hwindow hprefix hliteral hmerge with
              ⟨next, hnextDecode, hnextBasis, hnextPrefix⟩
            have hnextConsumed : consumed + block.length <= 2 ^ n :=
              nextConsumed_le (table := table) (blockLength := blockLength)
                hconsumed
            have hdecrease :
                2 ^ n - (consumed + block.length) < 2 ^ n - consumed :=
              unreadSuffix_strictly_decreases
                (table := table) hpositive hmore
            apply ih (consumed := consumed + block.length)
              (currentCode := nextCode) (current := next)
              hnextConsumed (by omega) hnextDecode (Or.inr hnextBasis)
              hnextPrefix
        | noCircuit =>
            unfold CorrectResult
            intro hhas
            have hnone :=
              (referenceStreamMerge_noCircuit_iff_noPrefixExtension
                block currentCode current table hdecode hwindow hprefix hliteral).mp
                hmerge
            exact hnone (hasCircuit_implies_prefixExtension
              (consumed + block.length) hhas)
        | malformed reason =>
            have himpossible := referenceStreamMerge_valid_eq
              block currentCode current hdecode hwindow
            rw [hmerge] at himpossible
            cases hselect : selectCode current consumed block with
            | none =>
                simp [hselect] at himpossible
            | some code =>
                simp [hselect] at himpossible

/-- The already-read prefix is trivially correct at the public initial
cursor, independently of the decoded circuit's values. -/
@[simp] theorem prefixAgreement_zero
    {n : Nat} (circuit : FlatCircuit n) (table : TruthTable n) :
    PrefixAgreement circuit table 0 := by
  simp [PrefixAgreement]

/-- A valid initial body and positive block length expose the fuel loop
without either public validation error. -/
theorem referenceStreamDriver_valid_eq
    {n s blockLength : Nat} (table : TruthTable n)
    (initialCode : DAGCodec.Code n s)
    (initial : DAGCodec.BoundedCircuit n s)
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength) :
    referenceStreamDriver initialCode blockLength table =
      runFuel table blockLength (2 ^ n + 1) 0 initialCode := by
  unfold referenceStreamDriver
  rw [hdecode]
  rw [if_neg (Nat.ne_of_gt hpositive)]

/-- Public induction theorem: a decoded initial body and positive nominal
block length always terminate in a semantically correct, non-malformed
result. -/
theorem referenceStreamDriver_correct
    {n s blockLength : Nat} (table : TruthTable n)
    (initialCode : DAGCodec.Code n s)
    (initial : DAGCodec.BoundedCircuit n s)
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength) :
    CorrectResult table
      (referenceStreamDriver initialCode blockLength table) := by
  rw [referenceStreamDriver_valid_eq
    table initialCode initial hdecode hpositive]
  apply runFuel_correct hpositive (Nat.zero_le _) (by simp) hdecode (Or.inl rfl)
  exact prefixAgreement_zero initial.val table

/-- An early `noCircuit` from any valid loop state is already sound for the
entire truth table; the driver need not wait for the final block. -/
theorem runFuel_early_noCircuit_sound
    {n s blockLength fuel consumed : Nat}
    {table : TruthTable n}
    {currentCode : DAGCodec.Code n s}
    {current : DAGCodec.BoundedCircuit n s}
    (hpositive : 0 < blockLength)
    (hconsumed : consumed <= 2 ^ n)
    (hfuel : 2 ^ n - consumed < fuel)
    (hdecode : DAGCodec.decode currentCode = some current)
    (hbasis : BasisAfterProgress consumed current)
    (hprefix : PrefixAgreement current.val table consumed)
    (hrun : runFuel table blockLength fuel consumed currentCode =
      Result.noCircuit) :
    Not (HasCircuit n s table) := by
  have hcorrect := runFuel_correct hpositive hconsumed hfuel hdecode hbasis hprefix
  rw [hrun] at hcorrect
  exact hcorrect

theorem referenceStreamDriver_found_sound
    {n s blockLength : Nat} {table : TruthTable n}
    {initialCode code : DAGCodec.Code n s}
    {initial : DAGCodec.BoundedCircuit n s}
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength)
    (hrun : referenceStreamDriver initialCode blockLength table =
      Result.found code) :
    Exists fun circuit : DAGCodec.BoundedCircuit n s =>
      DAGCodec.decode code = some circuit /\
        circuit.val.UsesOnlyAndOrNot /\ Computes circuit.val table := by
  have hcorrect := referenceStreamDriver_correct
    table initialCode initial hdecode hpositive
  rw [hrun] at hcorrect
  exact hcorrect

theorem referenceStreamDriver_noCircuit_sound
    {n s blockLength : Nat} {table : TruthTable n}
    {initialCode : DAGCodec.Code n s}
    {initial : DAGCodec.BoundedCircuit n s}
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength)
    (hrun : referenceStreamDriver initialCode blockLength table =
      Result.noCircuit) :
    Not (HasCircuit n s table) := by
  have hcorrect := referenceStreamDriver_correct
    table initialCode initial hdecode hpositive
  rw [hrun] at hcorrect
  exact hcorrect

/-- Exact successful endpoint for the complete block iteration. -/
theorem referenceStreamDriver_found_iff_hasCircuit
    {n s blockLength : Nat} (table : TruthTable n)
    (initialCode : DAGCodec.Code n s)
    (initial : DAGCodec.BoundedCircuit n s)
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength) :
    (Exists fun code : DAGCodec.Code n s =>
      referenceStreamDriver initialCode blockLength table = Result.found code) <->
      HasCircuit n s table := by
  have hcorrect := referenceStreamDriver_correct
    table initialCode initial hdecode hpositive
  constructor
  · rintro ⟨code, hrun⟩
    rw [hrun] at hcorrect
    rcases hcorrect with ⟨circuit, _hcircuitDecode, hbasis, hcomputes⟩
    exact ⟨circuit.val, circuit.property, hbasis, hcomputes⟩
  · intro hhas
    cases hrun : referenceStreamDriver initialCode blockLength table with
    | found code => exact ⟨code, rfl⟩
    | noCircuit =>
        rw [hrun] at hcorrect
        exact (hcorrect hhas).elim
    | malformed reason =>
        rw [hrun] at hcorrect
        exact hcorrect.elim

/-- Exact negative endpoint for the complete block iteration. -/
theorem referenceStreamDriver_noCircuit_iff
    {n s blockLength : Nat} (table : TruthTable n)
    (initialCode : DAGCodec.Code n s)
    (initial : DAGCodec.BoundedCircuit n s)
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength) :
    referenceStreamDriver initialCode blockLength table = Result.noCircuit <->
      Not (HasCircuit n s table) := by
  have hcorrect := referenceStreamDriver_correct
    table initialCode initial hdecode hpositive
  constructor
  · intro hrun
    rw [hrun] at hcorrect
    exact hcorrect
  · intro hnone
    cases hrun : referenceStreamDriver initialCode blockLength table with
    | found code =>
        rw [hrun] at hcorrect
        rcases hcorrect with ⟨circuit, _hcircuitDecode, hbasis, hcomputes⟩
        exact (hnone ⟨circuit.val, circuit.property, hbasis, hcomputes⟩).elim
    | noCircuit => rfl
    | malformed reason =>
        rw [hrun] at hcorrect
        exact hcorrect.elim

theorem referenceStreamDriver_noCircuit_complete
    {n s blockLength : Nat} {table : TruthTable n}
    {initialCode : DAGCodec.Code n s}
    {initial : DAGCodec.BoundedCircuit n s}
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength)
    (hnone : Not (HasCircuit n s table)) :
    referenceStreamDriver initialCode blockLength table = Result.noCircuit :=
  (referenceStreamDriver_noCircuit_iff
    table initialCode initial hdecode hpositive).mpr hnone

theorem referenceStreamDriver_found_complete
    {n s blockLength : Nat} {table : TruthTable n}
    {initialCode : DAGCodec.Code n s}
    {initial : DAGCodec.BoundedCircuit n s}
    (hdecode : DAGCodec.decode initialCode = some initial)
    (hpositive : 0 < blockLength)
    (hhas : HasCircuit n s table) :
    Exists fun code : DAGCodec.Code n s =>
      referenceStreamDriver initialCode blockLength table = Result.found code :=
  (referenceStreamDriver_found_iff_hasCircuit
    table initialCode initial hdecode hpositive).mpr hhas

end StreamMergeDriver
end StreamingMagnification
end Frontier
end Pnp4
