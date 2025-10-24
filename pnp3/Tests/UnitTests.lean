import Core.BooleanBasics

/-!
# Unit Tests for pnp3 Computational Functions

This file contains unit tests for computational (non-axiomatic) functions.
These tests verify the behavior of basic building blocks used in the proof.
-/

namespace Pnp3.Tests

open Pnp3.Core

/-!
## Tests for b2n (Bool to Nat conversion)
-/

/-- Test: true converts to 1 -/
def test_b2n_true : b2n true = 1 := by rfl

/-- Test: false converts to 0 -/
def test_b2n_false : b2n false = 0 := by rfl

/-!
## Tests for boolXor
-/

/-- Test: XOR of same values is false -/
def test_boolXor_true_true : boolXor true true = false := by rfl

/-- Test: XOR of same values is false -/
def test_boolXor_false_false : boolXor false false = false := by rfl

/-- Test: XOR of different values is true -/
def test_boolXor_true_false : boolXor true false = true := by rfl

/-- Test: XOR of different values is true -/
def test_boolXor_false_true : boolXor false true = true := by rfl

/-!
## Tests for Subcube.assign
-/

/-- Test: Assigning to a free coordinate succeeds -/
def test_subcube_assign_free :
    let β : Subcube 3 := fun _ => none
    let result := Subcube.assign β 0 true
    result.isSome = true := by rfl

/-- Test: Assigning same value to already-assigned coordinate succeeds -/
def test_subcube_assign_same :
    let β : Subcube 3 := fun i => if i = 0 then some true else none
    let result := Subcube.assign β 0 true
    result.isSome = true := by rfl

/-- Test: Assigning conflicting value to already-assigned coordinate fails -/
def test_subcube_assign_conflict :
    let β : Subcube 3 := fun i => if i = 0 then some true else none
    let result := Subcube.assign β 0 false
    result.isNone = true := by rfl

/-!
## Tests for Subcube.assignMany
-/

/-- Test: Empty assignment list succeeds -/
def test_subcube_assignMany_empty :
    let β : Subcube 3 := fun _ => none
    let result := Subcube.assignMany β []
    result.isSome = true := by rfl

/-- Test: Single assignment in list -/
def test_subcube_assignMany_single :
    let β : Subcube 3 := fun _ => none
    let result := Subcube.assignMany β [(0, true)]
    result.isSome = true := by rfl

/-- Test: Multiple compatible assignments succeed -/
def test_subcube_assignMany_compatible :
    let β : Subcube 3 := fun _ => none
    let result := Subcube.assignMany β [(0, true), (1, false), (2, true)]
    result.isSome = true := by rfl

/-- Test: Conflicting assignments in list fail -/
def test_subcube_assignMany_conflict :
    let β : Subcube 3 := fun _ => none
    let result := Subcube.assignMany β [(0, true), (0, false)]
    result.isNone = true := by rfl

/-!
## Tests for memB (membership check)
-/

/-- Test: Point belongs to free subcube -/
def test_memB_free_subcube :
    let β : Subcube 3 := fun _ => none
    let x : Core.BitVec 3 := fun _ => true
    memB β x = true := by
      simp [memB]

/-- Test: All-false point belongs to free subcube -/
def test_memB_free_subcube_false :
    let β : Subcube 3 := fun _ => none
    let x : Core.BitVec 3 := fun _ => false
    memB β x = true := by
      simp [memB]

/-- Test: memB evaluates correctly on simple example -/
def test_memB_simple_eval :
    let β : Subcube 2 := fun _ => none
    let x : Core.BitVec 2 := fun _ => true
    memB β x = true := by rfl

/-!
## Test Summary
All tests pass if this file compiles successfully.
-/

/-- Marker that all unit tests compiled and passed -/
def all_unit_tests_pass : Bool := true

end Pnp3.Tests
