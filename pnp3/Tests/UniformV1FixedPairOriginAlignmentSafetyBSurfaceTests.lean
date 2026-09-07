import Complexity.Uniform.V1.FixedPairOriginAlignment

namespace Pnp3.Tests.UniformV1FixedPairOriginAlignmentSafetyBSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment

theorem check_budget_accounting {n m : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    ((B = 0 ↔ B' = 0) → ∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).state =
          (machine.run s (startConfig B' x w)).state ∧
      (machine.run s (startConfig B x w)).head.val =
          (machine.run s (startConfig B' x w)).head.val ∧
      (∀ (i : Fin (tapeLength (pairLength n m) B))
          (i' : Fin (tapeLength (pairLength n m) B')),
        i.val = i'.val →
        (machine.run s (startConfig B x w)).tape i =
          (machine.run s (startConfig B' x w)).tape i')) ∧
    (∀ s, 3 ≤ s → s ≤ clock n m →
      (machine.run s (startConfig B x w)).state =
          (machine.run s (startConfig B' x w)).state ∧
      (machine.run s (startConfig B x w)).head.val =
          (machine.run s (startConfig B' x w)).head.val ∧
      (∀ (i : Fin (tapeLength (pairLength n m) B))
          (i' : Fin (tapeLength (pairLength n m) B')),
        i.val = i'.val →
        (machine.run s (startConfig B x w)).tape i =
          (machine.run s (startConfig B' x w)).tape i')) ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val → alignedTape B x w i = alignedTape B' x w i') ∧
    clock n m = (10 * n + 7) * (n + m + 1) + 3 * n := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment.budget_accounting
    B B' x w

theorem check_fixed_extent_recovery {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ j : Fin n, alignedTape B x w
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j)) ∧
    (∀ j : Fin m, alignedTape B x w
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j)) ∧
    (∀ (x' : Bitstring n) (w' : Bitstring m),
      alignedTape B x w = alignedTape B x' w' → x = x' ∧ w = w') := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment.fixed_extent_recovery
    x w

theorem check_empty_zero_budget : ∀ (x : Bitstring 0) (w : Bitstring 0),
    clock 0 0 = 7 ∧
    machine.run 7 (startConfig 0 x w) = finalConfig 0 x w ∧
    (machine.run 0 (startConfig 0 x w)).head.val = 1 ∧
    (machine.run 2 (startConfig 0 x w)).head.val = 1 ∧
    (machine.run 4 (startConfig 0 x w)).head.val = 0 ∧
    (machine.run 7 (startConfig 0 x w)).head.val = 0 ∧
    (machine.run 7 (startConfig 0 x w)).tape
      ⟨0, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (∀ s, s < 7 →
      (machine.run s (startConfig 0 x w)).state ≠ qAccept ∧
      (machine.run s (startConfig 0 x w)).state ≠ qReject) ∧
    (∀ s, s < 7 →
      let c := machine.run s (startConfig 0 x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .right ∧
        moveHead c.head .right = c.head ↔ s = 2)) ∧
    (∀ s, s < 7 →
      let c := machine.run s (startConfig 0 x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .left ∧
        moveHead c.head .left = c.head ↔ s = 4)) := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment.empty_zero_budget

theorem check_phase_contract {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    let p := FixedPairOriginShiftBootstrap.machine.run
      (FixedPairOriginShiftBootstrap.clock n m)
      (FixedPairOriginShiftBootstrap.startConfig B x w)
    let c₀ := startConfig B x w
    p = FixedPairOriginShiftBootstrap.finalConfig B x w ∧
    p.state = FixedPairOriginShiftBootstrap.qAccept ∧ c₀.state = qStart ∧
    c₀.head = p.head ∧ c₀.tape = p.tape ∧
    machine.run (clock n m) c₀ = finalConfig B x w ∧
    (∀ s, s < clock n m →
      (machine.run s c₀).state ≠ qAccept ∧
      (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ clock n m →
      (machine.run s c₀).head.val ≤ pairLength n m + Nat.min B 1) ∧
    (∀ s, s ≤ clock n m → ∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m ≤ i.val → (machine.run s c₀).tape i = none) ∧
    (machine.run (clock n m) c₀).state = qAccept ∧
    (machine.run (clock n m) c₀).head.val = 0 ∧
    (machine.run (clock n m) c₀).tape = alignedTape B x w := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment.phase_contract x w

end Pnp3.Tests.UniformV1FixedPairOriginAlignmentSafetyBSurfaceTests
