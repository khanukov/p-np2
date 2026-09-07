import Complexity.Uniform.V1.FixedPairOriginAlignment

namespace Pnp3.Tests.UniformV1FixedPairOriginAlignmentSafetyASurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment

theorem check_final_fields_and_layout {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    let c := machine.run (clock n m) (startConfig B x w)
    c = finalConfig B x w ∧ c.state = qAccept ∧ c.state = machine.accept ∧
    c.head = (⟨0, by unfold tapeLength; omega⟩ :
      Fin (tapeLength (pairLength n m) B)) ∧ c.head.val = 0 ∧
    c.tape = alignedTape B x w ∧
    (∀ j : Fin n, c.tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j)) ∧
    (∀ j : Fin m, c.tape
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j)) ∧
    c.tape ⟨n + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      n + m + 1 ≤ i.val → c.tape i = none) :=
  final_fields_and_layout x w

theorem check_strict_first_terminal {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ s, s < clock n m →
      (machine.run s (startConfig B x w)).state ≠ qAccept ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) ∧
    (machine.run (clock n m) (startConfig B x w)).state = qAccept :=
  strict_first_terminal x w

theorem check_accepting_absorption {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (extra : Nat) :
    machine.run (clock n m + extra) (startConfig B x w) = finalConfig B x w ∧
    (machine.run (clock n m + extra) (startConfig B x w)).state = qAccept ∧
    (machine.run (clock n m + extra) (startConfig B x w)).head.val = 0 ∧
    (machine.run (clock n m + extra) (startConfig B x w)).tape =
      alignedTape B x w :=
  accepting_absorption x w extra

theorem check_footprint_through_clock {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val ≤
        pairLength n m + Nat.min B 1) ∧
    (machine.run 0 (startConfig B x w)).head.val =
      pairLength n m + Nat.min B 1 ∧
    (∀ s, s < clock n m →
      (machine.run s (startConfig B x w)).head.val ≤
        pairLength n m + Nat.min B 1) ∧
    (∀ s, s ≤ clock n m → ∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m ≤ i.val →
      (machine.run s (startConfig B x w)).tape i = none) :=
  footprint_through_clock x w

theorem check_boundary_clamps {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ s, s < clock n m →
      let c := machine.run s (startConfig B x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .right ∧
        moveHead c.head .right = c.head ↔ s = 2 ∧ B = 0)) ∧
    (∀ s, s < clock n m →
      let c := machine.run s (startConfig B x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .left ∧
        moveHead c.head .left = c.head ↔ s = clock n m - 3)) ∧
    ((let c := machine.run 2 (startConfig B x w);
      c.head.val = (if B = 0 then pairLength n m else pairLength n m - 1) ∧
      (machine.step c.state (c.tape c.head)).2.2 = .right) ∧
    (let c := machine.run (clock n m - 3) (startConfig B x w);
      c.head.val = 0 ∧
      (machine.step c.state (c.tape c.head)).2.2 = .left)) :=
  boundary_clamps x w

end Pnp3.Tests.UniformV1FixedPairOriginAlignmentSafetyASurfaceTests
