import Complexity.Uniform.V1.FixedPairContentMarkerErase

namespace Pnp3.Tests.UniformV1FixedPairContentMarkerEraseSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase

def check_eraseStateCount : Nat := eraseStateCount

def check_qScan : Fin eraseStateCount := qScan

def check_qErase : Fin eraseStateCount := qErase

def check_qAccept : Fin eraseStateCount := qAccept

def check_qReject : Fin eraseStateCount := qReject

def check_machine : UniformTM := machine

def check_retag {N B : Nat} :
    Config FixedPairOriginAlignment.alignmentStateCount N B →
      Config eraseStateCount N B :=
  retag

def check_startConfig {n m : Nat} :
    (B : Nat) → (x : Bitstring n) → (w : Bitstring m) →
      Config eraseStateCount (pairLength n m) B :=
  startConfig

def check_clock : Nat → Nat → Nat := clock

def check_contentTape {n m : Nat} :
    (B : Nat) → (x : Bitstring n) → (w : Bitstring m) →
      Fin (tapeLength (pairLength n m) B) → Option Bool :=
  contentTape

def check_finalConfig {n m : Nat} :
    (B : Nat) → (x : Bitstring n) → (w : Bitstring m) →
      Config eraseStateCount (pairLength n m) B :=
  finalConfig

theorem check_table_and_resource_pins :
    (∀ scanned, machine.rawStep qScan scanned =
      match scanned with
      | none => (qErase, none, .left)
      | some b => (qScan, some b, .right)) ∧
    machine.rawStep qErase (some true) = (qAccept, none, .stay) ∧
    machine.rawStep qErase (some false) = (qReject, some false, .stay) ∧
    machine.rawStep qErase none = (qReject, none, .stay) ∧
    (∀ scanned, machine.rawStep qAccept scanned =
      (qAccept, scanned, .stay)) ∧
    (∀ scanned, machine.rawStep qReject scanned =
      (qReject, scanned, .stay)) ∧
    machine.stateCount = 4 ∧ machine.start = qScan ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qScan.val = 0 ∧ qErase.val = 1 ∧ qAccept.val = 2 ∧ qReject.val = 3 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 12 := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.table_and_resource_pins

theorem check_clock_exact (n m : Nat) : clock n m = n + m + 3 := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.clock_exact n m

theorem check_handoff_exact {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    let p := FixedPairOriginAlignment.machine.run
      (FixedPairOriginAlignment.clock n m)
      (FixedPairOriginAlignment.startConfig B x w)
    let c₀ := startConfig B x w
    p = FixedPairOriginAlignment.finalConfig B x w ∧
    p.state = FixedPairOriginAlignment.qAccept ∧
    c₀ = retag p ∧ c₀.state = qScan ∧ c₀.head = p.head ∧
    c₀.tape = p.tape := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.handoff_exact x w

theorem check_run_exact {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) :
    machine.run (clock n m) (startConfig B x w) = finalConfig B x w := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.run_exact B x w

theorem check_final_fields_and_layout {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    let c := machine.run (clock n m) (startConfig B x w)
    c = finalConfig B x w ∧ c.state = qAccept ∧ c.state = machine.accept ∧
    c.head = (⟨n + m, by unfold tapeLength pairLength; omega⟩ :
      Fin (tapeLength (pairLength n m) B)) ∧ c.head.val = n + m ∧
    c.tape = contentTape B x w ∧
    (∀ j : Fin (n + m), c.tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
    (∀ j : Fin n, c.tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j)) ∧
    (∀ j : Fin m, c.tape
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j)) ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      n + m ≤ i.val → c.tape i = none) := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.final_fields_and_layout x w

theorem check_strict_first_terminal {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ s, s < clock n m →
      (machine.run s (startConfig B x w)).state ≠ qAccept ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) ∧
    (machine.run (clock n m) (startConfig B x w)).state = qAccept := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.strict_first_terminal x w

theorem check_post_clock_absorption {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (extra : Nat) :
    machine.run (clock n m + extra) (startConfig B x w) =
      finalConfig B x w := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.post_clock_absorption
    x w extra

theorem check_full_footprint {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val =
        if s ≤ n + m + 1 then s else n + m) ∧
    (machine.run (n + m + 1) (startConfig B x w)).head.val = n + m + 1 ∧
    (∀ k, k ≤ n + m + 1 →
      (machine.run k (startConfig B x w)).head.val = k) ∧
    (∀ s, s ≤ clock n m → ∀ i : Fin (tapeLength (pairLength n m) B),
      n + m < i.val → (machine.run s (startConfig B x w)).tape i = none) := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.full_footprint x w

theorem check_no_boundary_clamp {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (s : Nat) (hs : s < clock n m) :
    let c := machine.run s (startConfig B x w)
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (move = .left → 0 < c.head.val) := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.no_boundary_clamp
    x w s hs

theorem check_budget_independence {n m : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m) (s : Nat)
    (hs : s ≤ clock n m) :
    (machine.run s (startConfig B x w)).state =
        (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
        (machine.run s (startConfig B' x w)).head.val ∧
    ∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i' := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.budget_independence
    B B' x w s hs

theorem check_fixed_extent_recovery {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ j : Fin n, contentTape B x w
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j)) ∧
    (∀ j : Fin m, contentTape B x w
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j)) ∧
    (∀ (x' : Bitstring n) (w' : Bitstring m),
      contentTape B x w = contentTape B x' w' → x = x' ∧ w = w') := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.fixed_extent_recovery
    x w

theorem check_empty_zero_budget_trace (x : Bitstring 0) (w : Bitstring 0) :
    clock 0 0 = 3 ∧
    (machine.run 0 (startConfig 0 x w)).state = qScan ∧
    (machine.run 0 (startConfig 0 x w)).head.val = 0 ∧
    (machine.run 0 (startConfig 0 x w)).tape
      ⟨0, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (machine.run 1 (startConfig 0 x w)).state = qScan ∧
    (machine.run 1 (startConfig 0 x w)).head.val = 1 ∧
    (machine.run 1 (startConfig 0 x w)).tape
      ⟨1, by unfold tapeLength pairLength; omega⟩ = none ∧
    (machine.run 2 (startConfig 0 x w)).state = qErase ∧
    (machine.run 2 (startConfig 0 x w)).head.val = 0 ∧
    machine.run 3 (startConfig 0 x w) = finalConfig 0 x w ∧
    (∀ i : Fin (tapeLength (pairLength 0 0) 0),
      (machine.run 3 (startConfig 0 x w)).tape i = none) := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.empty_zero_budget_trace
    x w

theorem check_phase_contract {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    let p := FixedPairOriginAlignment.machine.run
      (FixedPairOriginAlignment.clock n m)
      (FixedPairOriginAlignment.startConfig B x w)
    let c₀ := startConfig B x w
    p = FixedPairOriginAlignment.finalConfig B x w ∧
    p.state = FixedPairOriginAlignment.qAccept ∧ c₀ = retag p ∧
    machine.run (n + m + 3) c₀ = finalConfig B x w ∧
    (∀ s, s < n + m + 3 →
      (machine.run s c₀).state ≠ qAccept ∧
      (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ n + m + 3 →
      (machine.run s c₀).head.val ≤ n + m + 1) ∧
    (∀ s, s < n + m + 3 →
      let c := machine.run s c₀
      let move := (machine.step c.state (c.tape c.head)).2.2
      (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
      (move = .left → 0 < c.head.val)) ∧
    (machine.run (n + m + 3) c₀).head.val = n + m ∧
    (machine.run (n + m + 3) c₀).tape = contentTape B x w ∧
    (∀ i : Fin (tapeLength (pairLength n m) B), n + m ≤ i.val →
      (machine.run (n + m + 3) c₀).tape i = none) ∧
    (∀ j : Fin (n + m), (machine.run (n + m + 3) c₀).tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
    (∀ extra, machine.run (n + m + 3 + extra) c₀ = finalConfig B x w) ∧
    (∀ B' s, s ≤ n + m + 3 →
      (machine.run s c₀).state =
          (machine.run s (startConfig B' x w)).state ∧
      (machine.run s c₀).head.val =
          (machine.run s (startConfig B' x w)).head.val ∧
      ∀ (i : Fin (tapeLength (pairLength n m) B))
          (i' : Fin (tapeLength (pairLength n m) B')),
        i.val = i'.val →
        (machine.run s c₀).tape i =
          (machine.run s (startConfig B' x w)).tape i') := by
  exact Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase.phase_contract x w

end Pnp3.Tests.UniformV1FixedPairContentMarkerEraseSurfaceTests
