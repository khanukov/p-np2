import Complexity.Uniform.V1.FixedContentTagGate

namespace Pnp3.Tests.UniformV1FixedContentTagGateSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedContentTagGate

def check_stateCount : Nat := stateCount

def check_expectedTagBit : Fin 8 → Bool := expectedTagBit

def check_physicalSymbol {L : Nat} :
    Bitstring L → Nat → Option Bool :=
  physicalSymbol

def check_tagMatches {L : Nat} : Bitstring L → Bool := tagMatches

def check_machine : UniformTM := machine

def check_startConfig {a m : Nat} :
    (B : Nat) → (x : Bitstring a) → (w : Bitstring m) →
      Config stateCount (pairLength a m) B :=
  startConfig

def check_deadline : Nat → Nat → Nat := deadline

def check_finalConfig {a m : Nat} :
    (B : Nat) → (x : Bitstring a) → (w : Bitstring m) →
      Config stateCount (pairLength a m) B :=
  finalConfig

theorem check_tag_contract {L : Nat} (z : Bitstring L) :
    expectedTagBit ⟨0, by decide⟩ = true ∧
    expectedTagBit ⟨1, by decide⟩ = false ∧
    expectedTagBit ⟨2, by decide⟩ = true ∧
    expectedTagBit ⟨3, by decide⟩ = true ∧
    expectedTagBit ⟨4, by decide⟩ = false ∧
    expectedTagBit ⟨5, by decide⟩ = false ∧
    expectedTagBit ⟨6, by decide⟩ = true ∧
    expectedTagBit ⟨7, by decide⟩ = false ∧
    (tagMatches z = true ↔
      ∀ j : Fin 8,
        physicalSymbol z j.1 = some (expectedTagBit j)) ∧
    (tagMatches z = true → 8 ≤ L) := by
  exact Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tag_contract z

theorem check_table_and_resource_pins :
    machine.rawStep = (fun q scanned =>
      match q.1 with
      | 0 => match scanned with
        | none => (⟨1, by decide⟩, none, .left)
        | some b => (⟨14, by decide⟩, some b, .stay)
      | 1 => match scanned with
        | none => (⟨14, by decide⟩, none, .stay)
        | some false => (⟨2, by decide⟩, none, .left)
        | some true => (⟨3, by decide⟩, none, .left)
      | 2 => match scanned with
        | none => (⟨14, by decide⟩, some false, .stay)
        | some b => (⟨4, by decide⟩, some b, .right)
      | 3 => match scanned with
        | none => (⟨6, by decide⟩, some true, .right)
        | some b => (⟨5, by decide⟩, some b, .right)
      | 4 => match scanned with
        | none => (⟨1, by decide⟩, some false, .left)
        | some b => (⟨14, by decide⟩, some b, .stay)
      | 5 => match scanned with
        | none => (⟨1, by decide⟩, some true, .left)
        | some b => (⟨14, by decide⟩, some b, .stay)
      | 6 => match scanned with
        | some false => (⟨7, by decide⟩, some false, .right)
        | s => (⟨14, by decide⟩, s, .stay)
      | 7 => match scanned with
        | some true => (⟨8, by decide⟩, some true, .right)
        | s => (⟨14, by decide⟩, s, .stay)
      | 8 => match scanned with
        | some true => (⟨9, by decide⟩, some true, .right)
        | s => (⟨14, by decide⟩, s, .stay)
      | 9 => match scanned with
        | some false => (⟨10, by decide⟩, some false, .right)
        | s => (⟨14, by decide⟩, s, .stay)
      | 10 => match scanned with
        | some false => (⟨11, by decide⟩, some false, .right)
        | s => (⟨14, by decide⟩, s, .stay)
      | 11 => match scanned with
        | some true => (⟨12, by decide⟩, some true, .right)
        | s => (⟨14, by decide⟩, s, .stay)
      | 12 => match scanned with
        | some false => (⟨13, by decide⟩, some false, .right)
        | s => (⟨14, by decide⟩, s, .stay)
      | 13 => (⟨13, by decide⟩, scanned, .stay)
      | _ => (⟨14, by decide⟩, scanned, .stay)) ∧
    machine.stateCount = 15 ∧
    machine.start = ⟨0, by decide⟩ ∧
    machine.accept = ⟨13, by decide⟩ ∧
    machine.reject = ⟨14, by decide⟩ ∧
    machine.accept.val = 13 ∧ machine.reject.val = 14 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 45 := by
  exact Pnp3.Complexity.Uniform.V1.FixedContentTagGate.table_and_resource_pins

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a)
    (w : Bitstring m) :
    let p := FixedPairContentMarkerErase.machine.run
      (FixedPairContentMarkerErase.clock a m)
      (FixedPairContentMarkerErase.startConfig B x w)
    p = FixedPairContentMarkerErase.finalConfig B x w ∧
    p.state = FixedPairContentMarkerErase.qAccept ∧
    (startConfig B x w).state = machine.start ∧
    (startConfig B x w).head = p.head ∧
    (startConfig B x w).tape = p.tape := by
  exact Pnp3.Complexity.Uniform.V1.FixedContentTagGate.handoff_exact x w

theorem check_run_deadline {a m B : Nat} (x : Bitstring a)
    (w : Bitstring m) :
    machine.run (deadline a m) (startConfig B x w) =
      finalConfig B x w := by
  exact Pnp3.Complexity.Uniform.V1.FixedContentTagGate.run_deadline x w

theorem check_exact_terminal_contract {a m B : Nat} (x : Bitstring a)
    (w : Bitstring m) :
    let z : Bitstring (a + m) := Fin.append x w
    let base : Fin (tapeLength (pairLength a m) B) → Option Bool :=
      FixedPairContentMarkerErase.contentTape B x w
    let rejected (j : Nat) (hj : j ≤ a + m) :
        Config stateCount (pairLength a m) B :=
      { state := machine.reject
        head := ⟨j, by unfold tapeLength pairLength; omega⟩
        tape := base }
    let accepted (hL : 8 ≤ a + m) :
        Config stateCount (pairLength a m) B :=
      { state := machine.accept
        head := ⟨8, by unfold tapeLength pairLength; omega⟩
        tape := base }
    (a + m = 0 →
      (∀ s < 2,
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run 2 (startConfig B x w) = rejected 0 (by omega)) ∧
    (∀ (j : Nat), (hpos : 0 < a + m) → (hj7 : j ≤ 7) →
      (hjL : j ≤ a + m) →
      (∀ i : Fin 8, i.1 < j →
        physicalSymbol z i.1 = some (expectedTagBit i)) →
      physicalSymbol z j ≠ some (expectedTagBit ⟨j, by omega⟩) →
      (∀ s < 3 * (a + m) + j,
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (3 * (a + m) + j) (startConfig B x w) =
        rejected j hjL) ∧
    ((hpos : 0 < a + m) → (hshort : a + m < 8) →
      (∀ i : Fin 8, i.1 < a + m →
        physicalSymbol z i.1 = some (expectedTagBit i)) →
      (∀ s < 4 * (a + m),
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      (machine.run (4 * (a + m)) (startConfig B x w)).state =
        machine.reject ∧
      (machine.run (4 * (a + m)) (startConfig B x w)).head.1 =
        a + m ∧
      (machine.run (4 * (a + m)) (startConfig B x w)).tape = base) ∧
    (∀ h : (∀ i : Fin 8,
        physicalSymbol z i.1 = some (expectedTagBit i)),
      (∀ s < deadline a m,
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (deadline a m) (startConfig B x w) = accepted (by
        have h7 := h ⟨7, by decide⟩
        unfold physicalSymbol at h7
        split at h7
        · rename_i hlt
          change 7 < a + m at hlt
          omega
        · simp at h7)) := by
  exact Pnp3.Complexity.Uniform.V1.FixedContentTagGate.exact_terminal_contract x w

theorem check_phase_contract {a m : Nat} (x : Bitstring a)
    (w : Bitstring m) :
    (∀ B s, s ≤ deadline a m →
      (machine.run s (startConfig B x w)).head.1 ≤ a + m) ∧
    (∀ B s, s < deadline a m →
      let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .right →
        c.head.1 + 1 < tapeLength (pairLength a m) B) ∧
    (∀ B s, s < deadline a m →
      let c := machine.run s (startConfig B x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .left ∧
          c.head.1 = 0 ↔
        s = if a + m = 0 then 0 else 3 * (a + m) - 2)) ∧
    (∀ B, (machine.run (deadline a m) (startConfig B x w)).tape =
      FixedPairContentMarkerErase.contentTape B x w) ∧
    (∀ B (i : Fin (tapeLength (pairLength a m) B)), a + m ≤ i.1 →
      (machine.run (deadline a m) (startConfig B x w)).tape i = none) ∧
    (∀ B extra, machine.run (deadline a m + extra)
      (startConfig B x w) = finalConfig B x w) ∧
    (∀ B B' s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.1 = c'.head.1 ∧
      ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')),
        i.1 = i'.1 → c.tape i = c'.tape i') := by
  exact Pnp3.Complexity.Uniform.V1.FixedContentTagGate.phase_contract x w

end Pnp3.Tests.UniformV1FixedContentTagGateSurfaceTests
