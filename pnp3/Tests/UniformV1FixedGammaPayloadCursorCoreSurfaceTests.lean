import Complexity.Uniform.V1.FixedGammaPayloadCursorCore

namespace Pnp3.Tests.UniformV1FixedGammaPayloadCursorCoreSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadCursorCore

def check_stateCount : Nat := stateCount
def check_qStart : Fin stateCount := qStart
def check_qBackFirst : Fin stateCount := qBackFirst
def check_qBackSeen : Fin stateCount := qBackSeen
def check_qSpend : Fin stateCount := qSpend
def check_qSeekTerm : Fin stateCount := qSeekTerm
def check_qRead : Fin stateCount := qRead
def check_qNextFalse : Fin stateCount := qNextFalse
def check_qRestoreOne : Fin stateCount := qRestoreOne
def check_qRestoreVirtual : Fin stateCount := qRestoreVirtual
def check_qFillOne : Fin stateCount := qFillOne
def check_qFillVirtual : Fin stateCount := qFillVirtual
def check_qOne : Fin stateCount := qOne
def check_qVirtual : Fin stateCount := qVirtual
def check_qReject : Fin stateCount := qReject
def check_machine : UniformTM := machine

def check_retag {N B : Nat} :
    Config FixedContentGammaAnchor.stateCount N B → Config stateCount N B := retag

def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  fun B => startConfig B

def check_nextTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Nat → Fin (tapeLength (pairLength a m) B) → Option Bool := nextTape B x w

def check_NextInvariant {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Nat → Config stateCount (pairLength a m) B → Prop := NextInvariant B x w

theorem check_table_and_resource_pins :
    (∀ s, machine.step qStart s = match s with
      | some true => (qBackFirst, some true, .left)
      | some false => (qReject, some false, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qBackFirst s = match s with
      | some false => (qBackSeen, some false, .left)
      | none => (qVirtual, some false, .stay)
      | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qBackSeen s = match s with
      | some false => (qBackSeen, some false, .left)
      | none => (qSpend, none, .right)
      | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qSpend s = match s with
      | some false => (qSeekTerm, none, .right)
      | some true => (qReject, some true, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qSeekTerm s = match s with
      | some false => (qSeekTerm, some false, .right)
      | some true => (qRead, some true, .right)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRead s = match s with
      | some false => (qNextFalse, none, .stay)
      | some true => (qRestoreOne, some true, .left)
      | none => (qRestoreVirtual, none, .left)) ∧
    (∀ s, machine.step qNextFalse s = (qNextFalse, s, .stay)) ∧
    (∀ s, machine.step qRestoreOne s = match s with
      | none => (qFillOne, some false, .left)
      | some b => (qRestoreOne, some b, .left)) ∧
    (∀ s, machine.step qRestoreVirtual s = match s with
      | none => (qFillVirtual, some false, .left)
      | some b => (qRestoreVirtual, some b, .left)) ∧
    (∀ s, machine.step qFillOne s = match s with
      | none => (qOne, some false, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.step qFillVirtual s = match s with
      | none => (qVirtual, some false, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.step qOne s = (qOne, s, .stay)) ∧
    (∀ s, machine.step qVirtual s = (qVirtual, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 14 ∧ machine.start = qStart ∧
    machine.accept = qOne ∧ machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 42 :=
  table_and_resource_pins

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let p := FixedContentGammaAnchor.machine.run
      (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w)
    let c := startConfig B x w
    p = FixedContentGammaAnchor.finalConfig B x w ∧ c = retag p ∧
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_exact x w htag

theorem check_zero_width_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let c := machine.run 2 (startConfig B x w)
    c.state = qVirtual ∧ c.head.val = 7 ∧
      c.tape = FixedPairContentMarkerErase.contentTape B x w :=
  zero_width_exact x w htag hg

theorem check_successful_handoff_exact {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let p := FixedContentGammaAnchor.machine.run
      (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w)
    let c := startConfig B x w
    p.state = FixedContentGammaAnchor.machine.accept ∧
    p.head.val = 8 + zeros ∧ p.tape = FixedContentGammaAnchor.markedTape B x w ∧
    c = retag p :=
  successful_handoff_exact x w htag hg

theorem check_read_partition {N B : Nat} (c : Config stateCount N B)
    (hq : c.state = qRead) :
    (c.tape c.head = some false →
      (machine.stepConfig c).state = qNextFalse ∧
      (machine.stepConfig c).head = c.head ∧
      (machine.stepConfig c).tape c.head = none) ∧
    (c.tape c.head = some true →
      (machine.stepConfig c).state = qRestoreOne ∧
      (machine.stepConfig c).head.val = c.head.val - 1 ∧
      (machine.stepConfig c).tape = c.tape) ∧
    (c.tape c.head = none →
      (machine.stepConfig c).state = qRestoreVirtual ∧
      (machine.stepConfig c).head.val = c.head.val - 1 ∧
      (machine.stepConfig c).tape = c.tape) :=
  read_partition c hq

theorem check_first_read_reachable {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) :
    let c := machine.run (2 * zeros + 3) (startConfig B x w)
    c.state = qRead ∧ c.head.val = 9 + zeros ∧
      c.tape = (fun i => if i.val = 7 ∨ i.val = 8 then none else
        FixedPairContentMarkerErase.contentTape B x w i) :=
  first_read_reachable x w htag hg hzero

theorem check_first_physical_false_exact {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (hfalse : (Fin.append x w) ⟨9 + zeros, hp⟩ = false) :
    NextInvariant B x w zeros (machine.run (2 * zeros + 4) (startConfig B x w)) :=
  first_physical_false_exact x w htag hg hzero hp hfalse

theorem check_first_physical_true_exact {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (htrue : (Fin.append x w) ⟨9 + zeros, hp⟩ = true) :
    machine.run (3 * zeros + 6) (startConfig B x w) =
      ⟨qOne, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ :=
  first_physical_true_exact x w htag hg hzero hp htrue

theorem check_first_virtual_exact {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hvirtual : 9 + zeros = a + m) :
    machine.run (3 * zeros + 6) (startConfig B x w) =
      ⟨qVirtual, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ :=
  first_virtual_exact x w htag hg hzero hvirtual

theorem check_tracer_no_clamp_facts {a m B zeros : Nat}
    (hgamma : 8 + zeros < a + m) :
    0 < 7 ∧ 8 < tapeLength (pairLength a m) B ∧
    8 + zeros + 1 < tapeLength (pairLength a m) B ∧
    9 + zeros ≤ a + m :=
  tracer_no_clamp_facts hgamma

theorem check_nextTape_footprint {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B))
    (hi : i.val ≠ 7) (hi8 : i.val ≠ 8) (hip : i.val ≠ 9 + zeros) :
    nextTape B x w zeros i = FixedPairContentMarkerErase.contentTape B x w i :=
  nextTape_footprint x w i hi hi8 hip

private def concreteRead (s : Option Bool) : Config stateCount 10 1 :=
  ⟨qRead, ⟨10, by decide⟩, fun _ => s⟩

private theorem concrete_first_physical_false_trace :
    let c := machine.run 1 (concreteRead (some false))
    c.state = qNextFalse ∧ c.head.val = 10 ∧ c.tape c.head = none := by decide

private theorem concrete_first_physical_true_trace :
    let c := machine.run 1 (concreteRead (some true))
    c.state = qRestoreOne ∧ c.head.val = 9 ∧ c.tape c.head = some true := by decide

private theorem concrete_first_virtual_trace :
    let c := machine.run 1 (concreteRead none)
    c.state = qRestoreVirtual ∧ c.head.val = 9 ∧ c.tape ⟨10, by decide⟩ = none := by decide

private def concreteZero : Config stateCount 8 1 :=
  ⟨qBackFirst, ⟨7, by decide⟩, fun i => if i.val = 7 then none else some true⟩

private theorem concrete_zero_width_restoration_trace :
    let c := machine.run 1 concreteZero
    c.state = qVirtual ∧ c.head.val = 7 ∧ c.tape ⟨7, by decide⟩ = some false := by decide

private def concreteOneCleanup : Config stateCount 10 1 :=
  ⟨qRead, ⟨10, by decide⟩,
    fun i => if i.val = 7 ∨ i.val = 8 then none else some true⟩

private theorem concrete_physical_true_complete_restoration_trace :
    let c := machine.run 4 concreteOneCleanup
    c.state = qOne ∧ c.head.val = 6 ∧
      c.tape = fun i => if i.val = 7 ∨ i.val = 8 then some false else some true := by decide

private def concreteVirtualCleanup : Config stateCount 10 1 :=
  ⟨qRead, ⟨10, by decide⟩,
    fun i => if i.val = 7 ∨ i.val = 8 ∨ i.val = 10 then none else some true⟩

private theorem concrete_virtual_complete_restoration_trace :
    let c := machine.run 4 concreteVirtualCleanup
    c.state = qVirtual ∧ c.head.val = 6 ∧
      c.tape = fun i => if i.val = 10 then none else
        if i.val = 7 ∨ i.val = 8 then some false else some true := by decide

end Pnp3.Tests.UniformV1FixedGammaPayloadCursorCoreSurfaceTests
