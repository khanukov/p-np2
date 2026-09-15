import Complexity.Uniform.V1.FixedGammaPayloadRoundStep

namespace Pnp3.Tests.UniformV1FixedGammaPayloadRoundStepSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadRoundStep

def check_stateCount : Nat := stateCount
def check_qStart : Fin stateCount := qStart
def check_qBackPayload : Fin stateCount := qBackPayload
def check_qBackCounter : Fin stateCount := qBackCounter
def check_qSpend : Fin stateCount := qSpend
def check_qSeekTerm : Fin stateCount := qSeekTerm
def check_qSeekHole : Fin stateCount := qSeekHole
def check_qRead : Fin stateCount := qRead
def check_qExhausted : Fin stateCount := qExhausted
def check_qOnePending : Fin stateCount := qOnePending
def check_qVirtualPending : Fin stateCount := qVirtualPending
def check_qReject : Fin stateCount := qReject
def check_machine : UniformTM := machine
def check_coreTime : Nat → Nat := coreTime
def check_roundCost : Nat → Nat := roundCost

def check_retag {N B : Nat} :
    Config FixedGammaPayloadCursorCore.stateCount N B → Config stateCount N B := retag

def check_startConfig {a m : Nat} : (B : Nat) → Bitstring a → Bitstring m → Nat →
    Config stateCount (pairLength a m) B := fun B x w => startConfig B x w

def check_roundTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Nat → Nat → Fin (tapeLength (pairLength a m) B) → Option Bool := roundTape B x w

def check_RoundInvariant {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Nat → Nat → Config stateCount (pairLength a m) B → Prop := RoundInvariant B x w

theorem check_table_and_resource_pins :
    (∀ s, machine.step qStart s = match s with
      | none => (qBackPayload, none, .left) | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.step qBackPayload s = match s with
      | some false => (qBackPayload, some false, .left)
      | some true => (qBackCounter, some true, .left) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qBackCounter s = match s with
      | some false => (qBackCounter, some false, .left)
      | none => (qSpend, none, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qSpend s = match s with
      | some false => (qSeekTerm, none, .right)
      | some true => (qExhausted, some true, .stay) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qSeekTerm s = match s with
      | some false => (qSeekTerm, some false, .right)
      | some true => (qSeekHole, some true, .right) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qSeekHole s = match s with
      | some false => (qSeekHole, some false, .right)
      | none => (qRead, some false, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qRead s = match s with
      | some false => (qStart, none, .stay)
      | some true => (qOnePending, some true, .stay)
      | none => (qVirtualPending, none, .stay)) ∧
    (∀ s, machine.step qExhausted s = (qExhausted, s, .stay)) ∧
    (∀ s, machine.step qOnePending s = (qOnePending, s, .stay)) ∧
    (∀ s, machine.step qVirtualPending s = (qVirtualPending, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 11 ∧ machine.start = qStart ∧ machine.accept = qOnePending ∧
    machine.reject = qReject ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 33 :=
  table_and_resource_pins

theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (hfalse : (Fin.append x w) ⟨9 + zeros, hp⟩ = false) :
    RoundInvariant B x w zeros 1 (startConfig B x w zeros) :=
  handoff_exact x w htag hg hzero hp hfalse

theorem check_round_false_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros) (hp : 9 + zeros + k < a + m)
    (hfalse : (Fin.append x w) ⟨9 + zeros + k, hp⟩ = false)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B) (hc : RoundInvariant B x w zeros k c) :
    RoundInvariant B x w zeros (k + 1) (machine.run (roundCost zeros) c) :=
  round_false_exact x w hg hk hkz hp hfalse hprefix c hc

theorem check_second_round_reachable {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hp1 : 9 + zeros < a + m)
    (hfalse1 : (Fin.append x w) ⟨9 + zeros, hp1⟩ = false)
    (hp2 : 10 + zeros < a + m)
    (hfalse2 : (Fin.append x w) ⟨10 + zeros, hp2⟩ = false) :
    RoundInvariant B x w zeros 2
      (machine.run (roundCost zeros) (startConfig B x w zeros)) :=
  second_round_reachable x w htag hg hzeros hp1 hfalse1 hp2 hfalse2

theorem check_round_no_clamp_facts {a m B zeros k : Nat}
    (hk : 1 ≤ k) (hkz : k < zeros) (hp : 9 + zeros + k < a + m) :
    0 < 8 ∧ 8 + k < tapeLength (pairLength a m) B ∧
    9 + zeros + k < tapeLength (pairLength a m) B :=
  round_no_clamp_facts hk hkz hp

theorem check_roundTape_footprint {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hc : ¬(8 ≤ i.val ∧ i.val < 8 + k)) (hh : i.val ≠ 8 + zeros + k) :
    roundTape B x w zeros k i = FixedPairContentMarkerErase.contentTape B x w i :=
  roundTape_footprint x w i h7 hc hh

private def concreteRound : Config stateCount 16 1 :=
  ⟨qStart, ⟨11, by decide⟩, fun i =>
    if i.val = 7 ∨ i.val = 8 ∨ i.val = 11 then none
    else if i.val = 10 then some true else some false⟩

private theorem concrete_k1_to_k2_trace :
    let c := machine.run (roundCost 2) concreteRound
    c.state = qStart ∧ c.head.val = 12 ∧ c.tape ⟨11, by decide⟩ = some false ∧
      c.tape ⟨9, by decide⟩ = none ∧ c.tape ⟨12, by decide⟩ = none := by decide

end Pnp3.Tests.UniformV1FixedGammaPayloadRoundStepSurfaceTests
