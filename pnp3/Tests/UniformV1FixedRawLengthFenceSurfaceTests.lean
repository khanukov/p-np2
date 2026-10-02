import Complexity.Uniform.V1.FixedRawLengthFenceHandoff

/-! G3r Infrastructure: named full propositions plus independent finite executions. -/
namespace Pnp3.Tests.UniformV1FixedRawLengthFenceSurfaceTests
open Complexity.Uniform.V1 FixedRawLengthFence
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

theorem check_table_and_resource_pins :
    machine.stateCount = 48 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 144 ∧
    machine.start.val = 0 ∧ machine.accept.val = 2 ∧ machine.reject.val = 3 ∧
    (∀ q s, machine.step q s = machine.rawStep q s) :=
  table_and_resource_pins

/-- Public endpoint data and the unchanged suffix, with no run hypotheses. -/
theorem check_endpoint_definitions {R : Nat} (B : Nat) (input : Bitstring R) :
    fencePos R = 3*R+2 ∧
    installClock R = (if R = 0 then 4 else 3*R*R+9*R+5) ∧
    allocation R = 16*(R+1)^2 ∧
    fenceTape B input = (fun i => if h : i.val < R then some (input ⟨i.val,h⟩)
      else if i.val = fencePos R then some false else none) ∧
    installedConfig B input =
      ⟨machine.accept, ⟨0, by simp [tapeLength]⟩, fenceTape B input⟩ ∧
    G = FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine ∧
    prefixed = machine.seq G ∧
    g3qEntry B input = ⟨G.start, ⟨0, by simp [tapeLength]⟩, fenceTape B input⟩ := by
  repeat' apply And.intro
  all_goals rfl

theorem check_install_exact {R B : Nat} (input : Bitstring R) (hroom : 2*R+2 ≤ B) :
    machine.run (installClock R) (initialConfig machine B input) = installedConfig B input :=
  install_exact input hroom

theorem check_install_trace {R B : Nat} (input : Bitstring R) (hroom : 2*R+2 ≤ B) :
    (∀ t, t < installClock R →
      (machine.run t (initialConfig machine B input)).state ≠ machine.accept ∧
      (machine.run t (initialConfig machine B input)).state ≠ machine.reject) ∧
    (∀ t, t ≤ installClock R →
      (machine.run t (initialConfig machine B input)).head.val ≤ fencePos R) ∧
    (∀ t, t < installClock R →
      let c := machine.run t (initialConfig machine B input)
      let mv := (machine.step c.state (c.tape c.head)).2.2
      (mv = Move.left → 0 < c.head.val) ∧
      (mv = Move.right → c.head.val+1 < tapeLength R B)) :=
  install_trace input hroom

theorem check_installed_cells {R B : Nat} (input : Bitstring R) (hroom : 2*R+2 ≤ B) :
    let c := machine.run (installClock R) (initialConfig machine B input)
    (∀ i : Fin R, c.tape ⟨i.val, by have := i.isLt; unfold tapeLength; omega⟩ = some (input i)) ∧
    (∀ i : Fin (tapeLength R B), R ≤ i.val →
      c.tape i = if i.val = fencePos R then some false else none) ∧
    (∃ i : Fin (tapeLength R B), i.val = fencePos R ∧ c.tape i = some false) :=
  installed_cells input hroom

theorem check_resource_bounds (R : Nat) : 2*R+2 ≤ allocation R ∧ installClock R ≤ allocation R :=
  resource_bounds R

theorem check_raw_install_exact {R : Nat} (input : Bitstring R) :
    machine.run (installClock R) (initialConfig machine (allocation R) input) =
      installedConfig (allocation R) input := raw_install_exact input

theorem check_prefixed_pins :
    prefixed.stateCount = 256 ∧ Fintype.card (Fin prefixed.stateCount × Option Bool) = 768 ∧
    prefixed.start.val = 0 ∧ prefixed.accept.val = 254 ∧ prefixed.reject.val = 255 ∧
    (machine.seqRight G G.start).val = 48 :=
  prefixed_pins

theorem check_fence_handoff_exact {R B : Nat} (input : Bitstring R)
    (hroom : 2*R+2 ≤ B) (s : Nat) :
    prefixed.run (installClock R+s) (initialConfig prefixed B input) =
      machine.seqEmbedRight G (G.run s (g3qEntry B input)) :=
  fence_handoff_exact input hroom s

theorem check_raw_fence_handoff_exact {R : Nat} (input : Bitstring R) (s : Nat) :
    prefixed.run (installClock R+s) (initialConfig prefixed (allocation R) input) =
      machine.seqEmbedRight G (G.run s (g3qEntry (allocation R) input)) :=
  raw_fence_handoff_exact input s

private def snapshot {R : Nat} (B t : Nat) (x : Bitstring R) :=
  let c := machine.run t (initialConfig machine B x)
  (c.state.val, c.head.val, List.ofFn c.tape)
private def emptyWord : Bitstring 0 := Fin.elim0
private def mixed : Bitstring 3 := ![true,false,true]

/-- Literal complete configurations, independent of the universal proof. -/
theorem check_small_runs :
    snapshot 2 4 emptyWord = (2,0,[none,none,some false]) ∧
    snapshot 4 17 (![false] : Bitstring 1) =
      (2,0,[some false,none,none,none,none,some false]) ∧
    snapshot 4 17 (![true] : Bitstring 1) =
      (2,0,[some true,none,none,none,none,some false]) ∧
    snapshot 6 35 (![false,false] : Bitstring 2) =
      (2,0,[some false,some false,none,none,none,none,none,none,some false]) ∧
    snapshot 6 35 (![true,true] : Bitstring 2) =
      (2,0,[some true,some true,none,none,none,none,none,none,some false]) ∧
    snapshot 6 35 (![false,true] : Bitstring 2) =
      (2,0,[some false,some true,none,none,none,none,none,none,some false]) ∧
    snapshot 8 59 mixed =
      (2,0,[some true,some false,some true,none,none,none,none,none,none,none,none,some false]) := by
  repeat' apply And.intro
  all_goals decide

/-- Extra allocation changes neither the marker address nor input restoration. -/
theorem check_extra_room :
    snapshot 3 4 emptyWord = (2,0,[none,none,some false,none]) ∧
    snapshot 9 59 mixed =
      (2,0,[some true,some false,some true,none,none,none,none,none,none,none,none,some false,none]) := by
  decide

/-- All steps of the mixed minimum-room execution, not just a terminal snapshot. -/
theorem check_mixed_trace :
    (∀ t : Fin 59,
      let c := machine.run t.val (initialConfig machine 8 mixed)
      c.state.val ≠ 2 ∧ c.state.val ≠ 3 ∧ c.head.val ≤ 11 ∧
      let mv := (machine.step c.state (c.tape c.head)).2.2
      (mv = .left → 0 < c.head.val) ∧ (mv = .right → c.head.val+1 < 12)) ∧
    (machine.run 58 (initialConfig machine 8 mixed)).state.val = 47 := by
  decide

/-- Below-room acceptance can put the marker at the wrong address. No all-budget claim. -/
theorem check_insufficient_room :
    snapshot 1 4 emptyWord = (2,0,[none,some false]) ∧
    (machine.run 1 (initialConfig machine 1 emptyWord)).head.val = 1 ∧
    (machine.run 2 (initialConfig machine 1 emptyWord)).head.val = 1 ∧
    snapshot 3 16 (![true] : Bitstring 1) = (2,0,[some true,none,none,none,some false]) ∧
    snapshot 5 34 (![true,true] : Bitstring 2) =
      (2,0,[some true,some true,none,none,none,none,none,some false]) := by
  decide

/-- The capstone's fixed-allocation witness carries all 260 tape cells into G3q. -/
theorem check_raw_capstone :
    allocation 3 = 256 ∧ installClock 3 = 59 ∧ fencePos 3 = 11 ∧
    prefixed.run 59 (initialConfig prefixed 256 mixed) =
      ⟨machine.seqRight G G.start, ⟨0,by simp [tapeLength]⟩,
        fun i => if i.val = 0 then some true else if i.val = 1 then some false
          else if i.val = 2 then some true else if i.val = 11 then some false else none⟩ := by
  refine ⟨rfl,rfl,rfl,?_⟩
  have h := raw_fence_handoff_exact mixed 0
  change prefixed.run 59 (initialConfig prefixed 256 mixed) = _ at h
  rw [h]
  apply Config.ext_parts
  · rfl
  · rfl
  · funext i
    change fenceTape 256 mixed i = _
    by_cases hi : i.val < 3
    · have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hc with h | h | h <;> simp [fenceTape,mixed,h]
    · simp [fenceTape,fencePos,hi,show i.val ≠ 0 by omega,
        show i.val ≠ 1 by omega,show i.val ≠ 2 by omega]

/-- A literal composed run independently checks the minimum-room handoff. -/
theorem check_handoff_literal :
    let c := prefixed.run 59 (initialConfig prefixed 8 mixed)
    c.state.val = 48 ∧ c.head.val = 0 ∧ List.ofFn c.tape =
      [some true,some false,some true,none,none,none,none,none,none,none,none,some false] := by
  decide

end Pnp3.Tests.UniformV1FixedRawLengthFenceSurfaceTests
