import Complexity.Uniform.V1.FixedPairParserAmbient

/-!
# Surface pins for the ambient-budget fixed pair parser

Every public theorem in `FixedPairParserAmbient` has one fully typed wrapper
here.  The three public definitions are pinned by typed `#check` commands.
The central dependency audit should root each source theorem and its wrapper.
-/

namespace Pnp3.Tests.UniformV1FixedPairParserAmbientSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairParser

#check (tapeEmbed :
  ∀ {N C B : Nat}, C ≤ B →
    Fin (tapeLength N C) → Fin (tapeLength N B))

#check (tapeProject :
  ∀ {N C B : Nat}, C ≤ B →
    Fin (tapeLength N B) → Option (Fin (tapeLength N C)))

#check (ConfigExtension :
  ∀ {k N C B : Nat}, C ≤ B →
    Config k N C → Config k N B → Prop)

theorem check_tapeEmbed_val {N C B : Nat} (hCB : C ≤ B)
    (i : Fin (tapeLength N C)) :
    (tapeEmbed hCB i).val = i.val :=
  tapeEmbed_val hCB i

theorem check_tapeEmbed_injective {N C B : Nat} (hCB : C ≤ B) :
    Function.Injective (tapeEmbed hCB :
      Fin (tapeLength N C) → Fin (tapeLength N B)) :=
  tapeEmbed_injective hCB

theorem check_tapeProject_tapeEmbed {N C B : Nat} (hCB : C ≤ B)
    (i : Fin (tapeLength N C)) :
    tapeProject hCB (tapeEmbed hCB i) = some i :=
  tapeProject_tapeEmbed hCB i

theorem check_tapeProject_eq_none_iff {N C B : Nat} (hCB : C ≤ B)
    (j : Fin (tapeLength N B)) :
    tapeProject hCB j = none ↔ tapeLength N C ≤ j.val :=
  tapeProject_eq_none_iff hCB j

theorem check_tapeEmbed_tapeProject_of_eq_some {N C B : Nat}
    (hCB : C ≤ B) (j : Fin (tapeLength N B))
    (i : Fin (tapeLength N C))
    (hproject : tapeProject hCB j = some i) :
    tapeEmbed hCB i = j :=
  tapeEmbed_tapeProject_of_eq_some hCB j i hproject

theorem check_initialConfig_extension (M : UniformTM) {N C B : Nat}
    (hCB : C ≤ B) (y : Bitstring N) :
    ConfigExtension hCB
      (initialConfig M C y) (initialConfig M B y) :=
  initialConfig_extension M hCB y

theorem check_ambient_initial_tape_behavior {N B : Nat}
    (y : Bitstring N) :
    (∀ i : Fin N,
      (initialConfig machine B y).tape
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_add_right N (B + 1))⟩ = some (y i)) ∧
    (∀ j : Fin (tapeLength N B), N ≤ j.val →
      (initialConfig machine B y).tape j = none) :=
  ambient_initial_tape_behavior y

theorem check_moveHead_tapeEmbed {N C B : Nat} (hCB : C ≤ B)
    (i : Fin (tapeLength N C)) (move : Move)
    (hroom : i.val + 1 < tapeLength N C) :
    moveHead (tapeEmbed hCB i) move =
      tapeEmbed hCB (moveHead i move) :=
  moveHead_tapeEmbed hCB i move hroom

theorem check_stepConfig_extension (M : UniformTM) {N C B : Nat}
    (hCB : C ≤ B)
    {small : Config M.stateCount N C}
    {large : Config M.stateCount N B}
    (hrel : ConfigExtension hCB small large)
    (hroom : small.head.val + 1 < tapeLength N C) :
    ConfigExtension hCB (M.stepConfig small) (M.stepConfig large) :=
  stepConfig_extension M hCB hrel hroom

theorem check_run_extension (M : UniformTM) {N C B : Nat}
    (hCB : C ≤ B)
    {small₀ : Config M.stateCount N C}
    {large₀ : Config M.stateCount N B}
    (h₀ : ConfigExtension hCB small₀ large₀)
    (steps : Nat)
    (hroom : ∀ s, s < steps →
      (M.run s small₀).head.val + 1 < tapeLength N C) :
    ConfigExtension hCB (M.run steps small₀) (M.run steps large₀) :=
  run_extension M hCB h₀ steps hroom

theorem check_exact_head_le_input_through_clock {N : Nat}
    (y : Bitstring N) (steps : Nat) (hsteps : steps ≤ clock N) :
    (machine.run steps (exactInitial y)).head.val ≤ N :=
  exact_head_le_input_through_clock y steps hsteps

theorem check_exact_head_right_room_through_clock {N : Nat}
    (y : Bitstring N) (steps : Nat) (hsteps : steps ≤ clock N) :
    (machine.run steps (exactInitial y)).head.val + 1 <
      tapeLength N (clock N) :=
  exact_head_right_room_through_clock y steps hsteps

theorem check_ambient_run_extension {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (steps : Nat) (hsteps : steps ≤ clock N) :
    ConfigExtension hB
      (machine.run steps (initialConfig machine (clock N) y))
      (machine.run steps (initialConfig machine B y)) :=
  ambient_run_extension y hB steps hsteps

theorem check_ambient_extra_cells_blank_through_clock {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (steps : Nat) (hsteps : steps ≤ clock N)
    (j : Fin (tapeLength N B))
    (hj : tapeLength N (clock N) ≤ j.val) :
    (machine.run steps (initialConfig machine B y)).tape j = none :=
  ambient_extra_cells_blank_through_clock y hB steps hsteps j hj

theorem check_ambient_padding_blank_through_clock {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (steps : Nat) (hsteps : steps ≤ clock N)
    (j : Fin (tapeLength N B)) (hjN : N ≤ j.val) :
    (machine.run steps (initialConfig machine B y)).tape j = none :=
  ambient_padding_blank_through_clock y hB steps hsteps j hjN

theorem check_ambient_acceptsAt_iff_exact {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (steps : Nat) (hsteps : steps ≤ clock N) :
    AcceptsAt machine B steps y ↔
      AcceptsAt machine (clock N) steps y :=
  ambient_acceptsAt_iff_exact y hB steps hsteps

theorem check_ambient_rejectsAt_iff_exact {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (steps : Nat) (hsteps : steps ≤ clock N) :
    RejectsAt machine B steps y ↔
      RejectsAt machine (clock N) steps y :=
  ambient_rejectsAt_iff_exact y hB steps hsteps

theorem check_ambient_run_initialConfig_exact {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    machine.run (clock N) (initialConfig machine B y) =
      { initialConfig machine B y with state := expectedFinalState y } :=
  ambient_run_initialConfig_exact y hB

theorem check_ambient_run_initialConfig_accept {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) (p : DecodedPair)
    (hdecode : decodePair y = some p) :
    machine.run (clock N) (initialConfig machine B y) =
      { initialConfig machine B y with state := qAccept } :=
  ambient_run_initialConfig_accept y hB p hdecode

theorem check_ambient_run_initialConfig_reject {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (hdecode : decodePair y = none) :
    machine.run (clock N) (initialConfig machine B y) =
      { initialConfig machine B y with state := qReject } :=
  ambient_run_initialConfig_reject y hB hdecode

theorem check_ambient_final_literal_state {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    (machine.run (clock N) (initialConfig machine B y)).state =
      match decodePair y with
      | some _ => qAccept
      | none => qReject :=
  ambient_final_literal_state y hB

theorem check_ambient_head_literal_zero_at_clock {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    (machine.run (clock N) (initialConfig machine B y)).head =
      (⟨0, by simp [tapeLength]⟩ : Fin (tapeLength N B)) :=
  ambient_head_literal_zero_at_clock y hB

theorem check_ambient_tape_restored_at_clock {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    (machine.run (clock N) (initialConfig machine B y)).tape =
      (initialConfig machine B y).tape :=
  ambient_tape_restored_at_clock y hB

theorem check_ambient_final_tape_behavior {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    let cF := machine.run (clock N) (initialConfig machine B y)
    (∀ i : Fin N,
      cF.tape
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_add_right N (B + 1))⟩ = some (y i)) ∧
    (∀ j : Fin (tapeLength N B), N ≤ j.val → cF.tape j = none) :=
  ambient_final_tape_behavior y hB

theorem check_ambient_no_public_terminal_before_clock {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (steps : Nat) (hsteps : steps < clock N) :
    ¬ AcceptsAt machine B steps y ∧ ¬ RejectsAt machine B steps y :=
  ambient_no_public_terminal_before_clock y hB steps hsteps

theorem check_ambient_acceptsAt_clock_iff_decodePair_some {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    AcceptsAt machine B (clock N) y ↔
      ∃ p : DecodedPair, decodePair y = some p :=
  ambient_acceptsAt_clock_iff_decodePair_some y hB

theorem check_ambient_rejectsAt_clock_iff_decodePair_none {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    RejectsAt machine B (clock N) y ↔ decodePair y = none :=
  ambient_rejectsAt_clock_iff_decodePair_none y hB

theorem check_ambient_decidesWithin {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    DecidesWithin machine B y (decodePair y).isSome :=
  ambient_decidesWithin y hB

end Pnp3.Tests.UniformV1FixedPairParserAmbientSurfaceTests
