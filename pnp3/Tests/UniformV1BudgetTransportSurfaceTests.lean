import Complexity.Uniform.V1.BudgetTransport

/-!
# Typed surface pins for generic Uniform V1 budget transport

Every public theorem introduced by `BudgetTransport` is restated with its full
proposition.  These wrappers are deliberately proof-only API pins; executable
machine semantics remain in the Uniform V1 foundation.
-/

namespace Pnp3.Tests.UniformV1BudgetTransportSurfaceTests

open Pnp3.Complexity.Uniform.V1

theorem check_stepConfig_head_le_succ (M : UniformTM)
    {N budget : Nat} (c : Config M.stateCount N budget) :
    (M.stepConfig c).head.val ≤ c.head.val + 1 :=
  M.stepConfig_head_le_succ c

theorem check_run_head_le (M : UniformTM)
    {N budget steps : Nat} (c : Config M.stateCount N budget) :
    (M.run steps c).head.val ≤ c.head.val + steps :=
  M.run_head_le c

theorem check_run_initialConfig_head_le (M : UniformTM)
    {N budget steps : Nat} (y : Bitstring N) :
    (M.run steps (initialConfig M budget y)).head.val ≤ steps :=
  M.run_initialConfig_head_le y

theorem check_run_initialConfig_right_room (M : UniformTM)
    {N C s : Nat} (y : Bitstring N) (hs : s ≤ C) :
    ∀ r, r < s →
      (M.run r (initialConfig M C y)).head.val + 1 < tapeLength N C :=
  M.run_initialConfig_right_room y hs

theorem check_run_initialConfig_extension (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    FixedPairParser.ConfigExtension hCB
      (M.run s (initialConfig M C y))
      (M.run s (initialConfig M B y)) :=
  M.run_initialConfig_extension y hs hCB

theorem check_run_initialConfig_state_eq (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    (M.run s (initialConfig M C y)).state =
      (M.run s (initialConfig M B y)).state :=
  M.run_initialConfig_state_eq y hs hCB

theorem check_acceptsAt_budget_iff (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    AcceptsAt M C s y ↔ AcceptsAt M B s y :=
  M.acceptsAt_budget_iff y hs hCB

theorem check_acceptsAt_budget_mono (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    AcceptsAt M C s y → AcceptsAt M B s y :=
  M.acceptsAt_budget_mono y hs hCB

theorem check_rejectsAt_budget_iff (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    RejectsAt M C s y ↔ RejectsAt M B s y :=
  M.rejectsAt_budget_iff y hs hCB

theorem check_rejectsAt_budget_mono (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    RejectsAt M C s y → RejectsAt M B s y :=
  M.rejectsAt_budget_mono y hs hCB

theorem check_decidesAt_budget_iff (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (answer : Bool)
    (hs : s ≤ C) (hCB : C ≤ B) :
    DecidesAt M C s y answer ↔ DecidesAt M B s y answer :=
  M.decidesAt_budget_iff y answer hs hCB

theorem check_decidesAt_budget_mono
    (M : UniformTM) {N C B s : Nat} (y : Bitstring N) (answer : Bool)
    (hs : s ≤ C) (hCB : C ≤ B) :
    DecidesAt M C s y answer → DecidesAt M B s y answer :=
  M.decidesAt_budget_mono y answer hs hCB

theorem check_acceptsWithin_budget_mono (M : UniformTM)
    {N C B : Nat} (y : Bitstring N) (hCB : C ≤ B) :
    AcceptsWithin M C y → AcceptsWithin M B y :=
  M.acceptsWithin_budget_mono y hCB

theorem check_rejectsWithin_budget_mono (M : UniformTM)
    {N C B : Nat} (y : Bitstring N) (hCB : C ≤ B) :
    RejectsWithin M C y → RejectsWithin M B y :=
  M.rejectsWithin_budget_mono y hCB

theorem check_decidesWithin_budget_mono (M : UniformTM)
    {N C B : Nat} (y : Bitstring N) (answer : Bool) (hCB : C ≤ B) :
    DecidesWithin M C y answer → DecidesWithin M B y answer :=
  M.decidesWithin_budget_mono y answer hCB

end Pnp3.Tests.UniformV1BudgetTransportSurfaceTests
