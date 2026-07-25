import Pnp4.Frontier.SequentialMagnification.MMWMagnificationPort
import Pnp4.Frontier.SequentialMagnification.MuGapNoGo
import Pnp4.Frontier.SequentialMagnification.SequentialCapstone
import Pnp4.Frontier.SequentialMagnification.FoolingSet

/-!
# Falsifiability audit for the sequential-magnification port

The repository's standing rule is that a new source predicate must come with a
falsifiability audit *before* it is wired into a final theorem
(`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`, "Proof-Quality Safety Checks", item 3).
Every previously proposed source failed exactly this test: the predicates were
satisfiable for free by truth-table hardwiring, so the assumption collapsed to
`False`.

This module is that audit for `MCSPStreamingHard` and the port built on it.
Four things are checked, all kernel-verified:

| Probe | Question | Result |
|---|---|---|
| A | Is the hardness *shape* satisfiable at a fixed input length? | yes, `probeA_hard_function_exists` |
| B | Is the weak model trivially powerless (so hardness is free)? | no, `probeB_model_is_nontrivial` |
| C | Does fixed-slice hardwiring satisfy the model for free, as it does for `PpolyDAG`? | no, `probeC_hardwiring_costs_memory` |
| D | Is `MCSPStreamingHard` itself satisfiable, for the real MCSP predicate? | yes, `probeD_mcsp_streaming_hard_concrete` |
| E | Does padding close the published size-parameter gap? | no, `probeE_padding_nogo` |
| F | Is the locality price of a hitting-set generator real? | yes, `probeF_seed_length_obstruction` |
| G | Does the reduced chain actually reach `P ≠ NP`? | yes, `probeG_reduced_chain` |

Probe D is the one the earlier routes could never pass: it exhibits concrete
parameters at which the *actual* source predicate consumed by the port holds.

None of this proves `P ≠ NP`, and none of it proves the MCSP lower bound that
the port needs.  It establishes only that the port consumes a predicate which is
neither vacuous nor free.
-/

namespace Pnp4
namespace Tests
namespace SequentialMagnificationAudit

open Pnp4.Frontier.SequentialMagnification
open Pnp4.AlgorithmsToLowerBounds
open Pnp3.Models hiding truthTableFunction

/-!
## Probe A — the hardness shape is satisfiable
-/

/--
At any memory budget there is a Boolean function on a *single* input length
that no space-bounded one-pass algorithm decides.
-/
theorem probeA_hard_function_exists (space m : Nat) (h : space < m) :
    ∃ f : List Bool → Bool,
      ¬ ∃ A : SpaceBoundedStreaming space, A.SolvesLength (2 * m) f :=
  exists_streaming_hard_function_at_fixed_length space m h

/-!
## Probe B — the model is not trivially powerless
-/

/-- One bit of memory already decides a function that depends on all inputs. -/
theorem probeB_model_is_nontrivial (N : Nat) :
    parityBounded.SolvesLength N parityFn :=
  parity_solvable N

/-!
## Probe C — fixed-slice hardwiring is not free here
-/

/--
The contrast with `pnp3/Tests/HInDagTrivialityProbe.lean`.

There, a language supported on one input length is in `PpolyDAG` for free.
Here, being able to decide *every* function on one input length `2 * m` forces
a memory budget of at least `m` bits.
-/
theorem probeC_hardwiring_costs_memory (space m : Nat)
    (hAll : ∀ f : List Bool → Bool,
      ∃ A : SpaceBoundedStreaming space, A.SolvesLength (2 * m) f) :
    m ≤ space :=
  fixed_slice_hardwiring_costs_memory space m hAll

/-!
## Probe D — `MCSPStreamingHard` is satisfiable for the real MCSP predicate

This is the decisive probe.  The two probes above concern the abstract model;
this one concerns the exact predicate `MCSPStreamingHard` that
`MMWMagnificationPort.lean` consumes, with the repository's own MCSP semantics
(`circuitComplexityLE treeCircuitClass`).
-/

/-- The truth-table index map is injective. -/
theorem assignmentIndex_injective {n : Nat} :
    Function.Injective (@assignmentIndex n) := by
  intro x y hxy
  have hx := vecOfNat_assignmentIndex_val x
  have hy := vecOfNat_assignmentIndex_val y
  rw [← hx, ← hy, hxy]

/-- Every circuit has at least one gate. -/
theorem one_le_circuit_size {n : Nat} (c : Circuit n) : 1 ≤ c.size := by
  cases c <;> simp [Circuit.size]

/-- The all-false input on one variable. -/
def x₀ : Pnp3.Core.BitVec 1 := fun _ => false

/-- The all-true input on one variable. -/
def x₁ : Pnp3.Core.BitVec 1 := fun _ => true

theorem x₀_ne_x₁ : x₀ ≠ x₁ := by
  intro h
  have := congrFun h ⟨0, by omega⟩
  simp [x₀, x₁] at this

/-- `truthTableFunction` is table lookup at the assignment index. -/
theorem truthTableFunction_eq {n : Nat}
    (table : Pnp3.Core.BitVec (Partial.tableLen n)) (x : Pnp3.Core.BitVec n) :
    truthTableFunction table x = table (assignmentIndex x) := rfl

/-- Truth table of negation on one variable, defined via the index of `x₀`. -/
def notTable : TruthTable 1 :=
  fun i => decide (i = assignmentIndex x₀)

@[simp] theorem notTable_at_x₀ : truthTableFunction notTable x₀ = true := by
  rw [truthTableFunction_eq]
  simp [notTable]

@[simp] theorem notTable_at_x₁ : truthTableFunction notTable x₁ = false := by
  have hne : assignmentIndex x₁ ≠ assignmentIndex x₀ := by
    intro h
    exact x₀_ne_x₁ (assignmentIndex_injective h).symm
  rw [truthTableFunction_eq]
  simp [notTable, hne]

/-- Negation on one variable is not computed by any circuit of size `≤ 1`. -/
theorem notTable_hard :
    ¬ circuitComplexityLE treeCircuitClass 1 1 notTable := by
  rintro ⟨c, hsize, hcorrect⟩
  have hsize' : Circuit.size c ≤ 1 := hsize
  have h₀ : Circuit.eval c x₀ = true := by
    have := hcorrect x₀; simpa [treeCircuitClass] using this
  have h₁ : Circuit.eval c x₁ = false := by
    have := hcorrect x₁; simpa [treeCircuitClass] using this
  cases c with
  | input i =>
      have : x₀ i = true := h₀
      simp [x₀] at this
  | const b =>
      cases b with
      | false => simp [Circuit.eval] at h₀
      | true => simp [Circuit.eval] at h₁
  | not c' =>
      have := one_le_circuit_size c'
      simp [Circuit.size] at hsize'
      omega
  | and c₁ c₂ =>
      have h1 := one_le_circuit_size c₁
      have h2 := one_le_circuit_size c₂
      simp [Circuit.size] at hsize'
      omega
  | or c₁ c₂ =>
      have h1 := one_le_circuit_size c₁
      have h2 := one_le_circuit_size c₂
      simp [Circuit.size] at hsize'
      omega

/-- The constantly-false truth table has a size-`1` circuit. -/
theorem constFalseTable_easy :
    circuitComplexityLE treeCircuitClass 1 1 (fun _ => false) := by
  refine ⟨Circuit.const false, ?_, ?_⟩
  · simp [treeCircuitClass, Circuit.size]
  · intro x
    rw [truthTableFunction_eq]
    simp [treeCircuitClass, Circuit.eval]

/--
A zero-memory device answers the same on every input, so it cannot decide any
MCSP slice on which the answer actually varies.
-/
theorem MCSPStreamingHard_of_zero_space {n s : Nat} {tt₀ tt₁ : TruthTable n}
    (h0 : ¬ circuitComplexityLE treeCircuitClass n s tt₀)
    (h1 : circuitComplexityLE treeCircuitClass n s tt₁) :
    MCSPStreamingHard 0 n s := by
  rintro ⟨A, hA⟩
  have hcard : @Fintype.card A.State A.fintypeState ≤ 1 := by
    simpa using A.card_le
  have hconst : ∀ a b : A.State, a = b :=
    @Fintype.card_le_one_iff A.State A.fintypeState |>.mp hcard
  have hsame : A.decideOn (tableStream tt₀) = A.decideOn (tableStream tt₁) := by
    show A.algo.accept (A.algo.run (tableStream tt₀))
      = A.algo.accept (A.algo.run (tableStream tt₁))
    rw [hconst (A.algo.run (tableStream tt₀)) (A.algo.run (tableStream tt₁))]
  have hTrue₁ : A.decideOn (tableStream tt₁) = true := (hA tt₁).2 h1
  have hTrue₀ : A.decideOn (tableStream tt₀) = true := by
    rw [hsame]; exact hTrue₁
  exact h0 ((hA tt₀).1 hTrue₀)

/--
**Probe D.**  `MCSPStreamingHard` holds at concrete parameters: at zero memory,
one variable, and size threshold `1`.

This is a closed, kernel-checked satisfiability certificate for the exact
predicate consumed by `P_ne_NP_of_mcsp_streaming_hardness`.  It is of course far
below the budget the magnification contract supplies — the point is only that
the predicate is *not* refutable in the way every earlier source predicate was.
-/
theorem probeD_mcsp_streaming_hard_concrete : MCSPStreamingHard 0 1 1 :=
  MCSPStreamingHard_of_zero_space notTable_hard constFalseTable_easy

/-!
## Probe E — padding does not close the published size-parameter gap
-/

/-- Concrete instance of the padding no-go at the smallest nontrivial blowup. -/
theorem probeE_padding_nogo :
    chmyTimeExponentNum < mmwTimeExponentNum * 2 :=
  transferred_exponent_too_small 2 (by omega)


/-!
## Probe F — the locality price is real

`seedLength_bound_of_injective_localGenerator` says an injective local generator
at size parameter `s` cannot have more seeds than there are functions of circuit
complexity `≤ s`.  The degenerate instance below checks the statement bites:
at threshold `0` there are no circuits at all, so no generator exists.
-/

theorem probeF_seed_length_obstruction (n : Nat) :
    ¬ ∃ G : LocalGenerator n 0 1, Function.Injective G.gen := by
  refine no_injective_localGenerator_of_seed_too_long ?_
  simp [Pnp3.Models.circuitCountBound]

/-!
## Probe G — the reduced chain reaches the target

The capstone composes to `P ≠ NP` with exactly three inputs: the published MMW
contract, the Shannon-counting slack, and the hitting-set security of a local
generator.  Nothing else is consumed.
-/

theorem probeG_reduced_chain (w : LocalHSGWitness) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_localHSGWitness w

/-!
## Axiom surface
-/

#print axioms equality_forces_memory
#print axioms no_small_streaming_solver_for_equality
#print axioms fixed_slice_hardwiring_costs_memory
#print axioms padding_preserves_circuit_size
#print axioms padding_cannot_close_size_parameter_gap
#print axioms probeD_mcsp_streaming_hard_concrete
#print axioms P_ne_NP_of_mcsp_streaming_hardness
#print axioms P_ne_NP_of_sequentialGap
#print axioms P_ne_NP_of_closureRoute
#print axioms card_le_card_state_of_foolingFamily
#print axioms no_solver_of_large_foolingFamily
#print axioms mem_easyFunctions_of_circuitComplexityLE
#print axioms MCSPStreamingHard_of_localHSG
#print axioms seedLength_bound_of_injective_localGenerator
#print axioms no_injective_localGenerator_of_seed_too_long
#print axioms P_ne_NP_of_localHSG
#print axioms P_ne_NP_of_localHSGWitness

end SequentialMagnificationAudit
end Tests
end Pnp4
