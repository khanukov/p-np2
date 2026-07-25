import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP
import Pnp4.Frontier.SequentialMagnification.StreamingLowerBounds

/-!
# MCSP as a one-pass streaming target

The McKay–Murray–Williams magnification theorem is a statement about MCSP
*read as a stream*: the input is the truth table of a Boolean function on `n`
variables, of length `N = 2 ^ n`, presented one bit at a time.

This module fixes that reading precisely, reusing the existing `pnp4`
truth-table / circuit-complexity surface (`TruthTableMCSP.lean`) so that the
MCSP semantics here are literally the same ones already used by the coin-problem
and local-PRG tracks.

Nothing in this module is an assumption.  It is only a translation layer:
truth table `↦` bit stream, plus the definition of "a space-bounded one-pass
algorithm decides the MCSP slice `(n, s)`".
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

open Pnp4.AlgorithmsToLowerBounds

/--
The canonical left-to-right presentation of a truth table as a bit stream.

`tableStream tt` has length `tableLen n = 2 ^ n`, which is the input length `N`
in every magnification statement about MCSP.
-/
def tableStream {n : Nat} (tt : TruthTable n) : List Bool :=
  List.ofFn tt

@[simp] lemma tableStream_length {n : Nat} (tt : TruthTable n) :
    (tableStream tt).length = Pnp3.Models.Partial.tableLen n := by
  simp [tableStream]

/--
A space-bounded one-pass streaming algorithm *decides the MCSP slice* `(n, s)`
if, on every truth table of `n`-variable functions, it accepts exactly when the
function has a tree circuit of size at most `s`.

The right-hand side is the repository's existing proof-level MCSP predicate
`circuitComplexityLE treeCircuitClass`, so this is the same MCSP as elsewhere in
`pnp4`, not a new one.
-/
def SolvesMCSPSlice {space : Nat} (A : SpaceBoundedStreaming space)
    (n s : Nat) : Prop :=
  ∀ tt : TruthTable n,
    A.decideOn (tableStream tt) = true ↔
      circuitComplexityLE treeCircuitClass n s tt

/--
`MCSP[s]` at slice `n` admits a one-pass streaming solver with `space` bits of
memory.
-/
def MCSPStreamingSolvable (space n s : Nat) : Prop :=
  ∃ A : SpaceBoundedStreaming space, SolvesMCSPSlice A n s

/--
The negation: the weak sequential lower bound that the magnification port
consumes.
-/
def MCSPStreamingHard (space n s : Nat) : Prop :=
  ¬ MCSPStreamingSolvable space n s

/-- Solvability is monotone in the memory budget. -/
theorem MCSPStreamingSolvable.mono {space space' n s : Nat}
    (h : space ≤ space') :
    MCSPStreamingSolvable space n s → MCSPStreamingSolvable space' n s := by
  rintro ⟨A, hA⟩
  refine ⟨A.widen h, ?_⟩
  intro tt
  simpa using hA tt

/--
Hardness is antitone in the memory budget: a lower bound against a *larger*
budget is a stronger statement.
-/
theorem MCSPStreamingHard.mono {space space' n s : Nat}
    (h : space ≤ space') :
    MCSPStreamingHard space' n s → MCSPStreamingHard space n s := by
  intro hHard hSolv
  exact hHard (MCSPStreamingSolvable.mono h hSolv)

/-!
### Why this target survives the repository's own refutation attacks

The following theorem is the formal statement of the structural claim in
`StreamingLowerBounds.lean`, specialised to the resource that matters here.

In the non-uniform classes used by every previously refuted route, a *fixed
input length* can always be handled by hardwiring the truth table, at no cost
to the class membership predicate; see
`pnp3/Tests/HInDagTrivialityProbe.lean`.

In the one-pass streaming model that move costs memory: if a memory budget of
`space` bits sufficed to decide *every* Boolean function on the single input
length `2 * m`, then `m ≤ space`.  In particular a sub-linear memory budget
cannot hardwire a fixed slice.
-/
theorem fixed_slice_hardwiring_costs_memory (space m : Nat)
    (hAll : ∀ f : List Bool → Bool,
      ∃ A : SpaceBoundedStreaming space, A.SolvesLength (2 * m) f) :
    m ≤ space := by
  by_contra hlt
  have hspace : space < m := by omega
  obtain ⟨f, hf⟩ := exists_streaming_hard_function_at_fixed_length space m hspace
  exact hf (hAll f)

end SequentialMagnification
end Frontier
end Pnp4
