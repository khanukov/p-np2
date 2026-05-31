import Pnp4.Frontier.ContractExpansion.QueryComposition

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.ComplexityInterfaces (DagCircuit)

/-!
# Size-feasibility spike for the naive per-bit greedy extraction (decision gate)

This file is the **feasibility gate** for the downstream decision→search
extraction.  It is a *note/lemma* brick: it proves, in Lean, the size behaviour
of the **naive** per-bit greedy circuit construction, and records the resulting
architectural decision.  It builds **no** greedy solver and makes **no** lower
bound or `P ≠ NP` claim; it only quantifies the cost of one candidate
construction so the next bricks pick the right shape.

## The naive construction and why it blows up

The extraction composes a DAG-decider with query-bit circuits via
`composeDeciderWithQuery`, which is exactly the frozen `DagCircuit.substInputs`
(`composeDeciderWithQuery_eq_substInputs`).  The crucial structural fact is that
`substInputs` **does not share** subcircuits: its gate count is the *sum* of the
substituted circuits' gate counts plus the decider's
(`size (substInputs D G) = (∑ⱼ (G j).gates) + D.gates + 1`, from
`DagCircuit.size_substInputs` + `DagCircuit.bundleOfFamily_gates`).

In the naive greedy scheme, output bit `i` is produced by substituting the prior
greedy bits `0, …, i-1` into the query circuit (they occupy the prefix-payload
positions).  Hence the gate count `g i` of bit `i` satisfies the recurrence
`g (i+1) ≥ ∑_{k ≤ i} g k`, which forces `g i ≥ g 0 · 2^i` — exponential in the
number of output bits.  This is proved here twice:

* abstractly, `geometric_lower_bound`: any `g` with `∑_{k<i+1} g k ≤ g (i+1)`
  satisfies `g 0 · 2^i ≤ g (i+1)`;
* concretely, `naiveGreedyModel_size_ge`: a faithful model of the recursion
  (each step substitutes *all* prior steps via the real `composeDeciderWithQuery`)
  has size `≥ seed.gates · 2^i` at depth `i+1`.

## Magnification arithmetic (why this is fatal)

The number of greedy output bits is `witnessBits n`, and the instance size is
`N = tableLen n = 2^n`.  For the naive size `≈ 2^{witnessBits n}` to stay
polynomial in `N = 2^n` we need `witnessBits n = O(n)`:

* `pow_le_of_linear_witnessBits`: if `witnessBits n ≤ c·n + c` then
  `2^{witnessBits n} ≤ (2^n)^c · 2^c = poly(N)` — naive is fine;
* `pow_quadratic_gt_poly`: but for a super-linear witness length (e.g.
  `witnessBits n = n²`), for *every* fixed polynomial degree `c` and all `n > c`,
  `(2^n)^c < 2^{n²}` — the naive size outgrows every polynomial in `N`.

Standard circuit-witness encodings have length `≈ s(n)·log s(n)`, so for any
interesting MCSP threshold `s(n) ≥ n²` the witness is super-linear and the naive
construction is super-polynomial in `N`.

## Decision (the gate verdict)

**Option ① — shared `DagBundle` multi-output — is the working default.**  The
greedy bits must share one gate list (a `DagBundle`, projected per output bit) so
that size is *uniform* in the bit index rather than re-embedding all priors.  This
needs a new composition primitive generalizing `substInputsWithBundle` to retain
all outputs while layering a group reading prior outputs and fresh inputs.

**Option ② — naive per-bit, restricting `witnessBits n = O(n)` — is a fallback
only** if a *concrete* codec proves `witnessBits n = O(n)` and the resulting
threshold stays mathematically meaningful (unlikely for interesting thresholds).

Consequently the prefix-state query builder (next brick) must expose its payload
as reads of prior *bundle outputs*, not as a family of independent circuits.

Scope discipline — feasibility note only: **no** greedy solver, **no**
`BoundedSearchSolver`, **no** `PpolyDAG` bridge, **no** endpoint, **no**
`P ≠ NP` / `NP ⊄ P/poly` consequence, **no** lower bound.
-/

/-! ## Part 1 — abstract geometric lower bound for the additive recurrence -/

/--
If `f (i+1)` dominates the running sum `∑_{k ≤ i} f k` at every step, then the
running sum is at least `f 0 · 2^i`.  (Ordinary induction: the sum at least
doubles each step.)
-/
theorem sum_geometric_lower (f : Nat → Nat)
    (hstep : ∀ i, (∑ k ∈ Finset.range (i + 1), f k) ≤ f (i + 1)) :
    ∀ i, f 0 * 2 ^ i ≤ ∑ k ∈ Finset.range (i + 1), f k := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      have hsum := hstep i
      have hdouble : f 0 * 2 ^ (i + 1) = (f 0 * 2 ^ i) + (f 0 * 2 ^ i) := by ring
      rw [Finset.sum_range_succ]
      omega

/--
The additive greedy recurrence forces exponential growth: if `f` dominates its
running sum at every step, then `f (i+1) ≥ f 0 · 2^i`.
-/
theorem geometric_lower_bound (f : Nat → Nat)
    (hstep : ∀ i, (∑ k ∈ Finset.range (i + 1), f k) ≤ f (i + 1)) (i : Nat) :
    f 0 * 2 ^ i ≤ f (i + 1) :=
  le_trans (sum_geometric_lower f hstep i) (hstep i)

/-! ## Part 2 — concrete blow-up of the naive `composeDeciderWithQuery` recursion -/

/-- `composeDeciderWithQuery` is exactly the frozen `substInputs`; the model below
faithfully uses the real extraction composition op. -/
theorem composeDeciderWithQuery_eq_substInputs
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    composeDeciderWithQuery decider queryBit
      = DagCircuit.substInputs decider queryBit := rfl

/--
A faithful model of the naive per-bit greedy recursion: depth `0` is a seed
circuit, and depth `i+1` substitutes **all** prior depths `0, …, i` (as the query
bits) into a combiner decider, via the real `composeDeciderWithQuery`/`substInputs`.
This reproduces exactly the "re-embed all priors" structure of the naive scheme.
-/
def naiveGreedyModel (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) : Nat → DagCircuit m
  | 0 => seed
  | i + 1 =>
      DagCircuit.substInputs (decider (i + 1))
        (fun k : Fin (i + 1) => naiveGreedyModel m seed decider k.1)

/-- One step of the model sums the gate counts of all prior steps (plus the
combiner), exactly because `substInputs` does not share. -/
theorem gates_naiveGreedyModel_succ (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) :
    (naiveGreedyModel m seed decider (i + 1)).gates
      = (∑ k ∈ Finset.range (i + 1), (naiveGreedyModel m seed decider k).gates)
        + (decider (i + 1)).gates := by
  have hunfold :
      naiveGreedyModel m seed decider (i + 1)
        = DagCircuit.substInputs (decider (i + 1))
            (fun k : Fin (i + 1) => naiveGreedyModel m seed decider k.1) := by
    simp only [naiveGreedyModel]
  have hbundle :
      (DagCircuit.bundleOfFamily (i + 1)
          (fun k : Fin (i + 1) => naiveGreedyModel m seed decider k.1)).gates
        = ∑ k ∈ Finset.range (i + 1), (naiveGreedyModel m seed decider k).gates := by
    rw [DagCircuit.bundleOfFamily_gates]
    exact Fin.sum_univ_eq_sum_range
      (fun k => (naiveGreedyModel m seed decider k).gates) (i + 1)
  have hsize :=
    DagCircuit.size_substInputs (decider (i + 1))
      (fun k : Fin (i + 1) => naiveGreedyModel m seed decider k.1)
  rw [hbundle] at hsize
  have hsz :
      DagCircuit.size
          (DagCircuit.substInputs (decider (i + 1))
            (fun k : Fin (i + 1) => naiveGreedyModel m seed decider k.1))
        = (DagCircuit.substInputs (decider (i + 1))
            (fun k : Fin (i + 1) => naiveGreedyModel m seed decider k.1)).gates + 1 := rfl
  rw [hunfold]
  omega

/-- **The naive construction blows up.**  At depth `i+1`, the model's gate count
is at least `seed.gates · 2^i` — exponential in the depth (= number of bits). -/
theorem naiveGreedyModel_gates_ge (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) :
    seed.gates * 2 ^ i ≤ (naiveGreedyModel m seed decider (i + 1)).gates := by
  have hstep : ∀ j,
      (∑ k ∈ Finset.range (j + 1), (naiveGreedyModel m seed decider k).gates)
        ≤ (naiveGreedyModel m seed decider (j + 1)).gates := by
    intro j
    rw [gates_naiveGreedyModel_succ]
    exact Nat.le_add_right _ _
  have h0 : naiveGreedyModel m seed decider 0 = seed := by
    simp only [naiveGreedyModel]
  have hge := geometric_lower_bound
    (fun k => (naiveGreedyModel m seed decider k).gates) hstep i
  rw [h0] at hge
  exact hge

/-- The size (`= gates + 1`) version of the blow-up. -/
theorem naiveGreedyModel_size_ge (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) :
    seed.gates * 2 ^ i ≤ DagCircuit.size (naiveGreedyModel m seed decider (i + 1)) := by
  have h := naiveGreedyModel_gates_ge m seed decider i
  have hsz : DagCircuit.size (naiveGreedyModel m seed decider (i + 1))
      = (naiveGreedyModel m seed decider (i + 1)).gates + 1 := rfl
  omega

/-- With a nonempty seed (`1 ≤ seed.gates`), the size is at least `2^i`. -/
theorem naiveGreedyModel_size_ge_pow (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) (hseed : 1 ≤ seed.gates) :
    2 ^ i ≤ DagCircuit.size (naiveGreedyModel m seed decider (i + 1)) := by
  have h := naiveGreedyModel_size_ge m seed decider i
  have h2 : 1 * 2 ^ i ≤ seed.gates * 2 ^ i := by gcongr
  rw [one_mul] at h2
  exact le_trans h2 h

/-! ## Part 3 — magnification arithmetic (linear ⇒ poly; quadratic ⇒ super-poly) -/

/-- Linear witness length keeps the naive size polynomial in `N = 2^n`:
`2^{witnessBits} ≤ (2^n)^c · 2^c`. -/
theorem pow_le_of_linear_witnessBits (W n c : Nat) (h : W ≤ c * n + c) :
    2 ^ W ≤ (2 ^ n) ^ c * 2 ^ c := by
  calc
    2 ^ W ≤ 2 ^ (c * n + c) := Nat.pow_le_pow_right (by norm_num) h
    _ = (2 ^ n) ^ c * 2 ^ c := by
        rw [pow_add, Nat.mul_comm c n, pow_mul]

/-- Super-linear witness length outgrows every fixed polynomial degree in
`N = 2^n`: for `witnessBits n = n²`, every degree `c`, and all `n > c`,
`(2^n)^c < 2^{n²}`. -/
theorem pow_quadratic_gt_poly (n c : Nat) (hn : 0 < n) (hc : c < n) :
    (2 ^ n) ^ c < 2 ^ (n * n) := by
  have hmul : n * c < n * n := by nlinarith [hc, hn]
  calc
    (2 ^ n) ^ c = 2 ^ (n * c) := (pow_mul 2 n c).symm
    _ < 2 ^ (n * n) := Nat.pow_lt_pow_right (by norm_num) hmul

end ContractExpansion
end Frontier
end Pnp4
