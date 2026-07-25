import Mathlib.Data.Fintype.BigOperators
import Pnp4.Frontier.SequentialMagnification.StreamingModel

/-!
# Unconditional lower bounds in the one-pass streaming model

This module proves, with no assumptions, the two facts that make the
sequential-magnification port a *non-vacuous* research target.

## 1. Hardwiring is not free (the anti-vacuity theorem)

Every source predicate previously used in this repository was refuted the same
way: a non-uniform witness class is closed under hardwiring a truth table at a
fixed input length, so the predicate held for free and the assumption collapsed
to `False`.  See `pnp3/Tests/HInDagTrivialityProbe.lean`
(`fixedSlice_gapPartialMCSP_in_PpolyDAG`) and the refuted family listed in
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

`equality_forces_memory` below shows that the one-pass streaming model is
**not** closed under that attack: a single *fixed* input length `N = 2 * m`
already carries a function that needs `2 ^ m = 2 ^ (N / 2)` memory states, i.e.
`N / 2` bits of memory.  So a fixed-slice hardwiring argument cannot satisfy a
streaming hardness hypothesis, and cannot refute it either.

This is the precise structural reason to prefer this port: the killing attack
of every previous route provably does not apply here.

## 2. The model is not trivially hard either

`parity_solvable` exhibits a nontrivial function solved with a single bit of
memory.  Together with (1) this pins the model strictly between "everything is
easy" and "everything is hard", which is what an honest falsifiability audit
requires: the hypothesis shape is neither `False` nor trivially `True`.

## Method note

The proof of (1) is the standard fooling-set / crossing-sequence argument from
communication complexity, which is exactly the toolkit that the
Cheraghchi–Hirahara–Myrisiotis–Yoshida one-tape lower bounds build on.  It is
recorded here in full because it is the *only* ingredient of the sequential
route that this repository can currently prove outright.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

/-!
### The two-block equality function
-/

/--
`eqBlocks m xs` compares the first `m` bits of `xs` with the rest.

On inputs of length `2 * m` this is the classical equality predicate
`EQ_m`, the canonical hard function for one-pass devices.
-/
def eqBlocks (m : Nat) (xs : List Bool) : Bool :=
  decide (xs.take m = xs.drop m)

@[simp] lemma eqBlocks_append {m : Nat} {u v : List Bool}
    (hu : u.length = m) :
    eqBlocks m (u ++ v) = decide (u = v) := by
  unfold eqBlocks
  subst hu
  simp

lemma length_append_eq {m : Nat} {u v : List Bool}
    (hu : u.length = m) (hv : v.length = m) :
    (u ++ v).length = 2 * m := by
  simp [hu, hv]
  omega

/-!
### The memory lower bound
-/

/--
**Anti-hardwiring theorem.**

If a one-pass streaming algorithm decides two-block equality at block length
`m`, then its memory has at least `2 ^ m` states.

The argument is the fooling-set argument: the map `x ↦ (state after reading x)`
must be injective on the `2 ^ m` possible first blocks, because two blocks
reaching the same state are indistinguishable by every continuation, while
equality distinguishes them via the continuation `x` itself.
-/
theorem equality_forces_memory {σ : Type} [Fintype σ] (A : StreamingAlgo σ)
    (m : Nat)
    (hSolve : ∀ u v : List Bool, u.length = m → v.length = m →
      (A.decideOn (u ++ v) = true ↔ u = v)) :
    2 ^ m ≤ Fintype.card σ := by
  have hinj :
      Function.Injective (fun x : Fin m → Bool => A.run (List.ofFn x)) := by
    intro x y hxy
    have hlx : (List.ofFn x).length = m := by simp
    have hly : (List.ofFn y).length = m := by simp
    have h1 : A.decideOn (List.ofFn x ++ List.ofFn x) = true :=
      (hSolve _ _ hlx hlx).2 rfl
    have hstep :
        A.decideOn (List.ofFn x ++ List.ofFn x)
          = A.decideOn (List.ofFn y ++ List.ofFn x) :=
      A.decideOn_append_congr hxy (List.ofFn x)
    have h2 : A.decideOn (List.ofFn y ++ List.ofFn x) = true := by
      rw [← hstep]; exact h1
    have hEq : List.ofFn y = List.ofFn x := (hSolve _ _ hly hlx).1 h2
    exact (List.ofFn_inj.mp hEq).symm
  have hcard : Fintype.card (Fin m → Bool) ≤ Fintype.card σ :=
    Fintype.card_le_of_injective _ hinj
  have hcf : Fintype.card (Fin m → Bool) = 2 ^ m := by
    simp
  rw [hcf] at hcard
  exact hcard

/--
Space-budgeted form: a solver with fewer than `m` bits of memory cannot decide
two-block equality on the single input length `2 * m`.
-/
theorem no_small_streaming_solver_for_equality
    {space : Nat} (m : Nat) (hspace : space < m)
    (A : SpaceBoundedStreaming space) :
    ¬ A.SolvesLength (2 * m) (eqBlocks m) := by
  intro hA
  have hSolve : ∀ u v : List Bool, u.length = m → v.length = m →
      (A.algo.decideOn (u ++ v) = true ↔ u = v) := by
    intro u v hu hv
    have hlen : (u ++ v).length = 2 * m := length_append_eq hu hv
    have := hA (u ++ v) hlen
    have hval : A.algo.decideOn (u ++ v) = decide (u = v) := by
      simpa [SpaceBoundedStreaming.decideOn, eqBlocks_append hu] using this
    constructor
    · intro hTrue
      rw [hval] at hTrue
      simpa using hTrue
    · intro hEq
      rw [hval]
      simp [hEq]
  have hbig : 2 ^ m ≤ @Fintype.card A.State A.fintypeState :=
    @equality_forces_memory A.State A.fintypeState A.algo m hSolve
  have hle : (2 : Nat) ^ m ≤ 2 ^ space := le_trans hbig A.card_le
  have : m ≤ space := (Nat.pow_le_pow_iff_right (by omega)).mp hle
  omega

/--
Existential form, ready for use as a non-vacuity certificate: at memory budget
`space` there is a Boolean function on the single input length `2 * m`
(`space < m`) that no space-bounded one-pass streaming algorithm decides.
-/
theorem exists_streaming_hard_function_at_fixed_length
    (space m : Nat) (hspace : space < m) :
    ∃ f : List Bool → Bool,
      ¬ ∃ A : SpaceBoundedStreaming space, A.SolvesLength (2 * m) f := by
  refine ⟨eqBlocks m, ?_⟩
  rintro ⟨A, hA⟩
  exact no_small_streaming_solver_for_equality m hspace A hA

/-!
### The model is not trivially hard
-/

/-- Parity of a bit list. -/
def parityFn (xs : List Bool) : Bool :=
  xs.foldl xor false

/-- A one-bit streaming algorithm for parity. -/
def parityAlgo : StreamingAlgo Bool where
  init := false
  step := fun s b => xor s b
  accept := fun s => s

lemma parityAlgo_runFrom (s : Bool) (xs : List Bool) :
    parityAlgo.runFrom s xs = xs.foldl xor s := by
  induction xs generalizing s with
  | nil => simp
  | cons b bs ih => simpa [parityAlgo] using ih (xor s b)

@[simp] lemma parityAlgo_decideOn (xs : List Bool) :
    parityAlgo.decideOn xs = parityFn xs := by
  show parityAlgo.accept (parityAlgo.runFrom parityAlgo.init xs) = parityFn xs
  rw [parityAlgo_runFrom]
  rfl

/-- Parity packaged as a one-bit space-bounded solver. -/
def parityBounded : SpaceBoundedStreaming 1 where
  State := Bool
  fintypeState := inferInstance
  card_le := by simp
  algo := parityAlgo

/--
**Non-triviality of the model.**  A nontrivial function on *every* input length
is decided with one bit of memory, so "no space-bounded streaming solver" is not
a statement that holds for free.
-/
theorem parity_solvable (N : Nat) :
    parityBounded.SolvesLength N parityFn := by
  intro xs _
  simp [SpaceBoundedStreaming.decideOn, parityBounded]

end SequentialMagnification
end Frontier
end Pnp4
