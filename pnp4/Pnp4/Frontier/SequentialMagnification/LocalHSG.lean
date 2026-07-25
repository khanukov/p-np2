import Pnp4.Frontier.SequentialMagnification.MCSPStreamingTarget
import Counting.ShannonCounting

/-!
# Local hitting-set generators: a sufficient condition for the port's hypothesis

`MMWMagnificationPort.lean` reduces `P ≠ NP` to `MCSPStreamingHard`, which is a
weak lower bound nobody knows how to prove.  This module reduces that lower
bound further, to an explicit and completely standard **pseudorandomness**
statement, and then proves the counting obstruction that governs how good that
pseudorandom object has to be.

## The mechanism

A generator `G : {0,1}^λ → truth tables on n variables` is **local at `s`** if
every output is the truth table of a function with circuit complexity `≤ s`.
Every output of a local generator is therefore an MCSP[`s`]-YES instance.

Now suppose some algorithm `A` in a class `C` decides MCSP[`s`].  Its complement
`¬A` accepts exactly the NO instances, which by Shannon counting is at least
half of all truth tables — so `¬A` is a "large" test.  But `¬A` rejects every
output of `G`, since those are all YES instances.  So `G` fails to hit a large
test in `C`, i.e. `G` is not a hitting-set generator against `C`.

Contrapositive, which is what this module proves:

```text
local HSG at parameter s, secure against space-`B` one-pass streaming
  ⟹  MCSPStreamingHard B n s
  ⟹  (MMW contract)  P ≠ NP
```

This is the standard route — Razborov–Rudich, Hirahara, and the
Cheraghchi–Hirahara–Myrisiotis–Yoshida one-tape lower bounds all instantiate it.
Recording it here makes the sequential port's obligation concrete: not "prove a
lower bound", but "construct a pseudorandom object with specified parameters".

## The counting obstruction, and where `μ ≥ 1/2` comes from

`seedLength_bound_of_injective_localGenerator` proves the price of locality: an
injective local generator at parameter `s` has at most as many seeds as there
are functions of circuit complexity `≤ s`, so

```text
2 ^ λ  ≤  circuitCountBound n s
```

That single inequality is the whole reason the published lower bound sits at a
*large* size parameter.  Writing `N = 2 ^ n` and `s = 2 ^ (μ · n) = N ^ μ`, the
right-hand side is `2 ^ Õ(s)`, so the seed length must satisfy `λ ≲ Õ(N ^ μ)`.
The Forbes–Kelley generator used by CHMY has `λ = Õ(√N) = Õ(N ^ (1/2))`, which
forces `μ ≥ 1/2` — exactly the constant at which CHMY's own Theorem 3 says the
magnification side stops working.

So on this route the residual obstruction to `P ≠ NP` is not a circuit-complexity
question at all.  It is:

> **construct a local hitting-set generator against read-once / one-pass
> devices with seed length `N ^ o(1)` instead of `N ^ (1/2)`.**

`no_injective_localGenerator_of_seed_too_long` states the obstruction in the
sharp direction: whenever the seed budget exceeds the circuit-count budget, no
injective local generator exists at all.

## Status

Everything in this module is proved.  It does **not** prove `P ≠ NP`; it
replaces one open obligation by another, strictly more concrete, open
obligation.  The Shannon-counting slack is taken as an explicit hypothesis
(`hSlack`) rather than assumed silently; the repository's counting layer
(`Pnp3.Counting`) is what discharges it for size parameters below the counting
threshold.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

open Pnp4.AlgorithmsToLowerBounds
open Pnp3.Counting

/-!
### Complementing a streaming solver

The class of space-bounded one-pass algorithms is closed under complement, at
no cost in memory.  This is what lets us turn "decides MCSP" into "is a large
test that the generator must hit".
-/

/-- Flip the output of a space-bounded streaming solver. -/
def SpaceBoundedStreaming.complement {space : Nat}
    (A : SpaceBoundedStreaming space) : SpaceBoundedStreaming space where
  State := A.State
  fintypeState := A.fintypeState
  card_le := A.card_le
  algo :=
    { init := A.algo.init
      step := A.algo.step
      accept := fun st => !(A.algo.accept st) }

lemma complement_runFrom {space : Nat} (A : SpaceBoundedStreaming space)
    (st : A.State) (l : List Bool) :
    A.complement.algo.runFrom st l = A.algo.runFrom st l := by
  induction l generalizing st with
  | nil => rfl
  | cons b bs ih => exact ih _

@[simp] lemma decideOn_complement {space : Nat}
    (A : SpaceBoundedStreaming space) (xs : List Bool) :
    A.complement.decideOn xs = Bool.not (A.decideOn xs) :=
  congrArg (fun st => Bool.not (A.algo.accept st))
    (complement_runFrom A A.algo.init xs)

/-!
### Large tests
-/

/-- The set of truth tables at slice `n` accepted by `A`. -/
noncomputable def acceptedTables {space : Nat}
    (A : SpaceBoundedStreaming space) (n : Nat) : Finset (TruthTable n) :=
  Finset.univ.filter (fun tt => A.decideOn (tableStream tt) = true)

/-- `A` accepts at least half of all truth tables at slice `n`. -/
def LargeAcceptance {space : Nat} (A : SpaceBoundedStreaming space)
    (n : Nat) : Prop :=
  Fintype.card (TruthTable n) ≤ 2 * (acceptedTables A n).card

lemma acceptedTables_complement {space : Nat}
    (A : SpaceBoundedStreaming space) (n : Nat) :
    acceptedTables A.complement n
      = Finset.univ.filter
          (fun tt : TruthTable n => ¬ (A.decideOn (tableStream tt) = true)) := by
  ext tt
  simp [acceptedTables]

lemma card_accepted_add_card_accepted_complement {space : Nat}
    (A : SpaceBoundedStreaming space) (n : Nat) :
    (acceptedTables A n).card + (acceptedTables A.complement n).card
      = Fintype.card (TruthTable n) := by
  rw [acceptedTables_complement]
  unfold acceptedTables
  rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]

/-!
### Easy tables
-/

/--
A truth table with a circuit of size `≤ s` lies in the repository's counting
set `easyFunctions n s`.

This is the bridge between the `pnp4` MCSP predicate and the `pnp3` Shannon
counting layer.
-/
theorem mem_easyFunctions_of_circuitComplexityLE {n s : Nat} {tt : TruthTable n}
    (h : circuitComplexityLE treeCircuitClass n s tt) :
    tt ∈ easyFunctions n s := by
  obtain ⟨c, hsize, hcomp⟩ := h
  have hcirc : Pnp3.Models.circuitComputes c tt := hcomp
  have htab : tt = circuitToTable c :=
    circuitComputes_eq_circuitToTable c tt hcirc
  refine Finset.mem_image.mpr ⟨c, ?_, htab.symm⟩
  exact mem_circuitsOfSizeAtMost c s hsize

/-!
### Local generators
-/

/--
A generator of truth tables all of whose outputs are MCSP[`s`]-YES instances.

"Local" is the standard name: each output bit of `G z` is computable by a small
circuit from its index, which is exactly the statement that `G z` is the truth
table of a low-complexity function.
-/
structure LocalGenerator (n s seedLen : Nat) where
  /-- The generator itself. -/
  gen : (Fin seedLen → Bool) → TruthTable n
  /-- Locality: every output has a circuit of size at most `s`. -/
  localAt : ∀ z, circuitComplexityLE treeCircuitClass n s (gen z)

/--
Hitting-set security against space-bounded one-pass tests: every test in the
class that accepts at least half of all truth tables accepts some output of the
generator.
-/
def HitsStreamingTests {n s seedLen : Nat} (G : LocalGenerator n s seedLen)
    (space : Nat) : Prop :=
  ∀ A : SpaceBoundedStreaming space, LargeAcceptance A n →
    ∃ z, A.decideOn (tableStream (G.gen z)) = true

/-!
### The reduction
-/

/--
**Local HSG ⟹ the port's hypothesis.**

If a local hitting-set generator at size parameter `s` is secure against
`space`-bounded one-pass streaming tests, and Shannon counting leaves at least
half the truth tables outside the easy set, then `MCSP[s]` at slice `n` has no
`space`-bounded one-pass streaming solver.

Combined with `P_ne_NP_of_mcsp_streaming_hardness`, this reduces `P ≠ NP` to the
existence of such a generator (plus the published MMW contract).
-/
theorem MCSPStreamingHard_of_localHSG {n s seedLen space : Nat}
    (G : LocalGenerator n s seedLen)
    (hHit : HitsStreamingTests G space)
    (hSlack : 2 * (easyFunctions n s).card ≤ Fintype.card (TruthTable n)) :
    MCSPStreamingHard space n s := by
  rintro ⟨A, hA⟩
  -- Everything `A` accepts is an easy table.
  have hsub : acceptedTables A n ⊆ easyFunctions n s := by
    intro tt htt
    have hacc : A.decideOn (tableStream tt) = true := by
      have := Finset.mem_filter.mp htt
      exact this.2
    exact mem_easyFunctions_of_circuitComplexityLE ((hA tt).1 hacc)
  have hcardAcc : (acceptedTables A n).card ≤ (easyFunctions n s).card :=
    Finset.card_le_card hsub
  -- Hence the complement is a large test.
  have hsplit := card_accepted_add_card_accepted_complement A n
  have hlarge : LargeAcceptance A.complement n := by
    unfold LargeAcceptance
    omega
  -- The generator must hit it, but all its outputs are YES instances.
  obtain ⟨z, hz⟩ := hHit A.complement hlarge
  have hyes : A.decideOn (tableStream (G.gen z)) = true :=
    (hA (G.gen z)).2 (G.localAt z)
  rw [decideOn_complement, hyes] at hz
  simp at hz

/-!
### The counting price of locality
-/

/--
**Seed-length bound.**

An injective local generator at size parameter `s` cannot have more seeds than
there are functions of circuit complexity `≤ s`.

This is the inequality that pins the size parameter of every lower bound proved
by the local-HSG method.
-/
theorem seedLength_bound_of_injective_localGenerator {n s seedLen : Nat}
    (G : LocalGenerator n s seedLen) (hinj : Function.Injective G.gen) :
    2 ^ seedLen ≤ Pnp3.Models.circuitCountBound n s := by
  have hmaps : ∀ z ∈ (Finset.univ : Finset (Fin seedLen → Bool)),
      G.gen z ∈ easyFunctions n s :=
    fun z _ => mem_easyFunctions_of_circuitComplexityLE (G.localAt z)
  have hcard :
      (Finset.univ : Finset (Fin seedLen → Bool)).card
        ≤ (easyFunctions n s).card :=
    Finset.card_le_card_of_injOn G.gen hmaps (Function.Injective.injOn hinj)
  have huniv : (Finset.univ : Finset (Fin seedLen → Bool)).card = 2 ^ seedLen := by
    simp
  rw [huniv] at hcard
  exact le_trans hcard (card_easyFunctions_le n s)

/--
**The obstruction, sharp form.**

If the seed budget exceeds the circuit-count budget at parameter `s`, then no
injective local generator exists at all.

Reading: to lower the MCSP size parameter `s` one must simultaneously lower the
seed length of the generator.  With `s = N ^ μ` the right-hand side is
`2 ^ Õ(N ^ μ)`, so `λ = Õ(√N)` forces `μ ≥ 1/2`.
-/
theorem no_injective_localGenerator_of_seed_too_long {n s seedLen : Nat}
    (hbig : Pnp3.Models.circuitCountBound n s < 2 ^ seedLen) :
    ¬ ∃ G : LocalGenerator n s seedLen, Function.Injective G.gen := by
  rintro ⟨G, hinj⟩
  have := seedLength_bound_of_injective_localGenerator G hinj
  omega

/-!
### The reduced frontier

Putting the pieces together, the sequential route now reads:

```text
local HSG (seed λ, local at s, secure vs space-B one-pass streaming)
  + Shannon slack at s
  ⟹  MCSPStreamingHard B n s                     -- MCSPStreamingHard_of_localHSG
  ⟹  P ≠ NP                                      -- P_ne_NP_of_mcsp_streaming_hardness
                                                  --   (modulo the MMW contract)
```

subject to the hard constraint

```text
2 ^ λ ≤ circuitCountBound n s                     -- seedLength_bound_of_injective_localGenerator
```

which is what makes the two published theorems miss each other.  Improving the
seed length of local HSGs against read-once devices is therefore not a technical
convenience on this route — it is the route.
-/

end SequentialMagnification
end Frontier
end Pnp4
