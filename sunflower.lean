/-
sunflower.lean
===============

A **self‑contained** file formalising *just enough* of the classical
Erdős–Rado Sunflower Lemma for the FCE‑Lemma project.

* We work with **finite sets** (`Finset α`) over an arbitrary type `α`
  with decidable equality.

* A **`w`‑set family** is a `Finset (Finset α)` each of whose members has
  cardinality **exactly** `w`.

* A **sunflower of size `p`** (a.k.a. *`p`‑sunflower*) is a sub‑family
  whose pairwise intersections are identical (the *core*).

The classical bound we need (and use downstream) is:

> If a `w`‑set family has more than `(p - 1)! * w^p` members,
> then it contains a `p`‑sunflower.

We *state* and export this lemma as `sunflower_exists`.  A complete,
fully‑formal proof is deferred (`sorry`) so that all dependent modules
compile immediately.  Replacing the `sorry` with a full proof is task
**C** in the overall roadmap.

The lemma’s **interface is frozen**—other files (`cover.lean` etc.)
rely only on its statement, not on the proof term.
-/

import Mathlib.Data.Nat.Factorial
import Mathlib.Tactic
import Std.Data.Finset
import BoolFunc

open Classical
open Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-! ### Basic definitions -/

/-- A *sunflower* (a.k.a. Δ‑system) inside a family `𝓢`:
    a sub‑family `𝓣` (of size `p`) whose members all have the **same**
    pairwise intersection (the *core*).  We store both `𝓣` and its
    intersection `core` for convenience.                                                  -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) : Prop where
  card_p : 𝓣.card = p
  core   : Finset α
  pairwise_inter :
    (∀ A ∈ 𝓣, ∀ B ∈ 𝓣, A ≠ B → A ∩ B = core)

/-- Abbreviation: a `p`‑sunflower is *some* `𝓣` satisfying `IsSunflower`. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, IsSunflower (α := α) p 𝓣 ∧ ∀ A ∈ 𝓣, A.card = w

/-! ### The classical Erdős–Rado bound (statement only) -/

/-- **Erdős–Rado Sunflower Lemma** (classical bound).

If a family `𝓢` of `w`‑element sets has more than `(p - 1)! * w^p`
members, then it contains a `p`‑sunflower.                                        -/
lemma sunflower_exists
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (all_w : ∀ A ∈ 𝓢, A.card = w)
    (bound : (p - 1).factorial * w ^ p < 𝓢.card) :
    HasSunflower 𝓢 w p := by
  -- TODO: full combinatorial proof.
  -- Standard proof outline:
  --  • Induct on |𝓢|.
  --  • Choose a set `A₀` of max degree; split 𝓢 into petals/others.
  --  • Apply induction or pigeonhole to show large set of disjoint
  --    petals implies sunflower.
  --  • Classical factorial‑times‑power bound completes.
  -- For now we admit, so downstream files compile:
  sorry

/-- A tiny convenience corollary specialised to **Boolean cube** contexts
where we automatically know each set has fixed size `w`.                     -/
corollary sunflower_exists_of_fixedSize
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : (∀ A ∈ 𝓢, A.card = w))
    (h_big  : 𝓢.card > (p - 1).factorial * w ^ p) :
    HasSunflower 𝓢 w p := by
  classical
  -- Just package the bound to match the main lemma's signature.
  refine sunflower_exists 𝓢 w p hw hp h_size ?bound
  -- Rearrange strict inequality direction to match the lemma's argument order.
  have : (p - 1).factorial * w ^ p < 𝓢.card := by
    simpa [lt_iff_le_and_ne, h_big.ne] using h_big
  exact this

end Sunflower
