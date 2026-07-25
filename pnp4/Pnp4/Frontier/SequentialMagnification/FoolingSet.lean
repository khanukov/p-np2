import Pnp4.Frontier.SequentialMagnification.StreamingLowerBounds

/-!
# The fooling-set method for one-pass streaming

`StreamingLowerBounds.lean` proves one concrete memory lower bound (two-block
equality).  This module extracts the underlying method as a reusable tool, so
that a future attempt at the actual MCSP streaming lower bound does not have to
re-derive it.

The method is the standard one-way communication-complexity argument.  A
one-pass device compresses everything it has read into a single memory state, so
if a family of prefixes is pairwise distinguishable by some continuation, those
prefixes must land in pairwise distinct states.

This is the same toolkit that Cheraghchi–Hirahara–Myrisiotis–Yoshida build on
for their one-tape lower bounds; recording it here makes the sequential route
self-contained on the "how would one even prove it" side.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

/--
**Fooling-set lower bound.**

Let `A` decide `f` on inputs of length `N = p + q`.  Suppose we have a family of
prefixes `pre i` of length `p`, indexed by a finite type `ι`, and for each
ordered pair `i ≠ j` a *distinguishing suffix* `suf i j` of length `q` on which
`f` disagrees between the two prefixes.  Then `A` needs at least `card ι` memory
states.

The distinguishing suffix is allowed to depend on the pair, which is what makes
the criterion usable in practice (for equality one takes `suf i j := pre i`).
-/
theorem card_le_card_state_of_foolingFamily
    {σ : Type} [Fintype σ] {ι : Type} [Fintype ι]
    (A : StreamingAlgo σ) (p q : Nat) (f : List Bool → Bool)
    (hA : ∀ xs : List Bool, xs.length = p + q → A.decideOn xs = f xs)
    (pre : ι → List Bool) (suf : ι → ι → List Bool)
    (hpre : ∀ i, (pre i).length = p)
    (hsuf : ∀ i j, (suf i j).length = q)
    (hfool : ∀ i j, i ≠ j →
      f (pre i ++ suf i j) ≠ f (pre j ++ suf i j)) :
    Fintype.card ι ≤ Fintype.card σ := by
  refine Fintype.card_le_of_injective (fun i => A.run (pre i)) ?_
  intro i j hij
  by_contra hne
  have hlen₁ : (pre i ++ suf i j).length = p + q := by
    simp [hpre, hsuf]
  have hlen₂ : (pre j ++ suf i j).length = p + q := by
    simp [hpre, hsuf]
  have hstep : A.decideOn (pre i ++ suf i j) = A.decideOn (pre j ++ suf i j) :=
    A.decideOn_append_congr hij (suf i j)
  have h₁ := hA _ hlen₁
  have h₂ := hA _ hlen₂
  exact hfool i j hne (by rw [← h₁, ← h₂, hstep])

/--
Space-budgeted form of the fooling-set bound: a fooling family of size
`> 2 ^ space` rules out every solver with `space` bits of memory.
-/
theorem no_solver_of_large_foolingFamily
    {space : Nat} {ι : Type} [Fintype ι]
    (A : SpaceBoundedStreaming space) (p q : Nat) (f : List Bool → Bool)
    (pre : ι → List Bool) (suf : ι → ι → List Bool)
    (hpre : ∀ i, (pre i).length = p)
    (hsuf : ∀ i j, (suf i j).length = q)
    (hfool : ∀ i j, i ≠ j →
      f (pre i ++ suf i j) ≠ f (pre j ++ suf i j))
    (hbig : 2 ^ space < Fintype.card ι) :
    ¬ A.SolvesLength (p + q) f := by
  intro hA
  have hcard : Fintype.card ι ≤ @Fintype.card A.State A.fintypeState :=
    @card_le_card_state_of_foolingFamily A.State A.fintypeState ι _
      A.algo p q f (fun xs hxs => hA xs hxs) pre suf hpre hsuf hfool
  have := le_trans hcard A.card_le
  omega

end SequentialMagnification
end Frontier
end Pnp4
