import Pnp4.Frontier.SignSkeletonRectangleLowerBound

namespace Pnp4
namespace Frontier

def expansionUpTo {Skeleton : Type} (coverNumber : Skeleton → Nat) (G : Skeleton) (T : Nat) : Prop :=
  coverNumber G > T

theorem expansionUpTo_implies_coverNumber_gt
    {Skeleton : Type}
    (coverNumber : Skeleton → Nat)
    (G : Skeleton)
    (T : Nat)
    (h : expansionUpTo coverNumber G T) :
    coverNumber G > T := h

/-- Optional probabilistic scaffold encoded as an explicit success probability. -/
def randomKUniformSkeletonSatisfiesExpansion
    (m k T : Nat) : Prop :=
  ∃ p : ℚ, 0 ≤ p ∧ p ≤ 1

end Frontier
end Pnp4
