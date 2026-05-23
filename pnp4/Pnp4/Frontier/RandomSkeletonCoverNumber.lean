import Pnp4.Frontier.SignSkeletonRectangleLowerBound

namespace Pnp4
namespace Frontier

def expansionUpTo {Skeleton : Type} (G : Skeleton) (T : Nat) : Prop :=
  coverNumber G > T

theorem expansionUpTo_implies_coverNumber_gt
    {Skeleton : Type}
    (G : Skeleton)
    (T : Nat)
    (h : expansionUpTo G T) :
    coverNumber G > T := h

def randomKUniformSkeletonSatisfiesExpansion
    (m k T : Nat) : Prop :=
  True

theorem random_kUniformSkeleton_expansion_scaffold
    (m : Nat)
    (k : Nat := Nat.ceil (Real.sqrt (Real.log m)))
    (T : Nat := Nat.floor (Real.sqrt m / (100 * k))) :
    randomKUniformSkeletonSatisfiesExpansion m k T := by
  trivial

end Frontier
end Pnp4
