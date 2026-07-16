import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDCanonicalWalkCellDecomposition
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact energy packing of canonical-walk cells

Under unambiguity, one canonical-walk suffix cell is exactly the Boolean
indicator of the inputs which are compatible with its fixed accepting walk
and whose input-labelled walk trace has the displayed suffix.  Thus the
apparently atomic accepted-point definition is an exact cylinder/subcube
indicator, not merely a function supported on the compatibility fiber.

For a fixed suffix cone, the canonical-walk cells are pointwise disjoint.
Parseval therefore gives an exact, cardinality-free packing identity: the sum
of the full Fourier energies of all realized cells equals the full Fourier
energy of the cone.  No width, number-of-walks, read-once, or full-read factor
is lost.  The identity concerns unary cell energy; it does not control the
incidence multiplicity of walk-pair rectangles or select one common opposite
coordinate across different walk pairs.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanFourierEnergy

namespace FiniteUnambiguousFBDD

/-- Semantic membership in the fixed-walk part of a canonical suffix cone.
For a realized accepting walk this is a possibly empty, possibly
lower-dimensional Boolean subcube: compatibility and the labelled suffix
impose only coordinate-value constraints along the fixed walk. -/
def IsCanonicalWalkSuffixConeCellInput {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) (input : Fin n -> Bool) : Prop :=
  walk.Compatible input ∧ key <:+ walk.inputLabelledFullTrace input

/-- The rational `{0,1}` indicator of fixed-walk suffix-cell membership. -/
noncomputable def canonicalWalkSuffixConeCellMembershipIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) (input : Fin n -> Bool) : Rat := by
  classical
  exact if B.IsCanonicalWalkSuffixConeCellInput key walk input then 1 else 0

/-- Under unambiguity, the accepted-point sum defining a canonical-walk cell
is exactly the `{0,1}` indicator of compatibility with that walk plus the
labelled suffix condition. -/
theorem canonicalWalkSuffixConeCellIndicator_eq_compatibleSuffixIndicator
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) (input : Fin n -> Bool) :
    B.canonicalWalkSuffixConeCellIndicator key walk input =
      B.canonicalWalkSuffixConeCellMembershipIndicator key walk input := by
  classical
  unfold canonicalWalkSuffixConeCellIndicator
    canonicalWalkSuffixConeCellMembershipIndicator
  by_cases hcell : B.IsCanonicalWalkSuffixConeCellInput key walk input
  · let accepted : B.AcceptedModel :=
      ⟨input, Nonempty.intro { walk := walk, compatible := hcell.1 }⟩
    have hcanonical : B.canonicalAcceptingWalk accepted = walk :=
      B.canonicalAcceptingWalk_eq_of_compatible
        hUnambiguous accepted walk hcell.1
    have haccepted : accepted ∈ B.canonicalAcceptingWalkFiber walk :=
      (B.mem_canonicalAcceptingWalkFiber walk accepted).2 hcanonical
    have hsuffix : key <:+ B.canonicalInputLabelledFullTrace accepted := by
      simpa [canonicalInputLabelledFullTrace, hcanonical, accepted] using hcell.2
    rw [if_pos hcell]
    calc
      (∑ other ∈ B.canonicalAcceptingWalkFiber walk,
          if key <:+ B.canonicalInputLabelledFullTrace other then
            B.ratAcceptedPointIndicator other input
          else 0) =
          (if key <:+ B.canonicalInputLabelledFullTrace accepted then
            B.ratAcceptedPointIndicator accepted input
          else 0) := by
            apply Finset.sum_eq_single accepted
            · intro other hother _hne
              have hinput : input ≠ other.1 := by
                intro heq
                apply _hne
                apply Subtype.ext
                simpa [accepted] using heq.symm
              by_cases hotherSuffix :
                  key <:+ B.canonicalInputLabelledFullTrace other
              · simp [hotherSuffix, ratAcceptedPointIndicator, hinput]
              · simp [hotherSuffix]
            · intro hnotMem
              exact (hnotMem haccepted).elim
      _ = 1 := by
        simp [hsuffix, ratAcceptedPointIndicator, accepted]
  · rw [if_neg hcell]
    apply Finset.sum_eq_zero
    intro accepted haccepted
    by_cases hsuffix : key <:+ B.canonicalInputLabelledFullTrace accepted
    · have hwalk : B.canonicalAcceptingWalk accepted = walk :=
        (B.mem_canonicalAcceptingWalkFiber walk accepted).1 haccepted
      have hinput : input ≠ accepted.1 := by
        intro heq
        apply hcell
        constructor
        · simpa [heq, hwalk] using
            B.canonicalAcceptingWalk_compatible accepted
        · simpa [canonicalInputLabelledFullTrace, heq, hwalk] using hsuffix
      simp [hsuffix, ratAcceptedPointIndicator, hinput]
    · simp [hsuffix]

/-- The exact cell indicator is a cylinder on the variables queried by its
fixed walk.  This is the functional locality form of the subcube semantics. -/
theorem canonicalWalkSuffixConeCellIndicator_dependsOnlyOn_queryVars
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) :
    DependsOnlyOn walk.queryVars
      (B.canonicalWalkSuffixConeCellIndicator key walk) := by
  intro leftInput rightInput hagrees
  rw [B.canonicalWalkSuffixConeCellIndicator_eq_compatibleSuffixIndicator
      hUnambiguous,
    B.canonicalWalkSuffixConeCellIndicator_eq_compatibleSuffixIndicator
      hUnambiguous]
  unfold canonicalWalkSuffixConeCellMembershipIndicator
  have hcompatible : walk.Compatible leftInput ↔
      walk.Compatible rightInput :=
    walk.compatible_iff_of_eq_on_queryVars hagrees
  have htrace : walk.inputLabelledFullTrace leftInput =
      walk.inputLabelledFullTrace rightInput :=
    walk.inputLabelledFullTrace_eq_of_eq_on_queryVars
      leftInput rightInput hagrees
  have hcell : B.IsCanonicalWalkSuffixConeCellInput key walk leftInput ↔
      B.IsCanonicalWalkSuffixConeCellInput key walk rightInput := by
    unfold IsCanonicalWalkSuffixConeCellInput
    rw [hcompatible, htrace]
  by_cases hleft :
      B.IsCanonicalWalkSuffixConeCellInput key walk leftInput
  · have hright := hcell.mp hleft
    simp [hleft, hright]
  · have hright :
        ¬B.IsCanonicalWalkSuffixConeCellInput key walk rightInput := by
      exact fun h => hleft (hcell.mpr h)
    simp [hleft, hright]

/-- Every canonical-walk cell is idempotent pointwise: it is genuinely a
Boolean indicator. -/
theorem canonicalWalkSuffixConeCellIndicator_sq_eq_self
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) (input : Fin n -> Bool) :
    (B.canonicalWalkSuffixConeCellIndicator key walk input) ^ 2 =
      B.canonicalWalkSuffixConeCellIndicator key walk input := by
  rw [B.canonicalWalkSuffixConeCellIndicator_eq_compatibleSuffixIndicator
    hUnambiguous]
  unfold canonicalWalkSuffixConeCellMembershipIndicator
  by_cases hcell : B.IsCanonicalWalkSuffixConeCellInput key walk input <;>
    simp [hcell]

/-- A canonical residual suffix cone is also a Boolean indicator, without an
unambiguity premise. -/
theorem canonicalResidualSuffixConeIndicator_sq_eq_self
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B)) (input : Fin n -> Bool) :
    (B.canonicalResidualSuffixConeIndicator key input) ^ 2 =
      B.canonicalResidualSuffixConeIndicator key input := by
  rw [B.canonicalResidualSuffixConeIndicator_eq_membershipIndicator]
  unfold canonicalResidualSuffixConeMembershipIndicator
  by_cases hcone : B.IsCanonicalResidualSuffixConeInput key input <;>
    simp [hcone]

/-- Pointwise Pythagoras identity for the finite partition of one suffix cone
by realized canonical walks. -/
theorem sum_canonicalWalkCell_sq_eq_cone_sq
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous)
    (key : List (InputLabelledFullStep B)) (input : Fin n -> Bool) :
    (∑ walk ∈ B.realizedCanonicalAcceptingWalks,
        (B.canonicalWalkSuffixConeCellIndicator key walk input) ^ 2) =
      (B.canonicalResidualSuffixConeIndicator key input) ^ 2 := by
  calc
    (∑ walk ∈ B.realizedCanonicalAcceptingWalks,
        (B.canonicalWalkSuffixConeCellIndicator key walk input) ^ 2) =
        ∑ walk ∈ B.realizedCanonicalAcceptingWalks,
          B.canonicalWalkSuffixConeCellIndicator key walk input := by
            apply Finset.sum_congr rfl
            intro walk _
            exact B.canonicalWalkSuffixConeCellIndicator_sq_eq_self
              hUnambiguous key walk input
    _ = B.canonicalResidualSuffixConeIndicator key input :=
      (B.canonicalResidualSuffixConeIndicator_eq_sum_canonicalWalkCells
        key input).symm
    _ = (B.canonicalResidualSuffixConeIndicator key input) ^ 2 :=
      (B.canonicalResidualSuffixConeIndicator_sq_eq_self key input).symm

/-- **Cardinality-free Fourier packing.**  For one canonical suffix cone,
the sum of the complete Walsh energies of all canonical-walk cells is exactly
the complete Walsh energy of the cone. -/
theorem sum_canonicalWalkCell_fourierEnergy_eq_cone_fourierEnergy
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous)
    (key : List (InputLabelledFullStep B)) :
    (∑ walk ∈ B.realizedCanonicalAcceptingWalks,
        ∑ alpha : Finset (Fin n),
          (coefficient
            (B.canonicalWalkSuffixConeCellIndicator key walk) alpha) ^ 2) =
      ∑ alpha : Finset (Fin n),
        (coefficient (B.canonicalResidualSuffixConeIndicator key) alpha) ^ 2 := by
  calc
    (∑ walk ∈ B.realizedCanonicalAcceptingWalks,
        ∑ alpha : Finset (Fin n),
          (coefficient
            (B.canonicalWalkSuffixConeCellIndicator key walk) alpha) ^ 2) =
        ∑ walk ∈ B.realizedCanonicalAcceptingWalks,
          finiteAverage (fun input : Fin n -> Bool =>
            (B.canonicalWalkSuffixConeCellIndicator key walk input) ^ 2) := by
              apply Finset.sum_congr rfl
              intro walk _
              exact parseval
                (B.canonicalWalkSuffixConeCellIndicator key walk)
    _ = finiteAverage (fun input : Fin n -> Bool =>
        ∑ walk ∈ B.realizedCanonicalAcceptingWalks,
          (B.canonicalWalkSuffixConeCellIndicator key walk input) ^ 2) := by
            symm
            exact finiteAverage_finset_sum
              B.realizedCanonicalAcceptingWalks
              (fun walk input =>
                (B.canonicalWalkSuffixConeCellIndicator key walk input) ^ 2)
    _ = finiteAverage (fun input : Fin n -> Bool =>
        (B.canonicalResidualSuffixConeIndicator key input) ^ 2) := by
          apply finiteAverage_congr
          intro input
          exact B.sum_canonicalWalkCell_sq_eq_cone_sq
            hUnambiguous key input
    _ = ∑ alpha : Finset (Fin n),
        (coefficient (B.canonicalResidualSuffixConeIndicator key) alpha) ^ 2 :=
      (parseval (B.canonicalResidualSuffixConeIndicator key)).symm

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
