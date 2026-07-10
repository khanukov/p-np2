import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaGlobal

/-!
# Ordered-width information lost at the transformed gamma handoff

The transformed body of an empty gamma payload is the one-bit word `[true]`.
The transformed body of the singleton payload `[true]` is `[true, true, true]`.
Consequently, swapping those two adjacent bodies does not change their
concatenation.  This file records the resulting collision for the current
three-gamma final frame, footprint, useful time, and natural-coordinate
handoff configuration.

The scope is deliberately local.  The theorem concerns the transformed
three-gamma frame (or that frame followed by the *same* arbitrary suffix).  It
does not identify two complete canonical Stream-Merge requests and does not
rule out a wrapper which retains bounded shape information while parsing.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalTaggedGamma

open OperationalGammaZipper

/-- An empty transformed body followed by the transformed singleton `[true]`
is identical to the same two bodies in the opposite order. -/
theorem zippedBody_empty_true_collision :
    zippedBody [] ++ zippedBody [true] =
      zippedBody [true] ++ zippedBody [] := by
  rfl

/-- The collision persists inside the three-field final frame for every fixed
third payload. -/
theorem tripleFinalFrame_empty_true_collision (third : List Bool) :
    tripleFinalFrame [] [true] third =
      tripleFinalFrame [true] [] third := by
  simp [tripleFinalFrame, zippedBody, encChain, encFinal]

/-- Appending the same natural-coordinate suffix cannot distinguish the two
colliding transformed frames. -/
theorem framedTape_empty_true_collision (third : List Bool)
    (suffix : Nat -> Bool) :
    framedTape (tripleFinalFrame [] [true] third) suffix =
      framedTape (tripleFinalFrame [true] [] third) suffix := by
  rw [tripleFinalFrame_empty_true_collision]

/-- Swapping widths zero and one leaves the aggregate transformed footprint
unchanged. -/
theorem tripleFootprint_zero_one_collision (thirdWidth : Nat) :
    tripleFootprint 0 1 thirdWidth =
      tripleFootprint 1 0 thirdWidth := by
  simp [tripleFootprint]

/-- The exact useful tagged time is likewise insensitive to this swap. -/
theorem taggedTripleTime_zero_one_collision (thirdWidth : Nat) :
    taggedTripleTime 0 1 thirdWidth =
      taggedTripleTime 1 0 thirdWidth := by
  simp [taggedTripleTime, gammaBodyTime]

/-- The state, head, and natural-coordinate tape at the transformed handoff
are literally equal when the two colliding bodies are swapped and the same
third payload and suffix are used. -/
theorem transformedHandoffConfig_empty_true_collision
    (third : List Bool) (suffix : Nat -> Bool) :
    (⟨.done, tripleFootprint 0 1 third.length,
        framedTape (tripleFinalFrame [] [true] third) suffix⟩ :
      TaggedNatConfig) =
      ⟨.done, tripleFootprint 1 0 third.length,
        framedTape (tripleFinalFrame [true] [] third) suffix⟩ := by
  rw [tripleFootprint_zero_one_collision,
    tripleFinalFrame_empty_true_collision]

/-- The two distinct canonical gamma-prefix frames converge to the same
natural-coordinate result at their respective (equal) useful times when they
are followed by the same third payload and suffix.  As above, this is a
prefix-level statement, not an identification of two complete canonical
Stream-Merge requests. -/
theorem taggedNatRun_empty_true_convergence
    (third : List Bool) (suffix : Nat -> Bool) :
    taggedNatRun
        ⟨.tag0, 0,
          framedTape
            (tripleInitialFrame 0 [] 1 [true] third.length third) suffix⟩
        (taggedTripleTime 0 1 third.length) =
      taggedNatRun
        ⟨.tag0, 0,
          framedTape
            (tripleInitialFrame 1 [true] 0 [] third.length third) suffix⟩
        (taggedTripleTime 1 0 third.length) := by
  have hleft :
      taggedNatRun
          ⟨.tag0, 0,
            framedTape
              (tripleInitialFrame 0 [] 1 [true] third.length third) suffix⟩
          (taggedTripleTime 0 1 third.length) =
        ⟨.done, tripleFootprint 0 1 third.length,
          framedTape (tripleFinalFrame [] [true] third) suffix⟩ := by
    simpa using
      (taggedNatRun_triple ([] : List Bool) [true] third suffix)
  have hright :
      taggedNatRun
          ⟨.tag0, 0,
            framedTape
              (tripleInitialFrame 1 [true] 0 [] third.length third) suffix⟩
          (taggedTripleTime 1 0 third.length) =
        ⟨.done, tripleFootprint 1 0 third.length,
          framedTape (tripleFinalFrame [true] [] third) suffix⟩ := by
    simpa using
      (taggedNatRun_triple [true] ([] : List Bool) third suffix)
  exact hleft.trans
    ((transformedHandoffConfig_empty_true_collision third suffix).trans
      hright.symm)

/-- No function of the transformed triple frame alone can recover the ordered
lengths of its first two payloads on every input.  A continuation therefore
has to retain some bounded shape information before the current wrapper
collapses to `done`, or obtain it from additional data not modeled here. -/
theorem no_tripleFinalFrame_ordered_width_recovery :
    ¬ ∃ recover : List Bool -> Nat × Nat,
        ∀ (first second third : List Bool),
          recover (tripleFinalFrame first second third) =
            (first.length, second.length) := by
  rintro ⟨recover, hrecover⟩
  have hzeroOne :
      recover (tripleFinalFrame [] [true] []) = (0, 1) := by
    simpa using hrecover [] [true] []
  have honeZero :
      recover (tripleFinalFrame [true] [] []) = (1, 0) := by
    simpa using hrecover [true] [] []
  rw [tripleFinalFrame_empty_true_collision] at hzeroOne
  have hcollision : (0, 1) = (1, 0) := hzeroOne.symm.trans honeZero
  norm_num at hcollision

end OperationalTaggedGamma
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.zippedBody_empty_true_collision
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.tripleFinalFrame_empty_true_collision
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.transformedHandoffConfig_empty_true_collision
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_empty_true_convergence
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.no_tripleFinalFrame_ordered_width_recovery
