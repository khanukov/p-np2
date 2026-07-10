import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaActual

/-!
# Actual prefix closure of the current tagged gamma front end

The natural-coordinate theorem in `OperationalTaggedGammaGlobal` deliberately
allows an arbitrary suffix after the three canonical gamma fields.  This file
transfers that exact trace to the repository's finite-tape semantics when the
suffix is a finite Boolean list included in the ambient input length.

The resulting acceptance theorem is intentionally one-sided.  It records a
real limitation of the current machine: after recognizing a canonical prefix,
the absorbing `done` state accepts independently of every remaining input bit.
It does not claim an exact-length parser, malformed-input rejection, or any
converse characterization of accepted inputs.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalTaggedGamma

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity
open OperationalGammaZipper

/-! ## A finite suffix as a natural-coordinate tape -/

/-- Read a finite Boolean list and return blank symbols after its end. -/
def finiteSuffixTape (suffix : List Bool) : Nat -> Bool :=
  fun position => suffix[position]?.getD false

/-- Placing a finite suffix after a frame agrees with reading their list
concatenation, with blanks after both lists. -/
theorem framedTape_finiteSuffixTape (frame suffix : List Bool)
    (position : Nat) :
    framedTape frame (finiteSuffixTape suffix) position =
      finiteSuffixTape (frame ++ suffix) position := by
  unfold framedTape finiteSuffixTape
  by_cases hframe : position < frame.length
  · rw [List.getElem?_eq_getElem hframe]
    rw [List.getElem?_append_left hframe]
    rw [List.getElem?_eq_getElem hframe]
    simp
  · have hge : frame.length <= position := Nat.le_of_not_gt hframe
    rw [List.getElem?_eq_none_iff.mpr hge]
    rw [List.getElem?_append_right hge]

theorem framedTape_finiteSuffixTape_blank (frame suffix : List Bool)
    (position : Nat) (hbeyond : frame.length + suffix.length <= position) :
    framedTape frame (finiteSuffixTape suffix) position = false := by
  rw [framedTape_finiteSuffixTape]
  unfold finiteSuffixTape
  rw [List.getElem?_eq_none_iff.mpr]
  · rfl
  · simpa using hbeyond

/-! ## Extended canonical input and initial agreement -/

/-- A canonical request tag and three canonical gamma fields followed by an
arbitrary finite Boolean suffix.  The suffix contributes to the actual input
length, even though the current machine never inspects it after accepting the
prefix. -/
def taggedTripleExtendedInput
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    Boolcube.Point
      (tripleFootprint payload₁.length payload₂.length payload₃.length +
        suffix.length) :=
  fun index =>
    framedTape
      (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
        payload₃.length payload₃)
      (finiteSuffixTape suffix) index.val

/-- The actual finite-tape initial configuration agrees on every allocated
cell with the natural-coordinate canonical-prefix-plus-suffix tape. -/
theorem taggedExtendedInitialConfig_finiteNatAgree
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    TaggedFiniteNatAgree
      (TaggedExecutionTM.initialConfig
        (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix))
      ⟨.tag0, 0,
        framedTape
          (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
            payload₃.length payload₃)
          (finiteSuffixTape suffix)⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  unfold TM.initialConfig
  dsimp only
  by_cases hinput : index.val <
      tripleFootprint payload₁.length payload₂.length payload₃.length +
        suffix.length
  · simp only [hinput, dite_true, taggedTripleExtendedInput]
  · have hframeLength :
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃).length =
            tripleFootprint payload₁.length payload₂.length payload₃.length :=
      tripleInitialFrame_length rfl rfl rfl
    have hbeyond :
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃).length + suffix.length <= index.val := by
      rw [hframeLength]
      omega
    simp only [hinput, dite_false]
    exact (framedTape_finiteSuffixTape_blank
      (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
        payload₃.length payload₃) suffix index.val hbeyond).symm

/-! ## Tape room and exact accepting endpoint -/

/-- Increasing the ambient input length by a finite suffix preserves the head
room needed by the exact canonical-prefix trace. -/
theorem taggedTripleTime_lt_extendedTapeLength
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    taggedTripleTime payload₁.length payload₂.length payload₃.length <
      TaggedExecutionTM.tapeLength
        (tripleFootprint payload₁.length payload₂.length payload₃.length +
          suffix.length) := by
  let footprint :=
    tripleFootprint payload₁.length payload₂.length payload₃.length
  have hbase :
      taggedTripleTime payload₁.length payload₂.length payload₃.length <
        footprint + (footprint ^ 4 + 4) + 1 := by
    simpa [footprint, TaggedExecutionTM, TM.tapeLength,
      OperationalTM.executionTM, taggedGamma] using
      taggedTripleTime_lt_tapeLength payload₁.length payload₂.length
        payload₃.length
  have hfootprint : footprint <= footprint + suffix.length := by omega
  have hpow : footprint ^ 4 <= (footprint + suffix.length) ^ 4 :=
    Nat.pow_le_pow_left hfootprint 4
  simp only [TaggedExecutionTM, TM.tapeLength,
    OperationalTM.executionTM, taggedGamma]
  change taggedTripleTime payload₁.length payload₂.length payload₃.length <
    (footprint + suffix.length) +
      ((footprint + suffix.length) ^ 4 + 4) + 1
  omega

/-- At the exact useful time, actual finite execution has accepted the
canonical three-field prefix and has preserved the arbitrary finite suffix
literally. -/
theorem taggedExecution_runConfig_extendedTriple
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    TaggedFiniteNatAgree
      (TaggedExecutionTM.runConfig
        (TaggedExecutionTM.initialConfig
          (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix))
        (taggedTripleTime payload₁.length payload₂.length payload₃.length))
      ⟨.done,
        tripleFootprint payload₁.length payload₂.length payload₃.length,
        framedTape (tripleFinalFrame payload₁ payload₂ payload₃)
          (finiteSuffixTape suffix)⟩ := by
  have hagrees := taggedFiniteNatAgree_run
    (TaggedExecutionTM.initialConfig
      (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix))
    ⟨.tag0, 0,
      framedTape
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃)
        (finiteSuffixTape suffix)⟩
    (taggedTripleTime payload₁.length payload₂.length payload₃.length)
    (taggedExtendedInitialConfig_finiteNatAgree payload₁ payload₂ payload₃
      suffix)
    (by simpa using
      taggedTripleTime_lt_extendedTapeLength payload₁ payload₂ payload₃ suffix)
  rw [taggedNatRun_triple] at hagrees
  exact hagrees

/-! ## Prefix-closed acceptance at the ambient quartic clock -/

/-- The useful canonical-prefix time fits within the quartic clock computed
from the longer, suffix-inclusive input length. -/
theorem taggedTripleTime_le_extendedRunTime
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    taggedTripleTime payload₁.length payload₂.length payload₃.length <=
      TaggedExecutionTM.runTime
        (tripleFootprint payload₁.length payload₂.length payload₃.length +
          suffix.length) := by
  let footprint :=
    tripleFootprint payload₁.length payload₂.length payload₃.length
  have hbase :
      taggedTripleTime payload₁.length payload₂.length payload₃.length <=
        footprint ^ 4 + 4 := by
    simpa [footprint, TaggedExecutionTM, OperationalTM.executionTM,
      taggedGamma] using
      taggedTripleTime_le_runTime payload₁.length payload₂.length
        payload₃.length
  have hfootprint : footprint <= footprint + suffix.length := by omega
  have hpow : footprint ^ 4 <= (footprint + suffix.length) ^ 4 :=
    Nat.pow_le_pow_left hfootprint 4
  simp only [TaggedExecutionTM, OperationalTM.executionTM, taggedGamma]
  change taggedTripleTime payload₁.length payload₂.length payload₃.length <=
    (footprint + suffix.length) ^ 4 + 4
  omega

/-- Because `done` is absorbing, acceptance of a correct canonical prefix
survives until the longer input's canonical quartic clock. -/
theorem taggedExecution_extended_run_state_done
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    (TaggedExecutionTM.run
      (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix)).state =
        .done := by
  let inputLength :=
    tripleFootprint payload₁.length payload₂.length payload₃.length +
      suffix.length
  let initial := TaggedExecutionTM.initialConfig
    (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix)
  let finish :=
    taggedTripleTime payload₁.length payload₂.length payload₃.length
  have hfinish :
      (TaggedExecutionTM.runConfig initial finish).state = .done := by
    have hagrees := taggedExecution_runConfig_extendedTriple payload₁ payload₂
      payload₃ suffix
    exact hagrees.1
  have hle : finish <= TaggedExecutionTM.runTime inputLength := by
    exact taggedTripleTime_le_extendedRunTime payload₁ payload₂ payload₃ suffix
  unfold TM.run
  change
    (TaggedExecutionTM.runConfig initial
      (TaggedExecutionTM.runTime inputLength)).state = .done
  rw [show TaggedExecutionTM.runTime inputLength =
      finish + (TaggedExecutionTM.runTime inputLength - finish) by omega]
  rw [taggedRunConfig_add]
  exact taggedRunConfig_state_done _ _ hfinish

/-- Formal prefix closure of the current absorbing-done machine: every finite
Boolean suffix, including nonblank data, is accepted after a canonical tag and
three canonical gamma fields.  This is evidence of the missing ambient-end
check, not a parser-soundness theorem. -/
theorem taggedGamma_accepts_canonical_prefix_with_suffix
    (payload₁ payload₂ payload₃ suffix : List Bool) :
    taggedGamma.accepts
      (tripleFootprint payload₁.length payload₂.length payload₃.length +
        suffix.length)
      (taggedTripleExtendedInput payload₁ payload₂ payload₃ suffix) = true := by
  unfold OperationalTM.accepts
  rw [taggedExecution_extended_run_state_done]
  rfl

end OperationalTaggedGamma
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedExtendedInitialConfig_finiteNatAgree
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedExecution_runConfig_extendedTriple
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedGamma_accepts_canonical_prefix_with_suffix
