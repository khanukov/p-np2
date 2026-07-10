import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma
import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperContext

/-!
# Global natural-coordinate execution for the tagged gamma front end

This module begins the exact run composition for `taggedGamma`.  It keeps the
same honest scope as the transition table: successful canonical prefixes are
handled, while no converse parser or ambient-end check is inferred.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalTaggedGamma

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity
open OperationalGammaZipper

structure TaggedNatConfig where
  state : TaggedState
  head : Nat
  tape : Nat -> Bool

def taggedNatStep (config : TaggedNatConfig) : TaggedNatConfig :=
  let result := taggedGamma.step config.state (config.tape config.head)
  ⟨result.1, moveNat config.head result.2.2,
    writeNat config.tape config.head result.2.1⟩

def taggedNatRun (config : TaggedNatConfig) (steps : Nat) :
    TaggedNatConfig :=
  Nat.iterate taggedNatStep steps config

@[simp] theorem taggedNatRun_zero (config : TaggedNatConfig) :
    taggedNatRun config 0 = config := rfl

theorem taggedNatRun_add (config : TaggedNatConfig) (first second : Nat) :
    taggedNatRun config (first + second) =
      taggedNatRun (taggedNatRun config first) second := by
  unfold taggedNatRun
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem taggedNatRun_succ (config : TaggedNatConfig) (steps : Nat) :
    taggedNatRun config (steps + 1) =
      taggedNatStep (taggedNatRun config steps) := by
  unfold taggedNatRun
  exact Function.iterate_succ_apply' taggedNatStep steps config

def liftNatConfig (phase : GammaPhase) (config : NatConfig) :
    TaggedNatConfig :=
  ⟨liftCoreTarget phase config.state, config.head, config.tape⟩

theorem taggedNatStep_lift (phase : GammaPhase) (config : NatConfig)
    (hdone : config.state ≠ .done) (hreject : config.state ≠ .reject) :
    taggedNatStep (liftNatConfig phase config) =
      liftNatConfig phase (natStep config) := by
  rcases config with ⟨state, head, tape⟩
  cases state <;>
    simp_all [taggedNatStep, liftNatConfig, taggedGamma, delegatedStep,
      natStep, gammaZipper, liftCoreTarget]

theorem taggedNatRun_lift (phase : GammaPhase) (config : NatConfig)
    (steps : Nat)
    (hactive : forall elapsed, elapsed < steps ->
      (natRun config elapsed).state ≠ .done /\
        (natRun config elapsed).state ≠ .reject) :
    taggedNatRun (liftNatConfig phase config) steps =
      liftNatConfig phase (natRun config steps) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [taggedNatRun_succ]
      rw [ih (fun elapsed helapsed => hactive elapsed (by omega))]
      rw [natRun_succ]
      exact taggedNatStep_lift phase (natRun config steps)
        (hactive steps (by omega)).1 (hactive steps (by omega)).2

theorem taggedNatRun_scanFirst (phase : GammaPhase) (payload : List Bool)
    (suffix : Nat -> Bool) :
    taggedNatRun
        (liftNatConfig phase
          ⟨.scanFirst, 1,
            framedTape (initialFrame payload.length payload) suffix⟩)
        (gammaBodyTime payload.length) =
      liftNatConfig phase (canonicalFinalConfig payload suffix) := by
  rw [taggedNatRun_lift]
  · rw [natRun_scanFirst_payload]
  · intro elapsed helapsed
    exact natRun_scanFirst_active payload suffix elapsed helapsed

/-- The exact request byte consumes eight transitions, preserves its cells,
and enters the first zipper body at the following position. -/
theorem taggedNatRun_requestTag (tape : Nat -> Bool)
    (h0 : tape 0 = true) (h1 : tape 1 = false)
    (h2 : tape 2 = true) (h3 : tape 3 = true)
    (h4 : tape 4 = false) (h5 : tape 5 = false)
    (h6 : tape 6 = true) (h7 : tape 7 = true) :
    taggedNatRun ⟨.tag0, 0, tape⟩ 8 =
      ⟨.core .first .scanFirst, 8, tape⟩ := by
  simp [taggedNatRun, Function.iterate_succ_apply', taggedNatStep,
    taggedGamma, tagStep, h0, h1, h2, h3, h4, h5, h6, h7,
    moveNat]

theorem taggedNatRun_canonicalTag
    (k₁ k₂ k₃ : Nat) (payload₁ payload₂ payload₃ : List Bool)
    (suffix : Nat -> Bool) :
    taggedNatRun
        ⟨.tag0, 0,
          framedTape
            (tripleInitialFrame k₁ payload₁ k₂ payload₂ k₃ payload₃)
            suffix⟩
        8 =
      ⟨.core .first .scanFirst, 8,
        framedTape
          (tripleInitialFrame k₁ payload₁ k₂ payload₂ k₃ payload₃)
          suffix⟩ := by
  apply taggedNatRun_requestTag <;>
    simp [framedTape, tripleInitialFrame, requestTagPrefix]

theorem getLast?_cons_of_ne_nil (head : Bool) {tail : List Bool}
    (htail : tail ≠ []) :
    (head :: tail).getLast? = tail.getLast? := by
  cases tail with
  | nil => contradiction
  | cons next rest => rfl

theorem encFinal_getLast?_cons (bit : Bool) (bits : List Bool) :
    (encFinal (bit :: bits)).getLast? = some true := by
  induction bits generalizing bit with
  | nil => rfl
  | cons next rest ih =>
      change (bit :: false :: encFinal (next :: rest)).getLast? = some true
      rw [getLast?_cons_of_ne_nil bit (by simp)]
      rw [getLast?_cons_of_ne_nil false]
      · exact ih next
      · intro hempty
        have hlength := congrArg List.length hempty
        simp at hlength

@[simp] theorem zippedBody_getLast? (payload : List Bool) :
    (zippedBody payload).getLast? = some true := by
  cases payload with
  | nil => rfl
  | cons bit bits =>
      change (true :: encFinal (bit :: bits)).getLast? = some true
      rw [getLast?_cons_of_ne_nil true]
      · exact encFinal_getLast?_cons bit bits
      · intro hempty
        have hlength := congrArg List.length hempty
        simp at hlength

theorem zippedBody_dropLast_append_true (payload : List Bool) :
    (zippedBody payload).dropLast ++ [true] = zippedBody payload := by
  apply List.dropLast_append_getLast? true
  simp

theorem zippedBody_dropLast_append_sentinel (payload tail : List Bool) :
    (zippedBody payload).dropLast ++ true :: tail =
      zippedBody payload ++ tail := by
  rw [show true :: tail = [true] ++ tail by rfl]
  rw [← List.append_assoc, zippedBody_dropLast_append_true]

theorem initialFrame_eq_sentinel_body (k : Nat) (payload : List Bool) :
    initialFrame k payload = true :: gammaBody k payload := by
  simp [initialFrame, gammaBody, List.append_assoc]

theorem finalFrame_eq_sentinel_zipped (payload : List Bool) :
    finalFrame payload = true :: zippedBody payload := by
  rfl

theorem taggedNatRun_contextualPhase (phase : GammaPhase)
    (front payload tail : List Bool) (suffix : Nat -> Bool) :
    taggedNatRun
        (liftNatConfig phase
          (contextualScanFirstConfig front payload tail suffix))
        (gammaBodyTime payload.length) =
      liftNatConfig phase (contextualFinalConfig front payload tail suffix) := by
  rw [taggedNatRun_lift]
  · rw [natRun_contextualScanFirst]
  · intro elapsed helapsed
    exact natRun_contextualScanFirst_active front payload tail suffix elapsed
      helapsed

def secondFieldFront (payload₁ : List Bool) : List Bool :=
  requestTagPrefix ++ [true] ++ (zippedBody payload₁).dropLast

def thirdFieldFront (payload₁ payload₂ : List Bool) : List Bool :=
  requestTagPrefix ++ [true] ++ zippedBody payload₁ ++
    (zippedBody payload₂).dropLast

theorem taggedNatRun_firstField (payload₁ payload₂ payload₃ : List Bool)
    (suffix : Nat -> Bool) :
    taggedNatRun
        ⟨.core .first .scanFirst, 8,
          framedTape
            (tripleInitialFrame payload₁.length payload₁ payload₂.length
              payload₂ payload₃.length payload₃) suffix⟩
        (gammaBodyTime payload₁.length) =
      ⟨.core .second .scanFirst, secondGammaStart payload₁.length,
        framedTape
          (tripleAfterFirstFrame payload₁ payload₂.length payload₂
            payload₃.length payload₃) suffix⟩ := by
  have h := taggedNatRun_contextualPhase .first requestTagPrefix payload₁
    (gammaBody payload₂.length payload₂ ++
      gammaBody payload₃.length payload₃) suffix
  convert h using 1 <;> simp [liftNatConfig, contextualScanFirstConfig, contextualFinalConfig,
    contextualTape, liftCoreTarget, initialFrame_eq_sentinel_body,
    finalFrame_eq_sentinel_zipped, tripleInitialFrame,
    tripleAfterFirstFrame, secondGammaStart, List.append_assoc] <;> omega

theorem taggedNatRun_secondField
    (payload₁ payload₂ payload₃ : List Bool) (suffix : Nat -> Bool) :
    taggedNatRun
        ⟨.core .second .scanFirst, secondGammaStart payload₁.length,
          framedTape
            (tripleAfterFirstFrame payload₁ payload₂.length payload₂
              payload₃.length payload₃) suffix⟩
        (gammaBodyTime payload₂.length) =
      ⟨.core .third .scanFirst,
        thirdGammaStart payload₁.length payload₂.length,
        framedTape
          (tripleAfterSecondFrame payload₁ payload₂ payload₃.length
            payload₃) suffix⟩ := by
  have h := taggedNatRun_contextualPhase .second
    (secondFieldFront payload₁) payload₂
    (gammaBody payload₃.length payload₃) suffix
  have hstart :
      secondGammaStart payload₁.length =
        (secondFieldFront payload₁).length + 1 := by
    simp [secondGammaStart, secondFieldFront]
    omega
  have hend :
      thirdGammaStart payload₁.length payload₂.length =
        (secondFieldFront payload₁).length +
          (finalFrame payload₂).length := by
    simp [thirdGammaStart, secondFieldFront]
    omega
  rw [hstart, hend]
  simpa [liftNatConfig, contextualScanFirstConfig, contextualFinalConfig,
    contextualTape, liftCoreTarget, secondFieldFront,
    initialFrame_eq_sentinel_body, finalFrame_eq_sentinel_zipped,
    zippedBody_dropLast_append_sentinel, tripleAfterFirstFrame,
    tripleAfterSecondFrame, secondGammaStart, thirdGammaStart,
    List.append_assoc] using h

theorem taggedNatRun_thirdField
    (payload₁ payload₂ payload₃ : List Bool) (suffix : Nat -> Bool) :
    taggedNatRun
        ⟨.core .third .scanFirst,
          thirdGammaStart payload₁.length payload₂.length,
          framedTape
            (tripleAfterSecondFrame payload₁ payload₂ payload₃.length
              payload₃) suffix⟩
        (gammaBodyTime payload₃.length) =
      ⟨.done,
        tripleFootprint payload₁.length payload₂.length payload₃.length,
        framedTape (tripleFinalFrame payload₁ payload₂ payload₃)
          suffix⟩ := by
  have h := taggedNatRun_contextualPhase .third
    (thirdFieldFront payload₁ payload₂) payload₃ [] suffix
  have hstart :
      thirdGammaStart payload₁.length payload₂.length =
        (thirdFieldFront payload₁ payload₂).length + 1 := by
    simp [thirdGammaStart, thirdFieldFront]
    omega
  have hend :
      tripleFootprint payload₁.length payload₂.length payload₃.length =
        (thirdFieldFront payload₁ payload₂).length +
          (finalFrame payload₃).length := by
    simp [tripleFootprint, thirdFieldFront]
    omega
  rw [hstart, hend]
  simpa [liftNatConfig, contextualScanFirstConfig, contextualFinalConfig,
    contextualTape, liftCoreTarget, thirdFieldFront,
    initialFrame_eq_sentinel_body, finalFrame_eq_sentinel_zipped,
    zippedBody_dropLast_append_sentinel, tripleAfterSecondFrame,
    tripleFinalFrame, thirdGammaStart, tripleFootprint,
    List.append_assoc] using h

def taggedTripleTime (k₁ k₂ k₃ : Nat) : Nat :=
  8 + gammaBodyTime k₁ + gammaBodyTime k₂ + gammaBodyTime k₃

@[simp] theorem taggedTripleTime_closed (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ =
      5 * (k₁ * k₁ + k₂ * k₂ + k₃ * k₃) +
        4 * (k₁ + k₂ + k₃) + 11 := by
  simp [taggedTripleTime, gammaBodyTime]
  ring

/-- Exact one-sided run theorem for a correct tag and three canonical gamma
fields.  The arbitrary suffix is preserved literally; consequently this is
a canonical-prefix completeness theorem, not an exact-length parser
soundness theorem. -/
theorem taggedNatRun_triple (payload₁ payload₂ payload₃ : List Bool)
    (suffix : Nat -> Bool) :
    taggedNatRun
        ⟨.tag0, 0,
          framedTape
            (tripleInitialFrame payload₁.length payload₁ payload₂.length
              payload₂ payload₃.length payload₃) suffix⟩
        (taggedTripleTime payload₁.length payload₂.length
          payload₃.length) =
      ⟨.done,
        tripleFootprint payload₁.length payload₂.length payload₃.length,
        framedTape (tripleFinalFrame payload₁ payload₂ payload₃)
          suffix⟩ := by
  have htime :
      taggedTripleTime payload₁.length payload₂.length payload₃.length =
        8 + (gammaBodyTime payload₁.length +
          (gammaBodyTime payload₂.length +
            gammaBodyTime payload₃.length)) := by
    simp [taggedTripleTime]
    omega
  rw [htime, taggedNatRun_add, taggedNatRun_canonicalTag]
  rw [taggedNatRun_add, taggedNatRun_firstField]
  rw [taggedNatRun_add, taggedNatRun_secondField]
  exact taggedNatRun_thirdField payload₁ payload₂ payload₃ suffix

@[simp] theorem taggedNatStep_done (head : Nat) (tape : Nat -> Bool) :
    taggedNatStep ⟨.done, head, tape⟩ = ⟨.done, head, tape⟩ := by
  simp [taggedNatStep, taggedGamma, moveNat]

@[simp] theorem taggedNatRun_done (head : Nat) (tape : Nat -> Bool)
    (steps : Nat) :
    taggedNatRun ⟨.done, head, tape⟩ steps = ⟨.done, head, tape⟩ := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [taggedNatRun_succ, ih]
      exact taggedNatStep_done head tape

end OperationalTaggedGamma
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_canonicalTag
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_contextualPhase
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_firstField
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_secondField
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_thirdField
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_triple
