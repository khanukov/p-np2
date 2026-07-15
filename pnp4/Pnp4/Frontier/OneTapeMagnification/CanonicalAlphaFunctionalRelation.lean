import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteRejectingGuardedCanonicalFamily
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDFunctionalProjection

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

local instance cachedInputMachineStateDecidableEqForCanonicalRelation
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-!
# A functional bit relation for the canonical alpha witness

The finite rejecting-guarded family already proves that, for positive block
size, at most one eligible canonical alpha accepts a fixed input.  This file
turns that finite witness into an actual Boolean right block and exposes the
exact interface required by `FiniteUnambiguousFBDD.forgetRightQueries`.

The code has the information-theoretically optimal ambient length
`clog₂(card Index)`.  It is obtained from the canonical finite enumeration,
so the construction is extensional and noncomputable.  In particular, this
file does **not** provide a small circuit for decoding the bits, a bounded
pathwidth decomposition of the joint `(x,z)` checker, or a size bound for such
a checker.  Those are precisely the remaining compiler obligations.
-/

/-! ## Generic logarithmic coding of a finite layered family -/

/-- Boolean words of length `width` form a carrier of size `2 ^ width`. -/
noncomputable def booleanWordEquivFin (width : Nat) :
    (Fin width -> Bool) ≃ Fin (2 ^ width) :=
  Fintype.equivFinOfCardEq (by simp)

namespace FiniteLayeredQueryProgramFamily

/-- Minimum base-two ceiling-log length sufficient to injectively name every
component of a finite family. -/
def witnessBitWidth {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Nat :=
  Nat.clog 2 (@Fintype.card family.Index family.indexFintype)

/-- There are enough Boolean words of `witnessBitWidth` bits to name every
family component. -/
theorem index_card_le_two_pow_witnessBitWidth {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    @Fintype.card family.Index family.indexFintype ≤
      2 ^ family.witnessBitWidth := by
  exact Nat.le_pow_clog (by decide)
    (@Fintype.card family.Index family.indexFintype)

/-- A classically chosen finite-enumeration embedding of component indices
into a logarithmic Boolean witness block. -/
noncomputable def witnessCodeEmbedding {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    family.Index ↪ (Fin family.witnessBitWidth -> Bool) := by
  letI : Fintype family.Index := family.indexFintype
  exact (Fintype.equivFin family.Index).toEmbedding |>.trans
    ((Fin.castLEEmb (family.index_card_le_two_pow_witnessBitWidth)).trans
      (booleanWordEquivFin family.witnessBitWidth).symm.toEmbedding)

/-- Encode one component index as a logarithmic Boolean word. -/
noncomputable def witnessCode {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (index : family.Index) :
    Fin family.witnessBitWidth -> Bool :=
  family.witnessCodeEmbedding index

/-- The logarithmic witness encoding is injective. -/
theorem witnessCode_injective {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    Function.Injective family.witnessCode :=
  family.witnessCodeEmbedding.injective

/-- Partial decoder.  Invalid Boolean words decode to `none`; words in the
range of `witnessCode` decode to their unique component index. -/
noncomputable def decodeWitnessCode {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (code : Fin family.witnessBitWidth -> Bool) : Option family.Index := by
  classical
  exact if h : ∃ index, family.witnessCode index = code then
      some (Classical.choose h)
    else
      none

/-- Exact graph of the partial decoder. -/
theorem decodeWitnessCode_eq_some_iff {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (code : Fin family.witnessBitWidth -> Bool) (index : family.Index) :
    family.decodeWitnessCode code = some index ↔
      family.witnessCode index = code := by
  classical
  unfold decodeWitnessCode
  split_ifs with h
  · constructor
    · intro heq
      have hchoice : Classical.choose h = index := Option.some.inj heq
      simpa [hchoice] using Classical.choose_spec h
    · intro hcode
      have hchoice : Classical.choose h = index :=
        family.witnessCode_injective
          ((Classical.choose_spec h).trans hcode.symm)
      simp [hchoice]
  · constructor
    · simp
    · intro hcode
      exact (h ⟨index, hcode⟩).elim

@[simp]
theorem decodeWitnessCode_witnessCode {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (index : family.Index) :
    family.decodeWitnessCode (family.witnessCode index) = some index := by
  exact (family.decodeWitnessCode_eq_some_iff
    (family.witnessCode index) index).2 rfl

/-- The joint input/witness relation: `code` names a component and that
component accepts `input`.  Invalid codes never satisfy the relation. -/
def EncodedAcceptingRelation {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool)
    (code : Fin family.witnessBitWidth -> Bool) : Prop :=
  ∃ index, code = family.witnessCode index ∧
    (family.program index).eval input = true

/-- Decoder normal form for the encoded relation. -/
theorem encodedAcceptingRelation_iff_decode {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool)
    (code : Fin family.witnessBitWidth -> Bool) :
    family.EncodedAcceptingRelation input code ↔
      ∃ index, family.decodeWitnessCode code = some index ∧
        (family.program index).eval input = true := by
  constructor
  · rintro ⟨index, rfl, heval⟩
    exact ⟨index, family.decodeWitnessCode_witnessCode index, heval⟩
  · rintro ⟨index, hdecode, heval⟩
    exact ⟨index,
      (family.decodeWitnessCode_eq_some_iff code index).1 hdecode |>.symm,
      heval⟩

/-- Existentially forgetting the code is exactly the Boolean union of the
family components. -/
theorem exists_encodedAcceptingRelation_iff_eval {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) :
    (∃ code, family.EncodedAcceptingRelation input code) ↔
      family.eval input = true := by
  rw [eval_eq_true_iff]
  constructor
  · rintro ⟨_code, index, _hcode, heval⟩
    exact ⟨index, heval⟩
  · rintro ⟨index, heval⟩
    exact ⟨family.witnessCode index, index, rfl, heval⟩

/-- Family unambiguity becomes right-functionality of the Boolean witness
relation. -/
theorem encodedAcceptingRelation_rightFunctional {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    ∀ (input : Fin n -> Bool)
      (left right : Fin family.witnessBitWidth -> Bool),
      family.EncodedAcceptingRelation input left ->
      family.EncodedAcceptingRelation input right ->
      left = right := by
  intro input left right hleft hright
  rcases hleft with ⟨leftIndex, rfl, hleftEval⟩
  rcases hright with ⟨rightIndex, rfl, hrightEval⟩
  have hindex : leftIndex = rightIndex :=
    hunambiguous input leftIndex rightIndex hleftEval hrightEval
  subst rightIndex
  rfl

/-- Injective coding transports unique existence exactly between accepting
component indices and Boolean witness words.  No family-unambiguity hypothesis
is needed for this equivalence. -/
theorem existsUnique_encodedAcceptingRelation_iff_existsUnique_index
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n -> Bool) :
    (∃! code, family.EncodedAcceptingRelation input code) ↔
      ∃! index, (family.program index).eval input = true := by
  constructor
  · rintro ⟨code, ⟨index, hcode, heval⟩, hunique⟩
    refine ⟨index, heval, ?_⟩
    intro other hother
    apply family.witnessCode_injective
    calc
      family.witnessCode other = code :=
        hunique (family.witnessCode other) ⟨other, rfl, hother⟩
      _ = family.witnessCode index := hcode
  · rintro ⟨index, heval, hunique⟩
    refine ⟨family.witnessCode index, ⟨index, rfl, heval⟩, ?_⟩
    intro code hcode
    rcases hcode with ⟨other, hencoded, hother⟩
    have hindex : other = index := hunique other hother
    subst other
    exact hencoded

/-- Under family unambiguity, exact existence and unique existence of an
encoded accepting witness coincide. -/
theorem existsUnique_encodedAcceptingRelation_iff_eval {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (input : Fin n -> Bool) :
    (∃! code, family.EncodedAcceptingRelation input code) ↔
      family.eval input = true := by
  constructor
  · rintro ⟨code, hcode, _hunique⟩
    exact (family.exists_encodedAcceptingRelation_iff_eval input).1
      ⟨code, hcode⟩
  · intro heval
    obtain ⟨code, hcode⟩ :=
      (family.exists_encodedAcceptingRelation_iff_eval input).2 heval
    refine ⟨code, hcode, ?_⟩
    intro other hother
    exact family.encodedAcceptingRelation_rightFunctional hunambiguous
      input other code hother hcode

end FiniteLayeredQueryProgramFamily

/-! ## The concrete canonical-alpha relation -/

/-- Exact logarithmic number of bits used to name an eligible canonical alpha.
This is a carrier count; it is not yet a local/streaming decoder bound. -/
abbrev canonicalAlphaWitnessBitWidth
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) : Nat :=
  Nat.clog 2
    (Fintype.card (BuiltRejectingGuardedCanonicalAlphaIndex machine T b))

/-- The eligible-alpha code length is bounded by the ceiling-log of the full
ambient timed-alpha carrier.  Eligibility can only reduce the carrier. -/
theorem canonicalAlphaWitnessBitWidth_le_ambient
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) :
    letI : Fintype (cachedInputMachine machine).State :=
      (cachedInputMachine machine).stateFintype
    canonicalAlphaWitnessBitWidth machine T b ≤
      Nat.clog 2 (Fintype.card (AmbientTimedCanonicalAlpha
        (cachedInputMachine machine).State T b)) := by
  letI : Fintype (cachedInputMachine machine).State :=
    (cachedInputMachine machine).stateFintype
  exact Nat.clog_mono_right 2
    (card_builtRejectingGuardedCanonicalAlphaIndex_le_ambient machine T b)

/-- Concrete logarithmic bit encoding of one eligible canonical-alpha index.
The input length parameter chooses the family presentation but does not enter
the index carrier or the displayed bit width. -/
noncomputable def encodeFiniteRejectingGuardedCanonicalAlpha
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool :=
  (finiteRejectingGuardedCanonicalFamily machine n T b).witnessCode index

/-- Partial decoder paired with the concrete eligible-alpha encoding. -/
noncomputable def decodeFiniteRejectingGuardedCanonicalAlpha?
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat)
    (code : Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool) :
    Option (BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :=
  FiniteLayeredQueryProgramFamily.decodeWitnessCode
    (finiteRejectingGuardedCanonicalFamily machine n T b) code

/-- Decoding an encoded eligible alpha returns that alpha exactly. -/
@[simp]
theorem decodeFiniteRejectingGuardedCanonicalAlpha?_encode
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    decodeFiniteRejectingGuardedCanonicalAlpha? machine n T b
      (encodeFiniteRejectingGuardedCanonicalAlpha machine n T b index) =
        some index := by
  exact FiniteLayeredQueryProgramFamily.decodeWitnessCode_witnessCode
    (finiteRejectingGuardedCanonicalFamily machine n T b) index

/-- The concrete eligible-alpha bit encoding is injective. -/
theorem encodeFiniteRejectingGuardedCanonicalAlpha_injective
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    Function.Injective
      (encodeFiniteRejectingGuardedCanonicalAlpha machine n T b) :=
  FiniteLayeredQueryProgramFamily.witnessCode_injective
    (finiteRejectingGuardedCanonicalFamily machine n T b)

/-- The explicit functional relation `C(x,z)` for a canonical certificate.
The right block encodes one eligible alpha index and the installed strict
guarded component for that alpha must accept `x`. -/
def finiteRejectingGuardedCanonicalFunctionalRelation
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (input : Fin n -> Bool)
    (code : Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool) : Prop :=
  FiniteLayeredQueryProgramFamily.EncodedAcceptingRelation
    (finiteRejectingGuardedCanonicalFamily machine n T b) input code

/-- The relation can equivalently use the uniform mandatory realization of
the selected component.  This is the form relevant to a later fixed-order or
pathwidth compiler. -/
theorem finiteRejectingGuardedCanonicalFunctionalRelation_iff_mandatory
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (input : Fin n -> Bool)
    (code : Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool) :
    finiteRejectingGuardedCanonicalFunctionalRelation
        machine n T b input code ↔
      ∃ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        code = FiniteLayeredQueryProgramFamily.witnessCode
          (finiteRejectingGuardedCanonicalFamily machine n T b) index ∧
        (mandatoryBuiltRejectingGuardedCanonicalComponent
          machine n index).eval input = true := by
  unfold finiteRejectingGuardedCanonicalFunctionalRelation
  constructor
  · rintro ⟨index, hcode, heval⟩
    exact ⟨index, hcode, by
      rw [mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family]
      exact heval⟩
  · rintro ⟨index, hcode, heval⟩
    exact ⟨index, hcode, by
      rw [← mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family]
      exact heval⟩

/-- Positive block size makes `C(x,z)` right-functional. -/
theorem finiteRejectingGuardedCanonicalFunctionalRelation_rightFunctional
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) :
    ∀ (input : Fin n -> Bool)
      (left right : Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool),
      finiteRejectingGuardedCanonicalFunctionalRelation
        machine n T b input left ->
      finiteRejectingGuardedCanonicalFunctionalRelation
        machine n T b input right ->
      left = right := by
  exact FiniteLayeredQueryProgramFamily.encodedAcceptingRelation_rightFunctional
      (finiteRejectingGuardedCanonicalFamily machine n T b)
      (finiteRejectingGuardedCanonicalFamily_isUnambiguous machine n T b hb)

/-- A satisfying code decodes to an eligible index whose alpha field is the
actual chronological canonical alpha of the deterministic run. -/
theorem finiteRejectingGuardedCanonicalFunctionalRelation_decodes_actualAlpha
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (code : Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool)
    (hrelation : finiteRejectingGuardedCanonicalFunctionalRelation machine
      input.length T b (fun coordinate => input.get coordinate) code) :
    ∃ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
      decodeFiniteRejectingGuardedCanonicalAlpha? machine input.length T b
          code = some index ∧
        index.1 = chronologicalTimedCanonicalAlpha
          (cachedInputMachine machine) input T b hb := by
  rcases hrelation with ⟨index, hcode, heval⟩
  refine ⟨index, ?_, ?_⟩
  · rw [hcode]
    exact decodeFiniteRejectingGuardedCanonicalAlpha?_encode
      machine input.length T b index
  · exact rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_eq
      machine input T b hb index.1
        (builtTimedAlphaVisitSchedule (cachedInputMachine machine) index.1)
        (builtCanonicalIndex_certificate machine input index heval)

/-- Exact unique-witness semantics on list inputs, inherited from the
canonical-alpha uniqueness theorem. -/
theorem existsUnique_finiteRejectingGuardedCanonicalFunctionalRelation_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (∃! code : Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool,
      finiteRejectingGuardedCanonicalFunctionalRelation
        machine input.length T b (fun coordinate => input.get coordinate)
          code) ↔
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  change
    (∃! code,
      FiniteLayeredQueryProgramFamily.EncodedAcceptingRelation
        (finiteRejectingGuardedCanonicalFamily machine input.length T b)
        (fun coordinate => input.get coordinate) code) ↔ _
  rw [FiniteLayeredQueryProgramFamily.existsUnique_encodedAcceptingRelation_iff_existsUnique_index]
  exact existsUnique_finiteRejectingGuardedCanonicalFamily_index_iff
    machine input T b hb

/-! ## Exact bridge to functional uFBDD projection -/

namespace FiniteUnambiguousFBDD

/-- A diagram on `(x,z)` realizes the canonical functional relation exactly. -/
def RealizesFiniteRejectingGuardedCanonicalFunctionalRelation
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (B : FiniteUnambiguousFBDD
      (n + canonicalAlphaWitnessBitWidth machine T b)) : Prop :=
  ∀ (input : Fin n -> Bool)
    (code : Fin (canonicalAlphaWitnessBitWidth machine T b) -> Bool),
    B.Accepts (Fin.addCases input code) ↔
      finiteRejectingGuardedCanonicalFunctionalRelation
        machine n T b input code

/-- Any exact uFBDD realizer of `C(x,z)` is right-functional. -/
theorem rightFunctional_of_realizesFiniteRejectingGuardedCanonicalRelation
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (B : FiniteUnambiguousFBDD
      (n + canonicalAlphaWitnessBitWidth machine T b))
    (hrealizes :
      B.RealizesFiniteRejectingGuardedCanonicalFunctionalRelation machine) :
    B.RightFunctional := by
  intro input left right hleft hright
  apply finiteRejectingGuardedCanonicalFunctionalRelation_rightFunctional
    machine n T b hb input left right
  · exact (hrealizes input left).1 hleft
  · exact (hrealizes input right).1 hright

/-- Exact generic projection interface: before specializing to a list input,
existentially forgetting the code recovers the finite canonical-family union. -/
theorem forgetRightQueries_accepts_iff_canonicalFamilyEval_of_realizesRelation
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (B : FiniteUnambiguousFBDD
      (n + canonicalAlphaWitnessBitWidth machine T b))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hrealizes :
      B.RealizesFiniteRejectingGuardedCanonicalFunctionalRelation machine)
    (input : Fin n -> Bool) :
    (B.forgetRightQueries
      (n := n)
      (m := canonicalAlphaWitnessBitWidth machine T b)).Accepts input ↔
      (finiteRejectingGuardedCanonicalFamily machine n T b).eval input =
        true := by
  rw [B.forgetRightQueries_accepts_iff hreadOnce]
  constructor
  · rintro ⟨code, haccepts⟩
    exact (FiniteLayeredQueryProgramFamily.exists_encodedAcceptingRelation_iff_eval
        (finiteRejectingGuardedCanonicalFamily machine n T b) input).1
          ⟨code, (hrealizes input code).1 haccepts⟩
  · intro heval
    obtain ⟨code, hrelation⟩ :=
      (FiniteLayeredQueryProgramFamily.exists_encodedAcceptingRelation_iff_eval
        (finiteRejectingGuardedCanonicalFamily machine n T b) input).2 heval
    exact ⟨code, (hrealizes input code).2 hrelation⟩

/-- Forgetting the canonical witness bits from any read-once exact realizer
recovers precisely cached one-tape acceptance. -/
theorem forgetRightQueries_accepts_iff_cachedAcceptance_of_realizesCanonicalRelation
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (B : FiniteUnambiguousFBDD
      (input.length + canonicalAlphaWitnessBitWidth machine T b))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hrealizes :
      B.RealizesFiniteRejectingGuardedCanonicalFunctionalRelation machine) :
    (B.forgetRightQueries
      (n := input.length)
      (m := canonicalAlphaWitnessBitWidth machine T b)).Accepts
        (fun coordinate => input.get coordinate) ↔
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  rw [B.forgetRightQueries_accepts_iff_canonicalFamilyEval_of_realizesRelation
    machine hreadOnce hrealizes]
  exact finiteRejectingGuardedCanonicalFamily_eval_eq_true_iff
    machine input T b hb

/-- If the joint realizer is unambiguous, functionality of the canonical
witness makes its existential projection unambiguous as well. -/
theorem forgetRightQueries_isUnambiguous_of_realizesCanonicalRelation
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (B : FiniteUnambiguousFBDD
      (n + canonicalAlphaWitnessBitWidth machine T b))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hrealizes :
      B.RealizesFiniteRejectingGuardedCanonicalFunctionalRelation machine) :
    (B.forgetRightQueries
      (n := n)
      (m := canonicalAlphaWitnessBitWidth machine T b)).IsUnambiguous := by
  exact B.forgetRightQueries_isUnambiguous_of_rightFunctional
    hreadOnce hunambiguous
      (B.rightFunctional_of_realizesFiniteRejectingGuardedCanonicalRelation
        machine hb hrealizes)

/-- Functional projection keeps the hypothetical joint checker's vertex
count exactly; no selector-size improvement is hidden in the bridge. -/
theorem forgetRightQueries_vertex_card_canonicalWitnessWidth
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (B : FiniteUnambiguousFBDD
      (n + canonicalAlphaWitnessBitWidth machine T b)) :
    @Fintype.card
        (B.forgetRightQueries
          (n := n)
          (m := canonicalAlphaWitnessBitWidth machine T b)).Vertex
        (B.forgetRightQueries
          (n := n)
          (m := canonicalAlphaWitnessBitWidth machine T b)).vertexFintype =
      @Fintype.card B.Vertex B.vertexFintype :=
  B.forgetRightQueries_vertex_card

end FiniteUnambiguousFBDD

end OneTapeMagnification
end Frontier
end Pnp4
