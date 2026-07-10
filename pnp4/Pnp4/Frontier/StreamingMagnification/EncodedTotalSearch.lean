import Pnp4.Frontier.StreamingMagnification.DAGCodec
import Pnp4.Frontier.StreamingMagnification.TotalSearch
import Mathlib.Data.Fintype.Pi

/-!
# Executable fixed-length total search-MCSP

This module puts the semantic result from `TotalSearch` on an exact wire
format.  One outer bit distinguishes a found circuit body from `noCircuit`.
The negative branch uses the all-zero body only canonically: the outer tag is
different from every found result, and `parse` rejects a negative tag with a
nonzero body.

The reference solver below is deliberately exhaustive.  It enumerates the
finite set of canonical fixed-length DAG codes and compares a decoded
circuit with the complete truth table.  Its purpose is to prove executable
totality of the specification.  It can take exponential time in the code
length, rereads the whole table through evaluation, and is **not** a witness
for the MMW streaming-RAM or any polynomial-resource solvability predicate.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace EncodedTotalSearch

/-- The syntactic tagged result required by total search-MCSP. -/
inductive EncodedResult (n s : Nat) where
  | found (circuitCode : DAGCodec.Code n s)
  | noCircuit

/-- One collision-free tag bit followed by the exact circuit-code body. -/
abbrev ResultWire (n s : Nat) :=
  DAGCodec.BitString (1 + DAGCodec.codeLength n s)

/-- Pack a tag and body into their disjoint fixed-length coordinates. -/
def pack {n s : Nat} (tag : Bool) (body : DAGCodec.Code n s) :
    ResultWire n s := fun index =>
  match finSumFinEquiv.symm index with
  | .inl _ => tag
  | .inr bodyIndex => body bodyIndex

/-- Read the unique outer result tag. -/
def resultTag {n s : Nat} (wire : ResultWire n s) : Bool :=
  wire (finSumFinEquiv (.inl (0 : Fin 1)))

/-- Read the exact fixed-length circuit body. -/
def resultBody {n s : Nat} (wire : ResultWire n s) : DAGCodec.Code n s :=
  fun index => wire (finSumFinEquiv (.inr index))

@[simp] theorem resultTag_pack {n s : Nat} (tag : Bool)
    (body : DAGCodec.Code n s) :
    resultTag (pack tag body) = tag := by
  simp [resultTag, pack]

@[simp] theorem resultBody_pack {n s : Nat} (tag : Bool)
    (body : DAGCodec.Code n s) :
    resultBody (pack tag body) = body := by
  funext index
  simp [resultBody, pack]

/-- The unique body admitted for the negative result. -/
def zeroBody (n s : Nat) : DAGCodec.Code n s := fun _ => false

/-- Serialize the tagged syntax to exactly `1 + codeLength n s` bits. -/
def serialize {n s : Nat} : EncodedResult n s -> ResultWire n s
  | .found code => pack true code
  | .noCircuit => pack false (zeroBody n s)

/--
Parse the outer syntax.  A found body is validated separately by
`DAGCodec.decode`; a negative tag is accepted only with the canonical zero
body.
-/
def parse {n s : Nat} (wire : ResultWire n s) : Option (EncodedResult n s) :=
  match resultTag wire with
  | true => some (.found (resultBody wire))
  | false =>
      if resultBody wire = zeroBody n s then some .noCircuit else none

@[simp] theorem parse_serialize {n s : Nat} (result : EncodedResult n s) :
    parse (serialize result) = some result := by
  cases result <;> simp [parse, serialize]

/-- Serialization loses no tagged-result information. -/
theorem serialize_injective {n s : Nat} :
    Function.Injective (@serialize n s) := by
  intro left right heq
  have hparsed := congrArg (@parse n s) heq
  simpa using hparsed

/-- The failure wire cannot collide with any found circuit body. -/
theorem serialize_found_ne_noCircuit {n s : Nat}
    (code : DAGCodec.Code n s) :
    serialize (EncodedResult.found code) ≠
      serialize (EncodedResult.noCircuit : EncodedResult n s) := by
  intro heq
  have htag := congrArg (@resultTag n s) heq
  simp [serialize] at htag

theorem parse_found_iff {n s : Nat} (wire : ResultWire n s)
    (code : DAGCodec.Code n s) :
    parse wire = some (.found code) <->
      resultTag wire = true /\ resultBody wire = code := by
  cases htag : resultTag wire <;> simp [parse, htag]

theorem parse_noCircuit_iff {n s : Nat} (wire : ResultWire n s) :
    parse wire = some (.noCircuit : EncodedResult n s) <->
      resultTag wire = false /\ resultBody wire = zeroBody n s := by
  cases htag : resultTag wire <;> simp [parse, htag]

/-- Validate a syntactic found body and expose the semantic total result. -/
def validate {n s : Nat} :
    EncodedResult n s -> Option (TotalSearch.MCSPResult n s)
  | .found code =>
      (DAGCodec.decode code).map fun circuit =>
        TotalSearch.MCSPResult.found circuit
  | .noCircuit => some .noCircuit

/-- Parse the wire and validate any circuit carried by its found branch. -/
def decodeSemantic {n s : Nat} (wire : ResultWire n s) :
    Option (TotalSearch.MCSPResult n s) :=
  (parse wire).bind validate

@[simp] theorem validate_found_encode {n s : Nat}
    (circuit : DAGCodec.BoundedCircuit n s) :
    validate (EncodedResult.found (DAGCodec.encode circuit)) =
      some (TotalSearch.MCSPResult.found circuit) := by
  simp [validate]

@[simp] theorem validate_noCircuit {n s : Nat} :
    validate (EncodedResult.noCircuit : EncodedResult n s) =
      some (TotalSearch.MCSPResult.noCircuit : TotalSearch.MCSPResult n s) := by
  rfl

@[simp] theorem decodeSemantic_serialize_found_encode {n s : Nat}
    (circuit : DAGCodec.BoundedCircuit n s) :
    decodeSemantic (serialize (.found (DAGCodec.encode circuit))) =
      some (TotalSearch.MCSPResult.found circuit) := by
  simp [decodeSemantic]

@[simp] theorem decodeSemantic_serialize_noCircuit {n s : Nat} :
    decodeSemantic
        (serialize (EncodedResult.noCircuit : EncodedResult n s)) =
      some (TotalSearch.MCSPResult.noCircuit : TotalSearch.MCSPResult n s) := by
  simp [decodeSemantic]

/-! ## Finite executable reference search -/

/-- Re-reading an assembled word recovers every one of its input bits. -/
theorem bitsOfWord_wordOfBits {length : Nat}
    (bits : Fin length -> Bool) :
    DAGCodec.bitsOfWord (DAGCodec.wordOfBits bits) = bits := by
  funext index
  change (DAGCodec.wordOfBits bits).getLsbD index.val = bits index
  simp only [DAGCodec.wordOfBits, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Interpret a natural number modulo the external circuit-code width. -/
def codeOfNat (n s value : Nat) : DAGCodec.Code n s :=
  DAGCodec.bitsOfWord
    (BitVec.ofNat (DAGCodec.codeLength n s) value)

/-- Every fixed-length Boolean body, enumerated by its unsigned value. -/
def allCodes (n s : Nat) : List (DAGCodec.Code n s) :=
  (List.range (2 ^ DAGCodec.codeLength n s)).map (codeOfNat n s)

@[simp] theorem codeOfNat_wordOfBits_toNat {n s : Nat}
    (code : DAGCodec.Code n s) :
    codeOfNat n s (DAGCodec.wordOfBits code).toNat = code := by
  unfold codeOfNat
  rw [show BitVec.ofNat (DAGCodec.codeLength n s)
      (DAGCodec.wordOfBits code).toNat = DAGCodec.wordOfBits code by
    simp]
  exact bitsOfWord_wordOfBits code

/-- The numeric list is extensionally complete for fixed-length bodies. -/
@[simp] theorem mem_allCodes {n s : Nat} (code : DAGCodec.Code n s) :
    code ∈ allCodes n s := by
  rw [allCodes, List.mem_map]
  refine ⟨(DAGCodec.wordOfBits code).toNat, ?_, ?_⟩
  · exact List.mem_range.mpr (DAGCodec.wordOfBits code).isLt
  · exact codeOfNat_wordOfBits_toNat code

/-- All canonical bounded-circuit codes, filtered executably from all bodies. -/
def candidateCodes (n s : Nat) : List (DAGCodec.Code n s) :=
  (allCodes n s).filter fun code => (DAGCodec.decode code).isSome

@[simp] theorem mem_candidateCodes_iff {n s : Nat}
    (code : DAGCodec.Code n s) :
    code ∈ candidateCodes n s <-> (DAGCodec.decode code).isSome = true := by
  simp [candidateCodes]

@[simp] theorem encode_mem_candidateCodes {n s : Nat}
    (circuit : DAGCodec.BoundedCircuit n s) :
    DAGCodec.encode circuit ∈ candidateCodes n s := by
  simp [candidateCodes]

/-- Executable equality against the entire lexicographic truth table. -/
def tableMatches {n s : Nat} (table : TotalSearch.TruthTable n)
    (circuit : DAGCodec.BoundedCircuit n s) : Bool :=
  decide
    (List.ofFn (TotalSearch.circuitTruthTable circuit.val) =
      List.ofFn table)

@[simp] theorem tableMatches_eq_true_iff {n s : Nat}
    (table : TotalSearch.TruthTable n)
    (circuit : DAGCodec.BoundedCircuit n s) :
    tableMatches table circuit = true <->
      TotalSearch.Computes circuit.val table := by
  simp [tableMatches, TotalSearch.Computes, List.ofFn_inj]

/-- A code works exactly when it decodes and computes the supplied table. -/
def codeWorks {n s : Nat} (table : TotalSearch.TruthTable n)
    (code : DAGCodec.Code n s) : Bool :=
  match DAGCodec.decode code with
  | none => false
  | some circuit => tableMatches table circuit

theorem codeWorks_eq_true_iff {n s : Nat}
    (table : TotalSearch.TruthTable n) (code : DAGCodec.Code n s) :
    codeWorks table code = true <->
      ∃ circuit : DAGCodec.BoundedCircuit n s,
        DAGCodec.decode code = some circuit /\
          TotalSearch.Computes circuit.val table := by
  unfold codeWorks
  cases hdecode : DAGCodec.decode code with
  | none => simp
  | some circuit => simp

@[simp] theorem codeWorks_encode_eq_true_iff {n s : Nat}
    (table : TotalSearch.TruthTable n)
    (circuit : DAGCodec.BoundedCircuit n s) :
    codeWorks table (DAGCodec.encode circuit) = true <->
      TotalSearch.Computes circuit.val table := by
  simp [codeWorks]

/-- Deterministically select the first working canonical body, if any. -/
def firstWorkingCode {n s : Nat} (table : TotalSearch.TruthTable n) :
    Option (DAGCodec.Code n s) :=
  (candidateCodes n s).find? (codeWorks table)

theorem firstWorkingCode_some_sound {n s : Nat}
    {table : TotalSearch.TruthTable n} {code : DAGCodec.Code n s}
    (hfound : firstWorkingCode table = some code) :
    ∃ circuit : DAGCodec.BoundedCircuit n s,
      DAGCodec.decode code = some circuit /\
        TotalSearch.Computes circuit.val table := by
  apply (codeWorks_eq_true_iff table code).mp
  exact List.find?_some hfound

theorem firstWorkingCode_eq_none_iff {n s : Nat}
    (table : TotalSearch.TruthTable n) :
    firstWorkingCode (s := s) table = none <->
      ¬ TotalSearch.HasCircuit n s table := by
  unfold firstWorkingCode
  rw [List.find?_eq_none]
  constructor
  · intro hNoFound hHas
    rcases hHas with ⟨circuit, hsize, hcomputes⟩
    let bounded : DAGCodec.BoundedCircuit n s := ⟨circuit, hsize⟩
    have hworks :
        codeWorks table (DAGCodec.encode bounded) = true :=
      (codeWorks_encode_eq_true_iff table bounded).2 hcomputes
    exact hNoFound (DAGCodec.encode bounded)
      (encode_mem_candidateCodes bounded) hworks
  · intro hNone code _hmem hworks
    rcases (codeWorks_eq_true_iff table code).mp hworks with
      ⟨circuit, _hdecode, hcomputes⟩
    exact hNone ⟨circuit.val, circuit.property, hcomputes⟩

/-- The finite reference result before its fixed-length serialization. -/
def referenceResult {n s : Nat} (table : TotalSearch.TruthTable n) :
    EncodedResult n s :=
  match firstWorkingCode (s := s) table with
  | some code => .found code
  | none => .noCircuit

/-- The fixed-length output of the finite exhaustive reference solver. -/
def referenceSolver {n s : Nat} (table : TotalSearch.TruthTable n) :
    ResultWire n s :=
  serialize (referenceResult (s := s) table)

/-! ## All four total-search directions at the encoded surface -/

/-- A found code decodes to a valid bounded DAG computing the whole table. -/
theorem reference_found_sound {n s : Nat}
    {table : TotalSearch.TruthTable n} {code : DAGCodec.Code n s}
    (hresult : referenceResult (s := s) table = .found code) :
    ∃ circuit : DAGCodec.BoundedCircuit n s,
      DAGCodec.decode code = some circuit /\
        circuit.val.val.Valid n /\
        circuit.val.gateCount <= s /\
        TotalSearch.Computes circuit.val table := by
  unfold referenceResult at hresult
  cases hfound : firstWorkingCode (s := s) table with
  | none => simp [hfound] at hresult
  | some foundCode =>
      have hcode : foundCode = code := by
        simpa [hfound] using hresult
      subst code
      rcases firstWorkingCode_some_sound hfound with
        ⟨circuit, hdecode, hcomputes⟩
      exact ⟨circuit, hdecode, circuit.val.property, circuit.property,
        hcomputes⟩

/-- Existence of a suitable DAG forces the exhaustive result to be found. -/
theorem reference_found_complete {n s : Nat}
    {table : TotalSearch.TruthTable n}
    (hHas : TotalSearch.HasCircuit n s table) :
    ∃ code : DAGCodec.Code n s,
      ∃ circuit : DAGCodec.BoundedCircuit n s,
        referenceResult (s := s) table = .found code /\
        DAGCodec.decode code = some circuit /\
        TotalSearch.Computes circuit.val table := by
  cases hfound : firstWorkingCode (s := s) table with
  | none =>
      exact ((firstWorkingCode_eq_none_iff table).mp hfound hHas).elim
  | some code =>
      rcases firstWorkingCode_some_sound hfound with
        ⟨circuit, hdecode, hcomputes⟩
      exact ⟨code, circuit, by simp [referenceResult, hfound], hdecode,
        hcomputes⟩

/-- A negative exhaustive result proves genuine non-existence. -/
theorem reference_noCircuit_sound {n s : Nat}
    {table : TotalSearch.TruthTable n}
    (hresult : referenceResult (s := s) table = .noCircuit) :
    ¬ TotalSearch.HasCircuit n s table := by
  cases hfound : firstWorkingCode (s := s) table with
  | none => exact (firstWorkingCode_eq_none_iff table).mp hfound
  | some code => simp [referenceResult, hfound] at hresult

/-- Genuine non-existence forces the exhaustive result to be negative. -/
theorem reference_noCircuit_complete {n s : Nat}
    {table : TotalSearch.TruthTable n}
    (hNone : ¬ TotalSearch.HasCircuit n s table) :
    referenceResult (s := s) table = .noCircuit := by
  have hfound : firstWorkingCode (s := s) table = none :=
    (firstWorkingCode_eq_none_iff table).2 hNone
  simp [referenceResult, hfound]

/-! ## Semantic decoded correctness and the search-to-decision bridge -/

/-- The serialized reference result always decodes to a correct total result. -/
theorem reference_decodes_correct {n s : Nat}
    (table : TotalSearch.TruthTable n) :
    ∃ result : TotalSearch.MCSPResult n s,
      decodeSemantic (referenceSolver (s := s) table) = some result /\
        TotalSearch.Correct table result := by
  cases hfound : firstWorkingCode (s := s) table with
  | none =>
      refine ⟨TotalSearch.MCSPResult.noCircuit, ?_, ?_⟩
      · simp [referenceSolver, referenceResult, hfound, decodeSemantic]
      · exact (firstWorkingCode_eq_none_iff table).mp hfound
  | some code =>
      rcases firstWorkingCode_some_sound hfound with
        ⟨circuit, hdecode, hcomputes⟩
      refine ⟨TotalSearch.MCSPResult.found circuit, ?_, ?_⟩
      · simp [referenceSolver, referenceResult, hfound, decodeSemantic,
          validate, hdecode]
      · exact hcomputes

/-- Any semantic result decoded from the reference wire is correct. -/
theorem reference_decode_correct {n s : Nat}
    {table : TotalSearch.TruthTable n}
    {result : TotalSearch.MCSPResult n s}
    (hdecode :
      decodeSemantic (referenceSolver (s := s) table) = some result) :
    TotalSearch.Correct table result := by
  rcases reference_decodes_correct (s := s) table with
    ⟨expected, hexpected, hcorrect⟩
  have heq : expected = result :=
    Option.some.inj (hexpected.symm.trans hdecode)
  subst result
  exact hcorrect

/-- Wire-level found soundness. -/
theorem referenceSolver_found_sound {n s : Nat}
    {table : TotalSearch.TruthTable n}
    {circuit : TotalSearch.BoundedCircuit n s}
    (hdecode : decodeSemantic (referenceSolver (s := s) table) =
      some (TotalSearch.MCSPResult.found circuit)) :
    circuit.val.gateCount <= s /\
      TotalSearch.Computes circuit.val table :=
  TotalSearch.found_sound (reference_decode_correct hdecode)

/-- Wire-level found completeness. -/
theorem referenceSolver_found_complete {n s : Nat}
    {table : TotalSearch.TruthTable n}
    (hHas : TotalSearch.HasCircuit n s table) :
    ∃ circuit : TotalSearch.BoundedCircuit n s,
      decodeSemantic (referenceSolver (s := s) table) =
        some (TotalSearch.MCSPResult.found circuit) := by
  rcases reference_decodes_correct (s := s) table with
    ⟨result, hdecode, hcorrect⟩
  rcases TotalSearch.exists_implies_result_found hcorrect hHas with
    ⟨circuit, hresult⟩
  subst result
  exact ⟨circuit, hdecode⟩

/-- Wire-level negative soundness. -/
theorem referenceSolver_noCircuit_sound {n s : Nat}
    {table : TotalSearch.TruthTable n}
    (hdecode : decodeSemantic (referenceSolver (s := s) table) =
      some (TotalSearch.MCSPResult.noCircuit :
        TotalSearch.MCSPResult n s)) :
    ¬ TotalSearch.HasCircuit n s table :=
  TotalSearch.noCircuit_sound (reference_decode_correct hdecode)

/-- Wire-level negative completeness. -/
theorem referenceSolver_noCircuit_complete {n s : Nat}
    {table : TotalSearch.TruthTable n}
    (hNone : ¬ TotalSearch.HasCircuit n s table) :
    decodeSemantic (referenceSolver (s := s) table) =
      some (TotalSearch.MCSPResult.noCircuit :
        TotalSearch.MCSPResult n s) := by
  rcases reference_decodes_correct (s := s) table with
    ⟨result, hdecode, hcorrect⟩
  have hresult : result = TotalSearch.MCSPResult.noCircuit :=
    TotalSearch.noCircuit_complete hcorrect hNone
  subst result
  exact hdecode

/-- Read a decision bit only after parsing and semantic validation. -/
def decisionFromWire {n s : Nat} (wire : ResultWire n s) : Option Bool :=
  (decodeSemantic wire).map TotalSearch.decisionBit

/-- Every correct decoded total-search wire decides exact DAG-MCSP. -/
theorem decisionFromWire_eq_some_true_iff {n s : Nat}
    {table : TotalSearch.TruthTable n} {wire : ResultWire n s}
    {result : TotalSearch.MCSPResult n s}
    (hdecode : decodeSemantic wire = some result)
    (hcorrect : TotalSearch.Correct table result) :
    decisionFromWire wire = some true <->
      TotalSearch.HasCircuit n s table := by
  simp only [decisionFromWire, hdecode, Option.map_some, Option.some.injEq]
  exact TotalSearch.decisionBit_eq_true_iff hcorrect

/-- The exhaustive total-search solver therefore gives an executable decider. -/
def referenceDecision {n s : Nat} (table : TotalSearch.TruthTable n) : Bool :=
  (decisionFromWire (referenceSolver (s := s) table)).getD false

theorem referenceDecision_eq_true_iff {n s : Nat}
    (table : TotalSearch.TruthTable n) :
    referenceDecision (s := s) table = true <->
      TotalSearch.HasCircuit n s table := by
  rcases reference_decodes_correct (s := s) table with
    ⟨result, hdecode, hcorrect⟩
  simp only [referenceDecision, decisionFromWire, hdecode, Option.map_some,
    Option.getD_some]
  exact TotalSearch.decisionBit_eq_true_iff hcorrect

end EncodedTotalSearch
end StreamingMagnification
end Frontier
end Pnp4
