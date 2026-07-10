import Pnp4.Frontier.StreamingMagnification.EncodedTotalSearch
import Pnp4.Frontier.StreamingMagnification.StreamMergeFailureMatrix

/-!
# Fixed wires for the Stream-Merge prenex formula

This file only lays out disjoint fixed-length fields.  The outer choice is one
found/no-circuit tag followed by a candidate body.  A universal query is one
branch tag followed by an `n`-bit physical coordinate and one candidate body.
The inner wire reuses the `n + 2s` failure/trace witness.

No logical-hierarchy or resource claim follows from these codecs alone.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergePrenexWire

open StreamMergeFailureMatrix

/-- Outer `found`/`noCircuit` choice and selected code body. -/
abbrev ChoiceWire (n s : Nat) := EncodedTotalSearch.ResultWire n s

/-- One branch bit, one physical coordinate, and one competitor code. -/
abbrev QueryWire (n s : Nat) :=
  DAGCodec.BitString (1 + (n + DAGCodec.codeLength n s))

/-- Uniform innermost witness used by agreement and failure branches. -/
abbrev InnerWire (n s : Nat) := FailureWitness n s

/-- Pack the outer tag and selected body. -/
def packChoice {n s : Nat} (found : Bool) (code : DAGCodec.Code n s) :
    ChoiceWire n s :=
  EncodedTotalSearch.pack found code

/-- Read the outer branch tag. -/
def choiceTag {n s : Nat} (choice : ChoiceWire n s) : Bool :=
  EncodedTotalSearch.resultTag choice

/-- Read the selected body. -/
def choiceCode {n s : Nat} (choice : ChoiceWire n s) :
    DAGCodec.Code n s :=
  EncodedTotalSearch.resultBody choice

@[simp] theorem choiceTag_packChoice {n s : Nat} (found : Bool)
    (code : DAGCodec.Code n s) :
    choiceTag (packChoice found code) = found := by
  simp [choiceTag, packChoice]

@[simp] theorem choiceCode_packChoice {n s : Nat} (found : Bool)
    (code : DAGCodec.Code n s) :
    choiceCode (packChoice found code) = code := by
  simp [choiceCode, packChoice]

/-- Canonical all-zero coordinate field. -/
def zeroCoordinate (n : Nat) : DAGCodec.BitString n :=
  fun _ => false

/-- Canonical all-zero code field. -/
def zeroCode (n s : Nat) : DAGCodec.Code n s :=
  fun _ => false

/-- Pack the query branch, coordinate, and competitor-code fields. -/
def packQuery {n s : Nat} (competitorBranch : Bool)
    (coordinate : DAGCodec.BitString n) (code : DAGCodec.Code n s) :
    QueryWire n s :=
  Fin.append (fun _ : Fin 1 => competitorBranch)
    (Fin.append coordinate code)

/-- `false` selects agreement queries; `true` selects competitor queries. -/
def queryTag {n s : Nat} (query : QueryWire n s) : Bool :=
  query (Fin.castAdd (n + DAGCodec.codeLength n s) (0 : Fin 1))

/-- Physical-coordinate field of a universal query. -/
def queryCoordinate {n s : Nat} (query : QueryWire n s) :
    DAGCodec.BitString n :=
  fun index =>
    query (Fin.natAdd 1 (Fin.castAdd (DAGCodec.codeLength n s) index))

/-- Competitor-code field of a universal query. -/
def queryCode {n s : Nat} (query : QueryWire n s) : DAGCodec.Code n s :=
  fun index => query (Fin.natAdd 1 (Fin.natAdd n index))

@[simp] theorem queryTag_packQuery {n s : Nat} (competitorBranch : Bool)
    (coordinate : DAGCodec.BitString n) (code : DAGCodec.Code n s) :
    queryTag (packQuery competitorBranch coordinate code) =
      competitorBranch := by
  simp [queryTag, packQuery]

@[simp] theorem queryCoordinate_packQuery {n s : Nat}
    (competitorBranch : Bool) (coordinate : DAGCodec.BitString n)
    (code : DAGCodec.Code n s) :
    queryCoordinate (packQuery competitorBranch coordinate code) =
      coordinate := by
  funext index
  simp [queryCoordinate, packQuery]

@[simp] theorem queryCode_packQuery {n s : Nat}
    (competitorBranch : Bool) (coordinate : DAGCodec.BitString n)
    (code : DAGCodec.Code n s) :
    queryCode (packQuery competitorBranch coordinate code) = code := by
  funext index
  change
    Fin.append (fun _ : Fin 1 => competitorBranch)
        (Fin.append coordinate code)
        (Fin.natAdd 1 (Fin.natAdd n index)) = code index
  rw [Fin.append_right, Fin.append_right]

/-- One inhabited query used to recover query-independent outer conditions. -/
def zeroQuery (n s : Nat) : QueryWire n s :=
  packQuery false (zeroCoordinate n) (zeroCode n s)

end StreamMergePrenexWire
end StreamingMagnification
end Frontier
end Pnp4
