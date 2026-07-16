import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualLCPGeometry
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDResidualRectangle

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact labelled suffix buckets for the mandatory selector

The reverse-LCP argument writes an accepting derivation from the accepting
sink back towards the root.  A common prefix in that orientation is a common
forward accepting suffix in the `FiniteUnambiguousFBDD.Walk` orientation.

There are two small but important representation issues.

* A bare graph walk does not remember whether a query used its false or true
  edge when those edges have the same target.
* Silent-choice edges are propositions in the current graph API.  The source
  and target distinguish every edge of the quotient graph, but repeated
  occurrences of the same target in a choice list are intentionally
  identified by `FiniteUFBDDNode.HasChild`.

`InputLabelledFullStep` is therefore the strongest exact edge trace exposed
by the current graph model: it records source and target for every step and
also the queried coordinate and Boolean edge label for query steps.  We then
choose the unique compatible accepting walk of an accepted input
noncomputably.

Two complementary bucket surfaces are proved below.  The first accepts a
supplied common suffix.  The second computes the genuine longest common
suffix of every ordered accepted-model pair, proves that its finite fibers
are disjoint and cover the residual ordered-pair set, and lifts every
nonempty fixed-reference fiber back to a single dependent suffix `Walk`.
Full-step injectivity identifies both its cut vertex and graph suffix.  The
resulting fixed-reference maximal bucket has the sharp frozen residual
capacity unconditionally; empty fibers are handled trivially.

The graph API still intentionally identifies repeated occurrences of one
silent-choice target.  Thus the partition is exact for the quotient graph
represented by `FiniteUFBDDNode.HasChild`; recovering occurrence indices
would require strengthening that underlying graph datatype, not another
proof about the present `Walk`.
-/

noncomputable section

namespace FiniteUnambiguousFBDD

open FiniteResidualAcceptedModelCount

local instance acceptedModelDecidableEqForReverseLCP {n : Nat}
    (B : FiniteUnambiguousFBDD n) : DecidableEq B.AcceptedModel :=
  Classical.decEq _

/-- One edge of a walk with its full graph endpoints and, at a query vertex,
the Boolean label selecting the edge.  The label distinguishes false and
true even when their graph targets coincide. -/
structure InputLabelledFullStep {n : Nat}
    (B : FiniteUnambiguousFBDD n) where
  source : B.Vertex
  target : B.Vertex
  query? : Option (Fin n × Bool)
deriving DecidableEq

namespace InputLabelledFullStep

/-- Project a full edge step to the older query-only event representation. -/
def queryEvent? {n : Nat} {B : FiniteUnambiguousFBDD n}
    (step : InputLabelledFullStep B) :
    Option (InputLabelledQueryEvent B) :=
  step.query?.map fun query => {
    vertex := step.source
    queryIndex := query.1
    value := query.2
  }

end InputLabelledFullStep

namespace Walk

@[simp]
theorem append_nil {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target) :
    walk.append (.nil target) = walk := by
  induction walk with
  | nil vertex => rfl
  | cons edge tail ih => simp [append, ih]

/-- The labelled edge leaving `source`.  A silent step retains both graph
endpoints; a query step additionally retains its Boolean edge label. -/
def inputLabelledFullStep {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n -> Bool) (source target : B.Vertex) :
    InputLabelledFullStep B :=
  match B.node source with
  | .query queryIndex _ _ =>
      { source := source
        target := target
        query? := some (queryIndex, input queryIndex) }
  | .choice _ =>
      { source := source, target := target, query? := none }
  | .sink =>
      { source := source, target := target, query? := none }

@[simp]
theorem inputLabelledFullStep_source {n : Nat}
    (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool)
    (source target : B.Vertex) :
    (inputLabelledFullStep B input source target).source = source := by
  cases hnode : B.node source <;>
    simp [inputLabelledFullStep, hnode]

@[simp]
theorem inputLabelledFullStep_target {n : Nat}
    (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool)
    (source target : B.Vertex) :
    (inputLabelledFullStep B input source target).target = target := by
  cases hnode : B.node source <;>
    simp [inputLabelledFullStep, hnode]

/-- Complete input-labelled edge trace of a formal walk. -/
def inputLabelledFullTrace {n : Nat} {B : FiniteUnambiguousFBDD n}
    (input : Fin n -> Bool) :
    {source target : B.Vertex} -> B.Walk source target ->
      List (InputLabelledFullStep B)
  | _, _, .nil _ => []
  | _, _, .cons (source := source) (middle := middle) _ tail =>
      inputLabelledFullStep B input source middle ::
        tail.inputLabelledFullTrace input

/-- Projecting the full labelled edge trace recovers exactly the query-only
labelled trace used by the residual local-completeness theorem. -/
theorem inputLabelledFullTrace_filterMap_queryEvent?
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (input : Fin n -> Bool) :
    (walk.inputLabelledFullTrace input).filterMap
        InputLabelledFullStep.queryEvent? =
      walk.inputLabelledQueryTrace input := by
  induction walk with
  | nil vertex =>
      simp [inputLabelledFullTrace, inputLabelledQueryTrace, queryEvents]
  | @cons source middle target edge tail ih =>
      cases hnode : B.node source <;>
        simp [inputLabelledFullTrace, inputLabelledFullStep,
          InputLabelledFullStep.queryEvent?, inputLabelledQueryTrace,
          queryEvents, FiniteUFBDDNode.queryEvent?, hnode, ih]

/-- Equality of full labelled traces for the same graph suffix implies
equality of its query-labelled projection. -/
theorem inputLabelledQueryTrace_eq_of_inputLabelledFullTrace_eq
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (left right : Fin n -> Bool)
    (htrace : walk.inputLabelledFullTrace left =
      walk.inputLabelledFullTrace right) :
    walk.inputLabelledQueryTrace left =
      walk.inputLabelledQueryTrace right := by
  have hprojected := congrArg
    (List.filterMap InputLabelledFullStep.queryEvent?) htrace
  simpa [walk.inputLabelledFullTrace_filterMap_queryEvent?] using hprojected

/-- For fixed endpoints, the complete graph endpoints in every labelled step
make the full trace injective back to the bare walk.  Inputs may differ; their
labels only strengthen the equality premise. -/
theorem eq_of_inputLabelledFullTrace_eq
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex}
    (leftWalk rightWalk : B.Walk source target)
    (leftInput rightInput : Fin n -> Bool)
    (htrace : leftWalk.inputLabelledFullTrace leftInput =
      rightWalk.inputLabelledFullTrace rightInput) :
    leftWalk = rightWalk := by
  induction leftWalk with
  | nil vertex =>
      cases rightWalk with
      | nil => rfl
      | cons edge tail =>
          simp [inputLabelledFullTrace] at htrace
  | @cons source middle target edge tail ih =>
      cases rightWalk with
      | nil =>
          simp [inputLabelledFullTrace] at htrace
      | @cons _ rightMiddle _ rightEdge rightTail =>
          simp only [inputLabelledFullTrace, List.cons.injEq] at htrace
          have hmiddle : middle = rightMiddle :=
            by simpa using
              congrArg InputLabelledFullStep.target htrace.1
          subst rightMiddle
          have htail : tail = rightTail :=
            ih rightTail htrace.2
          subst rightTail
          rfl

/-- Equality of full traces to a common terminal vertex also identifies their
possibly dependent source vertices. -/
theorem source_eq_of_inputLabelledFullTrace_eq
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {leftSource rightSource target : B.Vertex}
    (leftWalk : B.Walk leftSource target)
    (rightWalk : B.Walk rightSource target)
    (leftInput rightInput : Fin n -> Bool)
    (htrace : leftWalk.inputLabelledFullTrace leftInput =
      rightWalk.inputLabelledFullTrace rightInput) :
    leftSource = rightSource := by
  cases leftWalk with
  | nil vertex =>
      cases rightWalk with
      | nil => rfl
      | cons edge tail =>
          simp [inputLabelledFullTrace] at htrace
  | @cons leftSource leftMiddle target edge tail =>
      cases rightWalk with
      | nil =>
          simp [inputLabelledFullTrace] at htrace
      | @cons rightSource rightMiddle target rightEdge rightTail =>
          simp only [inputLabelledFullTrace, List.cons.injEq] at htrace
          simpa using congrArg InputLabelledFullStep.source htrace.1

/-- A walk to a fixed terminal vertex with its dependent source packaged. -/
def AnyWalkTo {n : Nat} (B : FiniteUnambiguousFBDD n)
    (target : B.Vertex) :=
  Sigma fun source => B.Walk source target

/-- Full labelled traces are injective even before the dependent source is
known: equality identifies both the cut vertex and the suffix walk. -/
theorem anyWalkTo_eq_of_inputLabelledFullTrace_eq
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (target : B.Vertex) (leftInput rightInput : Fin n -> Bool)
    (left right : AnyWalkTo B target)
    (htrace : left.2.inputLabelledFullTrace leftInput =
      right.2.inputLabelledFullTrace rightInput) :
    left = right := by
  rcases left with ⟨leftSource, leftWalk⟩
  induction leftWalk with
  | nil vertex =>
      rcases right with ⟨rightSource, rightWalk⟩
      cases rightWalk with
      | nil => rfl
      | cons edge tail => simp [inputLabelledFullTrace] at htrace
  | @cons source middle target edge tail ih =>
      rcases right with ⟨rightSource, rightWalk⟩
      cases rightWalk with
      | nil => simp [inputLabelledFullTrace] at htrace
      | @cons ignoredSource otherMiddle otherTarget otherEdge otherTail =>
          have hparts := List.cons.inj htrace
          have hsource : source = rightSource := by
            have h := congrArg InputLabelledFullStep.source hparts.1
            simpa using h
          have hmiddle : middle = otherMiddle := by
            have h := congrArg InputLabelledFullStep.target hparts.1
            simpa using h
          subst rightSource
          subst otherMiddle
          have htailSigma :
              (⟨middle, tail⟩ : AnyWalkTo B target) =
                ⟨middle, otherTail⟩ :=
            ih (right := ⟨middle, otherTail⟩) hparts.2
          cases htailSigma
          rfl

/-- Every suffix of a full labelled trace lifts to an actual dependent suffix
walk and a matching prefix split.  This is the typed-walk half of reverse-LCP
selection. -/
theorem exists_split_of_isSuffix_inputLabelledFullTrace
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (input : Fin n -> Bool) (key : List (InputLabelledFullStep B))
    (hkey : key <:+ walk.inputLabelledFullTrace input) :
    ∃ vertex : B.Vertex,
      ∃ prefixWalk : B.Walk source vertex,
        ∃ suffixWalk : B.Walk vertex target,
          walk = prefixWalk.append suffixWalk ∧
            suffixWalk.inputLabelledFullTrace input = key := by
  induction walk with
  | nil vertex =>
      have hkeyNil : key = [] := by
        simpa [inputLabelledFullTrace] using
          (List.suffix_iff_eq_drop.mp hkey)
      subst key
      exact ⟨vertex, .nil vertex, .nil vertex, rfl, rfl⟩
  | @cons source middle target edge tail ih =>
      rcases hkey with ⟨before, hbefore⟩
      cases before with
      | nil =>
          have hwhole : key =
              (inputLabelledFullStep B input source middle) ::
                tail.inputLabelledFullTrace input := by
            simpa [inputLabelledFullTrace] using hbefore
          exact ⟨source, .nil source, .cons edge tail, rfl,
            by simpa [inputLabelledFullTrace] using hwhole.symm⟩
      | cons beforeHead beforeTail =>
          have htailSuffix :
              key <:+ tail.inputLabelledFullTrace input := by
            refine ⟨beforeTail, ?_⟩
            simpa [inputLabelledFullTrace] using
              (List.cons.inj hbefore).2
          rcases ih htailSuffix with
            ⟨vertex, prefixWalk, suffixWalk, htailSplit, hsuffixTrace⟩
          refine ⟨vertex, .cons edge prefixWalk, suffixWalk, ?_, hsuffixTrace⟩
          simp [append, htailSplit]

end Walk

/-! ## Exact finite-list longest common suffix -/

namespace ReverseLCP

/-- Longest common prefix, computed synchronously from the heads. -/
def longestCommonPrefix {α : Type*} [DecidableEq α] :
    List α -> List α -> List α
  | leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead = rightHead then
        leftHead :: longestCommonPrefix leftTail rightTail
      else []
  | _, _ => []

theorem longestCommonPrefix_comm {α : Type*} [DecidableEq α]
    (left right : List α) :
    longestCommonPrefix left right = longestCommonPrefix right left := by
  induction left generalizing right with
  | nil => simp [longestCommonPrefix]
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp [longestCommonPrefix]
      | cons rightHead rightTail =>
          by_cases heq : leftHead = rightHead
          · subst rightHead
            simp [longestCommonPrefix, ih]
          · have hne : rightHead ≠ leftHead := fun h => heq h.symm
            simp [longestCommonPrefix, heq, hne]

theorem longestCommonPrefix_isPrefix_left
    {α : Type*} [DecidableEq α] (left right : List α) :
    longestCommonPrefix left right <+: left := by
  induction left generalizing right with
  | nil => simp [longestCommonPrefix, List.IsPrefix]
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp [longestCommonPrefix, List.IsPrefix]
      | cons rightHead rightTail =>
          by_cases heq : leftHead = rightHead
          · subst rightHead
            simp only [longestCommonPrefix, if_pos]
            rcases ih rightTail with ⟨tail, htail⟩
            exact ⟨tail, by simp [htail]⟩
          · simp [longestCommonPrefix, heq, List.IsPrefix]

theorem longestCommonPrefix_isPrefix_right
    {α : Type*} [DecidableEq α] (left right : List α) :
    longestCommonPrefix left right <+: right := by
  rw [longestCommonPrefix_comm]
  exact longestCommonPrefix_isPrefix_left right left

/-- The computed common prefix is longest among all common prefixes. -/
theorem length_le_longestCommonPrefix_of_isPrefix
    {α : Type*} [DecidableEq α]
    (candidate left right : List α)
    (hleft : candidate <+: left) (hright : candidate <+: right) :
    candidate.length ≤ (longestCommonPrefix left right).length := by
  induction left generalizing right candidate with
  | nil =>
      rcases hleft with ⟨tail, htail⟩
      have hc : candidate = [] := (List.append_eq_nil_iff.mp htail).1
      simp [hc]
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          rcases hright with ⟨tail, htail⟩
          have hc : candidate = [] := (List.append_eq_nil_iff.mp htail).1
          simp [hc]
      | cons rightHead rightTail =>
          by_cases heq : leftHead = rightHead
          · subst rightHead
            cases candidate with
            | nil => simp
            | cons candidateHead candidateTail =>
                rcases hleft with ⟨leftRest, hleftRest⟩
                rcases hright with ⟨rightRest, hrightRest⟩
                simp only [List.cons_append, List.cons.injEq] at hleftRest hrightRest
                simp only [longestCommonPrefix, if_pos, List.length_cons,
                  Nat.succ_le_succ_iff]
                apply ih candidateTail rightTail
                · exact ⟨leftRest, hleftRest.2⟩
                · exact ⟨rightRest, hrightRest.2⟩
          · cases candidate with
            | nil => simp
            | cons candidateHead candidateTail =>
                rcases hleft with ⟨leftRest, hleftRest⟩
                rcases hright with ⟨rightRest, hrightRest⟩
                simp only [List.cons_append, List.cons.injEq] at hleftRest hrightRest
                exact (heq (hleftRest.1.symm.trans hrightRest.1)).elim

/-- Reverse the exact longest common prefix of the reversed lists. -/
def longestCommonSuffix {α : Type*} [DecidableEq α]
    (left right : List α) : List α :=
  (longestCommonPrefix left.reverse right.reverse).reverse

theorem longestCommonSuffix_isSuffix_left
    {α : Type*} [DecidableEq α] (left right : List α) :
    longestCommonSuffix left right <:+ left := by
  apply (List.reverse_prefix
    (l₁ := longestCommonSuffix left right) (l₂ := left)).mp
  simpa [longestCommonSuffix] using
    longestCommonPrefix_isPrefix_left left.reverse right.reverse

theorem longestCommonSuffix_isSuffix_right
    {α : Type*} [DecidableEq α] (left right : List α) :
    longestCommonSuffix left right <:+ right := by
  apply (List.reverse_prefix
    (l₁ := longestCommonSuffix left right) (l₂ := right)).mp
  simpa [longestCommonSuffix] using
    longestCommonPrefix_isPrefix_right left.reverse right.reverse

/-- Maximality of the common suffix, stated in the only invariant needed by
the reverse-LCP partition: no common suffix has greater length. -/
theorem length_le_longestCommonSuffix_of_isSuffix
    {α : Type*} [DecidableEq α]
    (candidate left right : List α)
    (hleft : candidate <:+ left) (hright : candidate <:+ right) :
    candidate.length ≤ (longestCommonSuffix left right).length := by
  have hreverseLeft : candidate.reverse <+: left.reverse :=
    (List.reverse_prefix (l₁ := candidate) (l₂ := left)).2 hleft
  have hreverseRight : candidate.reverse <+: right.reverse :=
    (List.reverse_prefix (l₁ := candidate) (l₂ := right)).2 hright
  simpa [longestCommonSuffix] using
    length_le_longestCommonPrefix_of_isPrefix
      candidate.reverse left.reverse right.reverse
      hreverseLeft hreverseRight

end ReverseLCP

/-! ## Canonical compatible accepting walk -/

/-- Choose an accepting path for an accepted input.  Under unambiguity the
walk field is independent of this noncomputable choice. -/
def canonicalAcceptingPath {n : Nat} (B : FiniteUnambiguousFBDD n)
    (accepted : B.AcceptedModel) : B.AcceptingPath accepted.1 :=
  Classical.choice accepted.2

/-- The selected compatible accepting graph walk. -/
def canonicalAcceptingWalk {n : Nat} (B : FiniteUnambiguousFBDD n)
    (accepted : B.AcceptedModel) : B.Walk B.start B.accept :=
  (B.canonicalAcceptingPath accepted).walk

theorem canonicalAcceptingWalk_compatible {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel) :
    (B.canonicalAcceptingWalk accepted).Compatible accepted.1 :=
  (B.canonicalAcceptingPath accepted).compatible

/-- In an unambiguous graph, every compatible accepting walk is the selected
canonical walk. -/
theorem canonicalAcceptingWalk_eq_of_compatible {n : Nat}
    (B : FiniteUnambiguousFBDD n) (hUnambiguous : B.IsUnambiguous)
    (accepted : B.AcceptedModel) (walk : B.Walk B.start B.accept)
    (hcompatible : walk.Compatible accepted.1) :
    B.canonicalAcceptingWalk accepted = walk := by
  exact hUnambiguous accepted.1 (B.canonicalAcceptingWalk accepted) walk
    (B.canonicalAcceptingWalk_compatible accepted) hcompatible

/-! ## Total maximal reverse-LCP key on accepted-model pairs -/

/-- Complete input-labelled trace of the selected accepting walk. -/
def canonicalInputLabelledFullTrace {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel) :
    List (InputLabelledFullStep B) :=
  (B.canonicalAcceptingWalk accepted).inputLabelledFullTrace accepted.1

/-- Total reverse-LCP key of an ordered accepted-model pair.  It is the exact
longest common forward suffix of the two complete input-labelled traces. -/
def canonicalPairReverseLCPKey {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (pair : B.AcceptedModel × B.AcceptedModel) :
    List (InputLabelledFullStep B) :=
  ReverseLCP.longestCommonSuffix
    (B.canonicalInputLabelledFullTrace pair.1)
    (B.canonicalInputLabelledFullTrace pair.2)

theorem canonicalPairReverseLCPKey_isSuffix_left {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (pair : B.AcceptedModel × B.AcceptedModel) :
    B.canonicalPairReverseLCPKey pair <:+
      B.canonicalInputLabelledFullTrace pair.1 :=
  ReverseLCP.longestCommonSuffix_isSuffix_left _ _

theorem canonicalPairReverseLCPKey_isSuffix_right {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (pair : B.AcceptedModel × B.AcceptedModel) :
    B.canonicalPairReverseLCPKey pair <:+
      B.canonicalInputLabelledFullTrace pair.2 :=
  ReverseLCP.longestCommonSuffix_isSuffix_right _ _

/-- The pair key is maximal among all common labelled suffixes. -/
theorem canonicalPairReverseLCPKey_maximal {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (pair : B.AcceptedModel × B.AcceptedModel)
    (candidate : List (InputLabelledFullStep B))
    (hleft : candidate <:+ B.canonicalInputLabelledFullTrace pair.1)
    (hright : candidate <:+ B.canonicalInputLabelledFullTrace pair.2) :
    candidate.length ≤ (B.canonicalPairReverseLCPKey pair).length :=
  ReverseLCP.length_le_longestCommonSuffix_of_isSuffix
    candidate _ _ hleft hright

/-- Compatible pairs having one exact maximal reverse-LCP key. -/
noncomputable def compatiblePairReverseLCPBucket {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) :
    Finset (B.AcceptedModel × B.AcceptedModel) := by
  classical
  exact (B.compatibleAcceptedModelPairs base mask).filter fun pair =>
    B.canonicalPairReverseLCPKey pair = key

/-- The finite set of reverse-LCP keys which actually occur in one frozen
affine cylinder. -/
noncomputable def compatiblePairReverseLCPKeys {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) :
    Finset (List (InputLabelledFullStep B)) := by
  classical
  exact (B.compatibleAcceptedModelPairs base mask).image
    B.canonicalPairReverseLCPKey

@[simp]
theorem mem_compatiblePairReverseLCPBucket {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B))
    (pair : B.AcceptedModel × B.AcceptedModel) :
    pair ∈ B.compatiblePairReverseLCPBucket base mask key ↔
      pair ∈ B.compatibleAcceptedModelPairs base mask ∧
        B.canonicalPairReverseLCPKey pair = key := by
  simp [compatiblePairReverseLCPBucket]

@[simp]
theorem mem_compatiblePairReverseLCPKeys {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) :
    key ∈ B.compatiblePairReverseLCPKeys base mask ↔
      ∃ pair ∈ B.compatibleAcceptedModelPairs base mask,
        B.canonicalPairReverseLCPKey pair = key := by
  simp [compatiblePairReverseLCPKeys]

/-- Every compatible ordered pair belongs to the bucket of its total key. -/
theorem mem_compatiblePairReverseLCPBucket_own_key {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool)
    (pair : B.AcceptedModel × B.AcceptedModel)
    (hpair : pair ∈ B.compatibleAcceptedModelPairs base mask) :
    pair ∈ B.compatiblePairReverseLCPBucket base mask
      (B.canonicalPairReverseLCPKey pair) := by
  simp [hpair]

/-- Distinct reverse-LCP keys have disjoint pair buckets. -/
theorem compatiblePairReverseLCPBucket_disjoint_of_ne {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool)
    {leftKey rightKey : List (InputLabelledFullStep B)}
    (hne : leftKey ≠ rightKey) :
    Disjoint (B.compatiblePairReverseLCPBucket base mask leftKey)
      (B.compatiblePairReverseLCPBucket base mask rightKey) := by
  classical
  rw [Finset.disjoint_left]
  intro pair hleft hright
  have hleftKey :=
    (B.mem_compatiblePairReverseLCPBucket base mask leftKey pair).1 hleft |>.2
  have hrightKey :=
    (B.mem_compatiblePairReverseLCPBucket base mask rightKey pair).1 hright |>.2
  exact hne (hleftKey.symm.trans hrightKey)

/-- The key fibers cover the compatible ordered-pair set exactly. -/
theorem biUnion_compatiblePairReverseLCPBuckets {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) :
    (B.compatiblePairReverseLCPKeys base mask).biUnion
        (B.compatiblePairReverseLCPBucket base mask) =
      B.compatibleAcceptedModelPairs base mask := by
  classical
  ext pair
  constructor
  · intro hpair
    rcases Finset.mem_biUnion.mp hpair with ⟨key, _hkey, hbucket⟩
    exact (B.mem_compatiblePairReverseLCPBucket
      base mask key pair).1 hbucket |>.1
  · intro hpair
    apply Finset.mem_biUnion.mpr
    refine ⟨B.canonicalPairReverseLCPKey pair, ?_, ?_⟩
    · exact (B.mem_compatiblePairReverseLCPKeys base mask _).2
        ⟨pair, hpair, rfl⟩
    · exact B.mem_compatiblePairReverseLCPBucket_own_key
        base mask pair hpair

/-- Exact cardinal partition of the residual ordered-pair count by maximal
reverse-LCP key. -/
theorem sum_card_compatiblePairReverseLCPBuckets_eq_pairCount {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) :
    (∑ key ∈ B.compatiblePairReverseLCPKeys base mask,
        (B.compatiblePairReverseLCPBucket base mask key).card) =
      B.residualAcceptedModelPairCount base mask := by
  classical
  symm
  simpa [compatiblePairReverseLCPKeys, compatiblePairReverseLCPBucket,
    residualAcceptedModelPairCount] using
    (Finset.card_eq_sum_card_image B.canonicalPairReverseLCPKey
      (B.compatibleAcceptedModelPairs base mask))

/-- Fixed-first-coordinate fiber of one pair key.  These are the model
fibers to which the linear residual rectangle capacity applies. -/
noncomputable def frozenReferenceReverseLCPFiber {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : B.AcceptedModel)
    (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) : Finset B.AcceptedModel := by
  classical
  exact (B.compatibleAcceptedModels base mask).filter fun accepted =>
    B.canonicalPairReverseLCPKey (reference, accepted) = key

@[simp]
theorem mem_frozenReferenceReverseLCPFiber {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference accepted : B.AcceptedModel)
    (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) :
    accepted ∈ B.frozenReferenceReverseLCPFiber reference base mask key ↔
      accepted ∈ B.compatibleAcceptedModels base mask ∧
        B.canonicalPairReverseLCPKey (reference, accepted) = key := by
  simp [frozenReferenceReverseLCPFiber]

/-- Inside one pair-key bucket, the fiber of the first projection at
`reference` is exactly the fixed-reference model fiber. -/
theorem card_pairReverseLCPBucket_filter_fst_eq_referenceFiber {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : B.AcceptedModel)
    (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B))
    (hreference : reference ∈ B.compatibleAcceptedModels base mask) :
    ((B.compatiblePairReverseLCPBucket base mask key).filter
        fun pair => pair.1 = reference).card =
      (B.frozenReferenceReverseLCPFiber
        reference base mask key).card := by
  classical
  apply Finset.card_bij (fun pair _ => pair.2)
  · intro pair hpair
    have hfiltered := Finset.mem_filter.mp hpair
    have hbucket := (B.mem_compatiblePairReverseLCPBucket
      base mask key pair).1 hfiltered.1
    have hpairFrozen :
        pair.1 ∈ B.compatibleAcceptedModels base mask ∧
          pair.2 ∈ B.compatibleAcceptedModels base mask := by
      simpa [compatibleAcceptedModelPairs] using hbucket.1
    apply (B.mem_frozenReferenceReverseLCPFiber
      reference pair.2 base mask key).2
    constructor
    · exact hpairFrozen.2
    · have hpairEq : (reference, pair.2) = pair := by
        apply Prod.ext
        · exact hfiltered.2.symm
        · rfl
      simpa [hpairEq] using hbucket.2
  · intro left hleft right hright heq
    have hleftFirst := (Finset.mem_filter.mp hleft).2
    have hrightFirst := (Finset.mem_filter.mp hright).2
    apply Prod.ext
    · exact hleftFirst.trans hrightFirst.symm
    · exact heq
  · intro accepted haccepted
    have hfiber := (B.mem_frozenReferenceReverseLCPFiber
      reference accepted base mask key).1 haccepted
    refine ⟨(reference, accepted), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (B.mem_compatiblePairReverseLCPBucket
        base mask key (reference, accepted)).2
      constructor
      · simp [compatibleAcceptedModelPairs, hreference, hfiber.1]
      · exact hfiber.2
    · rfl

/-- Exact first-coordinate decomposition of every total pair-key bucket.
This is the extra fiber decomposition required before applying a linear
rectangle capacity to an ordered-pair bucket. -/
theorem sum_card_referenceFibers_eq_pairReverseLCPBucket_card {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) :
    (∑ reference ∈ B.compatibleAcceptedModels base mask,
        (B.frozenReferenceReverseLCPFiber
          reference base mask key).card) =
      (B.compatiblePairReverseLCPBucket base mask key).card := by
  classical
  have hmaps : Set.MapsTo Prod.fst
      (B.compatiblePairReverseLCPBucket base mask key :
        Set (B.AcceptedModel × B.AcceptedModel))
      (B.compatibleAcceptedModels base mask : Set B.AcceptedModel) := by
    intro pair hpair
    have hbucket := (B.mem_compatiblePairReverseLCPBucket
      base mask key pair).1 hpair
    have hpairFrozen :
        pair.1 ∈ B.compatibleAcceptedModels base mask ∧
          pair.2 ∈ B.compatibleAcceptedModels base mask := by
      simpa [compatibleAcceptedModelPairs] using hbucket.1
    exact hpairFrozen.1
  calc
    (∑ reference ∈ B.compatibleAcceptedModels base mask,
        (B.frozenReferenceReverseLCPFiber
          reference base mask key).card) =
      ∑ reference ∈ B.compatibleAcceptedModels base mask,
        ((B.compatiblePairReverseLCPBucket base mask key).filter
          fun pair => pair.1 = reference).card := by
            apply Finset.sum_congr rfl
            intro reference hreference
            exact (B.card_pairReverseLCPBucket_filter_fst_eq_referenceFiber
              reference base mask key hreference).symm
    _ = (B.compatiblePairReverseLCPBucket base mask key).card :=
      (Finset.card_eq_sum_card_fiberwise hmaps).symm

/-- The canonical accepting walk of `accepted` has the displayed graph
suffix. -/
def HasCanonicalAcceptingSuffix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept) : Prop :=
  ∃ prefixWalk : B.Walk B.start vertex,
    B.canonicalAcceptingWalk accepted = prefixWalk.append suffixWalk

/-- A canonical suffix decomposition supplies the compatible prefix needed
by the residual rectangle. -/
theorem hasCompatiblePrefix_of_hasCanonicalAcceptingSuffix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hsuffix : B.HasCanonicalAcceptingSuffix accepted suffixWalk) :
    B.HasCompatiblePrefix accepted.1 vertex := by
  rcases hsuffix with ⟨prefixWalk, hsplit⟩
  refine ⟨prefixWalk, ?_⟩
  have hcompatible := B.canonicalAcceptingWalk_compatible accepted
  rw [hsplit, Walk.compatible_append] at hcompatible
  exact hcompatible.1

/-- The same decomposition also makes the fixed suffix compatible. -/
theorem compatible_of_hasCanonicalAcceptingSuffix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hsuffix : B.HasCanonicalAcceptingSuffix accepted suffixWalk) :
    suffixWalk.Compatible accepted.1 := by
  rcases hsuffix with ⟨prefixWalk, hsplit⟩
  have hcompatible := B.canonicalAcceptingWalk_compatible accepted
  rw [hsplit, Walk.compatible_append] at hcompatible
  exact hcompatible.2

/-! ## Dependent-walk realization of one list-key fiber -/

/-- Exact realization of one finite-list reverse-LCP fiber by a common typed
graph suffix.  The theorem immediately below discharges this interface for
every nonempty fiber.

The reference canonical walk is split at `vertex`; every model in the fixed-
reference key fiber has the same typed suffix; and both reference and member
traces realize the finite-list key exactly. -/
def ReverseLCPFiberWalkLift {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : B.AcceptedModel)
    (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) : Prop :=
  ∃ vertex : B.Vertex,
    ∃ referencePrefix : B.Walk B.start vertex,
    ∃ suffixWalk : B.Walk vertex B.accept,
      B.canonicalAcceptingWalk reference =
          referencePrefix.append suffixWalk ∧
        suffixWalk.inputLabelledFullTrace reference.1 = key ∧
        ∀ accepted ∈
            B.frozenReferenceReverseLCPFiber reference base mask key,
          B.HasCanonicalAcceptingSuffix accepted suffixWalk ∧
            suffixWalk.inputLabelledFullTrace accepted.1 = key

/-- Every nonempty fixed-reference maximal-key fiber has the required common
typed suffix.  The proof lifts the finite-list suffix independently on the
reference and on each member, then uses full-step injectivity to identify the
dependent cut vertex and the entire suffix walk. -/
theorem reverseLCPFiberWalkLift_of_nonempty {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : B.AcceptedModel)
    (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B))
    (hfiber :
      (B.frozenReferenceReverseLCPFiber reference base mask key).Nonempty) :
    B.ReverseLCPFiberWalkLift reference base mask key := by
  rcases hfiber with ⟨anchor, hanchor⟩
  have hanchorKey :
      B.canonicalPairReverseLCPKey (reference, anchor) = key :=
    (B.mem_frozenReferenceReverseLCPFiber
      reference anchor base mask key).1 hanchor |>.2
  have hkeyReference :
      key <:+ B.canonicalInputLabelledFullTrace reference := by
    rw [← hanchorKey]
    exact B.canonicalPairReverseLCPKey_isSuffix_left (reference, anchor)
  rcases Walk.exists_split_of_isSuffix_inputLabelledFullTrace
      (B.canonicalAcceptingWalk reference) reference.1 key
      (by simpa [canonicalInputLabelledFullTrace] using hkeyReference) with
    ⟨vertex, referencePrefix, suffixWalk,
      hreferenceSplit, hreferenceTrace⟩
  refine ⟨vertex, referencePrefix, suffixWalk,
    hreferenceSplit, hreferenceTrace, ?_⟩
  intro accepted haccepted
  have hacceptedKey :
      B.canonicalPairReverseLCPKey (reference, accepted) = key :=
    (B.mem_frozenReferenceReverseLCPFiber
      reference accepted base mask key).1 haccepted |>.2
  have hkeyAccepted :
      key <:+ B.canonicalInputLabelledFullTrace accepted := by
    rw [← hacceptedKey]
    exact B.canonicalPairReverseLCPKey_isSuffix_right (reference, accepted)
  rcases Walk.exists_split_of_isSuffix_inputLabelledFullTrace
      (B.canonicalAcceptingWalk accepted) accepted.1 key
      (by simpa [canonicalInputLabelledFullTrace] using hkeyAccepted) with
    ⟨acceptedVertex, acceptedPrefix, acceptedSuffix,
      hacceptedSplit, hacceptedTrace⟩
  have hsuffixSigma :
      (⟨acceptedVertex, acceptedSuffix⟩ : Walk.AnyWalkTo B B.accept) =
        ⟨vertex, suffixWalk⟩ :=
    Walk.anyWalkTo_eq_of_inputLabelledFullTrace_eq
      B.accept accepted.1 reference.1
      ⟨acceptedVertex, acceptedSuffix⟩ ⟨vertex, suffixWalk⟩
      (hacceptedTrace.trans hreferenceTrace.symm)
  cases hsuffixSigma
  exact ⟨⟨acceptedPrefix, hacceptedSplit⟩, hacceptedTrace⟩

/-- The empty maximal suffix always has a typed realization: cut at the
accepting sink.  Thus the only unresolved lift case is a nonempty list key. -/
theorem reverseLCPFiberWalkLift_nil {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : B.AcceptedModel)
    (base mask : Fin n -> Bool) :
    B.ReverseLCPFiberWalkLift reference base mask [] := by
  refine ⟨B.accept, B.canonicalAcceptingWalk reference,
    .nil B.accept, ?_, ?_, ?_⟩
  · simp
  · simp [Walk.inputLabelledFullTrace]
  · intro accepted _haccepted
    constructor
    · exact ⟨B.canonicalAcceptingWalk accepted, by simp⟩
    · simp [Walk.inputLabelledFullTrace]

/-! ## Exact frozen labelled-suffix bucket -/

/-- Accepted inputs in one affine cylinder whose canonical accepting walk has
the supplied graph suffix and whose *full input-labelled* suffix trace equals
that of the reference input. -/
noncomputable def frozenCanonicalLabelledSuffixBucket {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool) : Finset B.AcceptedModel := by
  classical
  exact (B.compatibleAcceptedModels base mask).filter fun accepted =>
    B.HasCanonicalAcceptingSuffix accepted suffixWalk ∧
      suffixWalk.inputLabelledFullTrace accepted.1 =
        suffixWalk.inputLabelledFullTrace reference.1

@[simp]
theorem mem_frozenCanonicalLabelledSuffixBucket {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference accepted : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool) :
    accepted ∈ B.frozenCanonicalLabelledSuffixBucket
        reference suffixWalk base mask ↔
      accepted ∈ B.compatibleAcceptedModels base mask ∧
        B.HasCanonicalAcceptingSuffix accepted suffixWalk ∧
        suffixWalk.inputLabelledFullTrace accepted.1 =
          suffixWalk.inputLabelledFullTrace reference.1 := by
  simp [frozenCanonicalLabelledSuffixBucket]

/-- Generic combined reverse-LCP lemma.  A complete read-once split upgrades
full labelled suffix equality to agreement on every global `postVars`
coordinate, after which the sharp frozen residual rectangle applies.

This version accepts an arbitrary finite fiber and is the direct insertion
surface for any future maximal-suffix partition implementation. -/
theorem card_frozenFullLabelledCompleteSuffixFiber_mul_residual_le
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) {vertex : B.Vertex}
    (prefixWalk : B.Walk B.start vertex)
    (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hcomplete : (prefixWalk.append suffixWalk).queryVars = Finset.univ)
    (hreference : reference ∈ B.compatibleAcceptedModels base mask)
    (fiber : Finset B.AcceptedModel)
    (hfrozen : ∀ accepted ∈ fiber,
      accepted ∈ B.compatibleAcceptedModels base mask)
    (hprefix : ∀ accepted ∈ fiber,
      B.HasCompatiblePrefix accepted.1 vertex)
    (htrace : ∀ accepted ∈ fiber,
      suffixWalk.inputLabelledFullTrace accepted.1 =
        suffixWalk.inputLabelledFullTrace reference.1) :
    fiber.card *
        Fintype.card (B.FrozenResidualSuffixModel vertex base mask) ≤
      B.residualAcceptedModelCount base mask := by
  apply B.card_frozenFiber_mul_card_frozenResidualSuffix_le_residualAcceptedModelCount
    reference vertex base mask hreadOnce hreference fiber hfrozen hprefix
  intro accepted haccepted queryIndex hpost
  have hqueryTrace :=
    suffixWalk.inputLabelledQueryTrace_eq_of_inputLabelledFullTrace_eq
      accepted.1 reference.1 (htrace accepted haccepted)
  exact FiniteUnambiguousFBDD.Walk.eq_on_postVars_of_inputLabelledQueryTrace_eq
    B prefixWalk suffixWalk hreadOnce hcomplete accepted.1 reference.1
      hqueryTrace queryIndex hpost

/-- Sharp residual capacity of the literal canonical fixed-suffix bucket.
The displayed suffix is required to lie on the reference canonical walk, and
all formal accepting walks must be complete. -/
theorem card_frozenCanonicalLabelledSuffixBucket_mul_residual_le
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ)
    (hreference : reference ∈ B.compatibleAcceptedModels base mask)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk) :
    (B.frozenCanonicalLabelledSuffixBucket
        reference suffixWalk base mask).card *
        Fintype.card (B.FrozenResidualSuffixModel vertex base mask) ≤
      B.residualAcceptedModelCount base mask := by
  rcases hreferenceSuffix with ⟨prefixWalk, _hreferenceSplit⟩
  apply B.card_frozenFullLabelledCompleteSuffixFiber_mul_residual_le
    reference prefixWalk suffixWalk base mask hreadOnce
      (hreadsAll (prefixWalk.append suffixWalk)) hreference
  · intro accepted haccepted
    exact (B.mem_frozenCanonicalLabelledSuffixBucket
      reference accepted suffixWalk base mask).1 haccepted |>.1
  · intro accepted haccepted
    have hsuffix := (B.mem_frozenCanonicalLabelledSuffixBucket
      reference accepted suffixWalk base mask).1 haccepted |>.2.1
    exact B.hasCompatiblePrefix_of_hasCanonicalAcceptingSuffix
      accepted suffixWalk hsuffix
  · intro accepted haccepted
    exact (B.mem_frozenCanonicalLabelledSuffixBucket
      reference accepted suffixWalk base mask).1 haccepted |>.2.2

/-- Capacity of every fixed-reference maximal-key fiber once the single
typed-walk lift obligation is discharged.  The conclusion returns the cut
vertex and common suffix because the residual suffix model depends on that
vertex.

For pair counting, apply this theorem separately to the fixed-first-coordinate
fibers inside each total pair-key bucket.  A linear rectangle bound cannot
hold for the whole pair bucket without this extra fiber decomposition: a
bucket on `k` models may contain `k^2` ordered pairs. -/
theorem exists_card_frozenReferenceReverseLCPFiber_mul_residual_le_of_walkLift
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ)
    (hreference : reference ∈ B.compatibleAcceptedModels base mask)
    (hlift : B.ReverseLCPFiberWalkLift reference base mask key) :
    ∃ vertex : B.Vertex,
      ∃ _suffixWalk : B.Walk vertex B.accept,
        (B.frozenReferenceReverseLCPFiber
            reference base mask key).card *
            Fintype.card
              (B.FrozenResidualSuffixModel vertex base mask) ≤
          B.residualAcceptedModelCount base mask := by
  rcases hlift with
    ⟨vertex, referencePrefix, suffixWalk, _hreferenceSplit,
      hreferenceTrace, hmembers⟩
  refine ⟨vertex, suffixWalk, ?_⟩
  apply B.card_frozenFullLabelledCompleteSuffixFiber_mul_residual_le
    reference referencePrefix suffixWalk base mask hreadOnce
      (hreadsAll (referencePrefix.append suffixWalk)) hreference
  · intro accepted haccepted
    exact (B.mem_frozenReferenceReverseLCPFiber
      reference accepted base mask key).1 haccepted |>.1
  · intro accepted haccepted
    exact B.hasCompatiblePrefix_of_hasCanonicalAcceptingSuffix
      accepted suffixWalk (hmembers accepted haccepted).1
  · intro accepted haccepted
    exact (hmembers accepted haccepted).2.trans hreferenceTrace.symm

/-- Unconditional capacity for every fixed-reference maximal reverse-LCP key.
A nonempty fiber has a canonical common typed suffix by
`reverseLCPFiberWalkLift_of_nonempty`; an empty fiber satisfies the inequality
trivially.  Thus no list-to-walk lift obligation remains. -/
theorem exists_card_frozenReferenceReverseLCPFiber_mul_residual_le
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ)
    (hreference : reference ∈ B.compatibleAcceptedModels base mask) :
    ∃ vertex : B.Vertex,
      ∃ _suffixWalk : B.Walk vertex B.accept,
        (B.frozenReferenceReverseLCPFiber
            reference base mask key).card *
            Fintype.card
              (B.FrozenResidualSuffixModel vertex base mask) ≤
          B.residualAcceptedModelCount base mask := by
  classical
  by_cases hfiber :
      (B.frozenReferenceReverseLCPFiber
        reference base mask key).Nonempty
  · exact B.exists_card_frozenReferenceReverseLCPFiber_mul_residual_le_of_walkLift
      reference base mask key hreadOnce hreadsAll hreference
        (B.reverseLCPFiberWalkLift_of_nonempty
          reference base mask key hfiber)
  · have hempty :
        B.frozenReferenceReverseLCPFiber reference base mask key = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    refine ⟨B.accept, .nil B.accept, ?_⟩
    simp [hempty]

/-- Every realized total pair key has a compatible reference endpoint whose
fixed-reference fiber satisfies the sharp residual capacity.  The stronger
preceding theorem in fact gives the capacity for every compatible reference,
not merely this witness. -/
theorem exists_reference_and_maximalReverseLCPFiber_capacity_of_key_mem
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B))
    (hkey : key ∈ B.compatiblePairReverseLCPKeys base mask)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ) :
    ∃ reference : B.AcceptedModel,
      reference ∈ B.compatibleAcceptedModels base mask ∧
        ∃ vertex : B.Vertex,
          ∃ _suffixWalk : B.Walk vertex B.accept,
            (B.frozenReferenceReverseLCPFiber
                reference base mask key).card *
                Fintype.card
                  (B.FrozenResidualSuffixModel vertex base mask) ≤
              B.residualAcceptedModelCount base mask := by
  rcases (B.mem_compatiblePairReverseLCPKeys base mask key).1 hkey with
    ⟨pair, hpair, _hpairKey⟩
  have hpairFrozen :
      pair.1 ∈ B.compatibleAcceptedModels base mask ∧
        pair.2 ∈ B.compatibleAcceptedModels base mask := by
    simpa [compatibleAcceptedModelPairs] using hpair
  refine ⟨pair.1, hpairFrozen.1, ?_⟩
  exact B.exists_card_frozenReferenceReverseLCPFiber_mul_residual_le
    pair.1 base mask key hreadOnce hreadsAll hpairFrozen.1

/-- The empty-key fiber has unconditional capacity, since its typed lift is
the nil suffix at the accepting sink. -/
theorem exists_card_frozenReferenceReverseLCPFiber_nil_mul_residual_le
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ)
    (hreference : reference ∈ B.compatibleAcceptedModels base mask) :
    ∃ vertex : B.Vertex,
      ∃ _suffixWalk : B.Walk vertex B.accept,
        (B.frozenReferenceReverseLCPFiber
            reference base mask []).card *
            Fintype.card
              (B.FrozenResidualSuffixModel vertex base mask) ≤
          B.residualAcceptedModelCount base mask := by
  exact B.exists_card_frozenReferenceReverseLCPFiber_mul_residual_le_of_walkLift
    reference base mask [] hreadOnce hreadsAll hreference
      (B.reverseLCPFiberWalkLift_nil reference base mask)

end FiniteUnambiguousFBDD

/-! ## Mandatory-selector specialization -/

/-- The exact fixed-suffix bucket capacity for every affine-prefixed
mandatory canonical selector on `2^n` input coordinates.  Both read-once and
full-walk completeness are discharged by the mandatory-selector geometry. -/
theorem prefixedMandatoryCanonicalSelector_card_frozenCanonicalLabelledSuffixBucket_mul_residual_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound (2 ^ n)))
    (reference :
      ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
        |>.affinePaddedRestrictByRounds rounds).AcceptedModel)
    {vertex : ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds rounds).Vertex}
    (suffixWalk : ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds rounds).Walk vertex
        ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
          |>.affinePaddedRestrictByRounds rounds).accept)
    (base mask : Fin (2 ^ n) -> Bool)
    (hreference : reference ∈
      ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
        |>.affinePaddedRestrictByRounds rounds).compatibleAcceptedModels
          base mask)
    (hreferenceSuffix :
      ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
        |>.affinePaddedRestrictByRounds rounds).HasCanonicalAcceptingSuffix
          reference suffixWalk) :
    (((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
        |>.affinePaddedRestrictByRounds rounds)
          |>.frozenCanonicalLabelledSuffixBucket
            reference suffixWalk base mask).card *
        Fintype.card
          (((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
            |>.affinePaddedRestrictByRounds rounds).FrozenResidualSuffixModel
              vertex base mask) ≤
      ((mandatoryCanonicalUFBDD machine (2 ^ n) T b)
        |>.affinePaddedRestrictByRounds rounds).residualAcceptedModelCount
          base mask := by
  let B := (mandatoryCanonicalUFBDD machine (2 ^ n) T b)
    |>.affinePaddedRestrictByRounds rounds
  apply FiniteUnambiguousFBDD.card_frozenCanonicalLabelledSuffixBucket_mul_residual_le
    B reference suffixWalk base mask
  · exact (mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds_isSyntacticallyReadOnce rounds
        (mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
          machine (2 ^ n) T b)
  · exact mandatoryCanonicalUFBDD_affinePaddedRestrictByRounds_walk_queryVars_eq_univ
      machine (2 ^ n) T b rounds
  · exact hreference
  · exact hreferenceSuffix

/-- Unconditional maximal reverse-LCP fiber capacity for every affine-
prefixed mandatory selector.  The total ordered-pair key and its disjoint
partition are generic; this specialization discharges read-once and complete-
walk geometry for each fixed-reference fiber. -/
theorem prefixedMandatoryCanonicalSelector_exists_maximalReverseLCPFiber_capacity
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let B := (mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds rounds
    ∀ (reference : B.AcceptedModel)
      (base mask : Fin (2 ^ n) -> Bool)
      (key : List (FiniteUnambiguousFBDD.InputLabelledFullStep B)),
      reference ∈ B.compatibleAcceptedModels base mask ->
        ∃ vertex : B.Vertex,
          ∃ _suffixWalk : B.Walk vertex B.accept,
            (B.frozenReferenceReverseLCPFiber
                reference base mask key).card *
                Fintype.card
                  (B.FrozenResidualSuffixModel vertex base mask) ≤
              B.residualAcceptedModelCount base mask := by
  dsimp only
  intro reference base mask key hreference
  let B := (mandatoryCanonicalUFBDD machine (2 ^ n) T b)
    |>.affinePaddedRestrictByRounds rounds
  apply FiniteUnambiguousFBDD.exists_card_frozenReferenceReverseLCPFiber_mul_residual_le
    B reference base mask key
  · exact (mandatoryCanonicalUFBDD machine (2 ^ n) T b)
      |>.affinePaddedRestrictByRounds_isSyntacticallyReadOnce rounds
        (mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
          machine (2 ^ n) T b)
  · exact mandatoryCanonicalUFBDD_affinePaddedRestrictByRounds_walk_queryVars_eq_univ
      machine (2 ^ n) T b rounds
  · exact hreference

end

end OneTapeMagnification
end Frontier
end Pnp4
